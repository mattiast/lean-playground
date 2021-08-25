import data.real.basic

-- based on video https://www.youtube.com/watch?v=ac9GNeVaWgE

section

variables {f g : ℝ → ℝ}
variable feq : ∀ x y, g (f (x + y)) = f x + (2*x+y) * (g y)

include feq

lemma l2 (x : ℝ) : g (f (-x)) = f x :=
begin
  let h := feq x (-2*x),
  simp at h,
  rw (by linarith : x + (-(2*x)) = -x) at h,
  exact h,
end

lemma l5 (x y : ℝ ) : f (-x-y) = f x + (2*x+y) * g y :=
begin
  rw ← l2 feq ,
  rw (by linarith : -(-x-y) = x+y),
  apply feq,
end


lemma l3 (x y : ℝ) : f x + (2*x+y) * g y = f y + (2*y+x) * g x :=
begin
  let h1 := feq x y,
  let h2 := feq y x,
  rw (by linarith : y + x = x + y) at h2,
  linarith,
end

def gform (a b : ℝ) : Prop := ∀ (x : ℝ) , g x = a * x + b

lemma l4 : ∃ (a b : ℝ), gform feq a b :=
begin
  use g 1 - g 0,
  use g 0,
  intro x,

  let h1 := l3 feq 0 x,
  let h2 := l3 feq 1 0,
  let h3 := l3 feq x 1,

  linarith,
end

lemma l6 (a b : ℝ) (gf : gform feq a b) : ∀ x y : ℝ, f (-x-y) = f x + (2*x+y)*(a*y+b) :=
begin
  intros x y,
  rw ← gf,
  apply l5 feq,
end

lemma l7 (a b : ℝ ) (gf : gform feq a b) : ∀ x : ℝ , f x = a * x^2 - b*x + f 0 :=
begin
  intro x,
  let h1 := l6 feq a b gf 0 (-x),
  simp at h1,
  linarith,
end

theorem solutions : (∀ x : ℝ , f x = 0 ∧ g x = 0) ∨ (∃ c, ∀ x, f x = x^2 + c ∧ g x = x) :=
begin
  rcases l4 feq with ⟨ a, b, gf ⟩,
  have heq : ∀ x, a * (a * x ^ 2 + b * x + f 0) + b = a * x ^ 2 - b * x + f 0 , 
  {
    intro x,
    have h1 := l2 feq x,
    rw gf at h1,
    rw l7 feq a b gf (-x) at h1,
    rw l7 feq a b gf x at h1,
    simp at h1,
    assumption,
  },
  let e0 := heq 0,
  let e1 := heq 1,
  let e2 := heq 2,

  have ha : a = a*a, linarith,
  have hb : a*b = -b, linarith,
  clear e0 e1 e2 heq,

  by_cases a = 0,
  {
    left,
    rw h at hb,
    simp at hb,
    have : ∀ x, g x = 0,
    {
      intro x,
      rw [gf, h ,hb],
      simp,
    },
    intro x,
    split,
    {
      rw ← l2 feq,
      rw this,
    },
    exact this x,
  },
  right,
  have ta : a = 1,
  {
    -- Q: There must be an easier way to do this??
    have : a*(a-1) = 0,
    {
      calc a*(a-1) = a*a-a : by ring
      ... = a-a : by rw ← ha
      ... = 0 : by ring,
    },
    rw mul_eq_zero at this,
    cases this ,
    {
      exfalso,
      exact h this,
    },
    linarith,
  },
  clear h ha,
  rw ta at hb,
  have tb : b = 0, linarith,
  rw [ta,tb] at gf,

  use f 0,
  intro x,
  split,
  {
    have hh := l7 feq 1 0 gf x,
    simp at hh,
    assumption,
  },
  dsimp [gform] at gf,
  specialize gf x,
  simp at gf,
  assumption,
end

end

#check @solutions
