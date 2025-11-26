import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Playground.func

-- based on video https://www.youtube.com/watch?v=ac9GNeVaWgE

variable {f g : ℝ → ℝ}

abbrev FuncEq (f g : ℝ → ℝ) : Prop := ∀ x y, g (f (x + y)) = f x + (2*x+y) * (g y)

lemma l2 (feq : FuncEq f g) (x : ℝ) : g (f (-x)) = f x := by
  let h := feq x (-2*x)
  simp at h
  rw [(by linarith : x + (-(2*x)) = -x)] at h
  exact h

lemma l5 (feq : FuncEq f g) (x y : ℝ ) : f (-x-y) = f x + (2*x+y) * g y := by
  rw [← l2 feq]
  rw [(by linarith : -(-x-y) = x+y)]
  apply feq

lemma l3 (feq : FuncEq f g) (x y : ℝ) : f x + (2*x+y) * g y = f y + (2*y+x) * g x := by
  let h1 := feq x y
  let h2 := feq y x
  rw [(by linarith : y + x = x + y)] at h2
  linarith

def gform (g : ℝ → ℝ) (a b : ℝ) : Prop := ∀ (x : ℝ) , g x = a * x + b

lemma l4 (feq : FuncEq f g) : ∃ (a b : ℝ), gform g a b := by
  use g 1 - g 0
  use g 0
  intro x
  let h1 := l3 feq 0 x
  let h2 := l3 feq 1 0
  let h3 := l3 feq x 1
  linarith

lemma l6 (feq : FuncEq f g) (a b : ℝ) (gf : gform g a b) : ∀ x y : ℝ, f (-x-y) = f x + (2*x+y)*(a*y+b) := by
  intros x y
  rw [← gf]
  apply l5 feq

lemma l7 (feq : FuncEq f g) (a b : ℝ ) (gf : gform g a b) : ∀ x : ℝ , f x = a * x^2 - b*x + f 0 := by
  intro x
  let h1 := l6 feq a b gf 0 (-x)
  simp at h1
  linarith

theorem solutions (feq : FuncEq f g) : (∀ x : ℝ , f x = 0 ∧ g x = 0) ∨ (∃ c, ∀ x, f x = x^2 + c ∧ g x = x) := by
  rcases l4 feq with ⟨ a, b, gf ⟩
  have heq : ∀ x, a * (a * x ^ 2 + b * x + f 0) + b = a * x ^ 2 - b * x + f 0 := by
    intro x
    have h1 := l2 feq x
    rw [gf] at h1
    rw [l7 feq a b gf (-x)] at h1
    rw [l7 feq a b gf x] at h1
    simp at h1
    assumption
  let e0 := heq 0
  let e1 := heq 1
  let e2 := heq 2
  have ha : a = a*a := by linarith
  have hb : a*b = -b := by linarith
  clear e0 e1 e2 heq
  by_cases h : a = 0
  · left
    rw [h] at hb
    simp at hb
    have : ∀ x, g x = 0 := by
      intro x
      rw [gf, h, hb]
      simp
    intro x
    constructor
    · rw [← l2 feq]
      rw [this]
    · exact this x
  · right
    have ta : a = 1 := by
      -- Q: There must be an easier way to do this??
      have : a*(a-1) = 0 := by
        calc a*(a-1) = a*a-a := by ring
          _ = a-a := by rw [← ha]
          _ = 0 := by ring
      rw [mul_eq_zero] at this
      cases' this with h1 h2
      · exfalso
        exact h h1
      · linarith
    clear h ha
    rw [ta] at hb
    have tb : b = 0 := by linarith
    rw [ta, tb] at gf
    use f 0
    intro x
    constructor
    · have hh := l7 feq 1 0 gf x
      simp at hh
      assumption
    · dsimp [gform] at gf
      specialize gf x
      simp at gf
      assumption

end Playground.func
