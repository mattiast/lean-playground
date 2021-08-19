import data.real.basic

structure solution (k : ℤ) :=
  (req0 : k ≥ 1)
  (a : ℤ)
  (b : ℤ)
  (req1 : a^2 + b^2 = k*(a*b+1))
  (req2 : a ≥ 0 ∧ b ≥ 0)

structure solution_pos (k : ℤ) :=
  (s : solution k)
  (pos : s.a > 0 ∧ s.b > 0)

def nosq (k : ℤ) : Prop := ¬ ∃ l : ℤ , k = l*l

-- Goal is to prove that if k isn't a square then ∄ positive solution
-- Follows idea from https://www.youtube.com/watch?v=WCI5OaBKME4

def l1 (k  : ℤ) (s : solution k) (H2 : s.b ≥ 1) (H1 : s.a ≥ s.b) : solution k :=
begin
  let a1 := k*s.b-s.a, -- integer, must be positive
  let b := s.b,
  let a := s.a,
  have h : a1^2 + b^2 = k*(a1*b+1),
  {
    dsimp [a1],
    calc (k*b-a)^2 + b^2 = k^2*b^2 - 2*k*b*a + (a^2+b^2) : by ring
    ... = k^2*b^2 - 2*k*b*a + k*(a*b+1) : by rw s.req1
    ... = k*((k*b-a)*b+1) : by ring
  },
  have h2 : a1 ≥ 0,
  {
    by_contra hh,
    have h3 : a1 < 0,
    {
      simp,
      simp at hh,
      assumption,
    },
    have h4 : a1*b+1 ≤ 0,
    {
      rw ←  int.lt_iff_add_one_le,
      apply mul_neg_iff.mpr,
      apply or.inr,
      dsimp [b],
      split,
      assumption,
      linarith [H2, h3],
    },
    have h5 : k*(a1*b+1) ≤ 0,
    {
      rw (by ring : 0 = k * 0),
      apply int.mul_le_mul_of_nonneg_left h4,
      linarith only [s.req0],
    },
    have h6 : a1^2 + b^2 > 0,
    {
      have : 1*1 ≤ b*b,
      {
        exact int.mul_self_le_mul_self (by linarith : 0 ≤ (1 : int)) (H2),
      },
      have : a1*a1 ≥ 0,
      {
        exact mul_self_nonneg a1,
      },
      linarith,
    },
    linarith,
  },
  have s : solution k,
  {
    exact solution.mk (s.req0) a1 b h ⟨h2, by linarith⟩,
  },
  exact s,
end

lemma l2 (k : ℤ ) (s : solution k) (H2 : s.b ≥ 1) (H1 : s.a ≥ s.b)
  : (l1 k s H2 H1).a * s.a = (s.b^2 - k) :=
begin
  dsimp [l1],
  have : s.b^2 = -s.a^2 + k*(s.a*s.b+1),
  {
    linarith only [s.req1]
  },
  rw this,
  ring_nf,
end

lemma l3 (k : ℤ ) (s : solution k) (H2 : s.b ≥ 1) (H1 : s.a ≥ s.b)
  : (l1 k s H2 H1).a < s.a :=
begin
  rw ← mul_lt_mul_right (by linarith : s.a > 0),
  rw l2,
  calc s.b^2 - k < s.b^2 : by linarith [s.req0]
  ... = s.b * s.b : by ring_nf
  ... ≤ s.a * s.a : mul_self_le_mul_self (by linarith) H1
end

def height {k : ℤ}: solution k → ℤ :=
  λ s, (s.a + s.b)

lemma l4 (k : ℤ) (s : solution k) (H2 : s.b ≥ 1) (H1 : s.a ≥ s.b)
  : height (l1 k s H2 H1) < height s :=
begin
  dsimp [height],
  calc (l1 k s H2 H1).a + (l1 k s H2 H1).b = (l1 k s H2 H1).a + s.b : rfl
  ... < s.a + s.b : by linarith [l3 k s H2 H1]
end

lemma l5 (k : ℤ) (s : solution k) (H2 : s.b ≥ 1) (H1 : s.a ≥ s.b) (H3 : nosq k)
  : (l1 k s H2 H1).a > 0 :=
begin
  cases lt_or_eq_of_le (l1 k s H2 H1).req2.left,
  assumption,
  exfalso,
  -- l2 : (l1 k s H2 H1).a * s.a = (s.b^2 - k) :=
  have : 0 = s.b^2 - k,
  {
    calc 0 = 0 * s.a : by ring
    ... = (l1 k s H2 H1).a * s.a : by rw [h]
    ... = s.b^2 - k : l2 k s H2 H1
  },
  apply H3,
  use s.b,
  calc k = k + 0 : by ring
  ... = k + (s.b^2-k) : by rw [this]
  ... = s.b * s.b : by ring,
end

structure solution_normal (k : ℤ) :=
  (s : solution k)
  (H2 : s.b ≥ 1)
  (H1 : s.a ≥ s.b)

def normal (k : ℤ) (sp : solution_pos k) : solution_normal k :=
begin
  by_cases sp.s.a ≥ sp.s.b,
  {
    apply solution_normal.mk sp.s,
    have : sp.s.b > 0, exact sp.pos.right,
    linarith,
    assumption,
  },
  {
    simp at h,
    have sn : solution_normal k :=
    {
      s := begin apply solution.mk sp.s.req0 sp.s.b sp.s.a,
      {
        let hh := sp.s.req1,
        calc sp.s.b ^ 2 + sp.s.a ^ 2 = sp.s.a ^ 2 + sp.s.b ^ 2 : by ring
        ... = k * (sp.s.a * sp.s.b + 1) : hh
        ... = k * (sp.s.b * sp.s.a + 1) : by ring,
      },
      split ; linarith [sp.s.req2],
      end,
      H2 := begin
        simp,
        linarith [sp.pos],
      end,
      H1 := begin
        simp,
        linarith,
      end,
    },
    exact sn,
  },
end

lemma l6 (k : ℤ) (sp : solution_pos k) : height sp.s = height (normal k sp).s :=
begin
  by_cases sp.s.a ≥ sp.s.b ; dsimp [normal],
    simp [h],
  simp [h],
  dsimp [height],
  ring,
end

def step (k : ℤ) (hk : nosq k) (sn : solution_normal k) : solution_normal k :=
  normal k {
    s := l1 k sn.s sn.H2 sn.H1,
    pos := begin
      split,
      apply l5,
      exact hk,
      dsimp [l1],
      linarith [sn.H2],
    end
  }

lemma l7 (k : ℤ) (hk : nosq k) (sn : solution_normal k) : height (step k hk sn).s < height sn.s :=
begin
  dsimp [step],
  rw ← l6,
  simp,
  apply l4,
end

lemma heightn {k : ℤ} (s : solution k): ∃ (n : ℕ ), height s = n :=
begin
  have : height s ≥ 0,
  {
    dsimp [height]; linarith [s.req2],
  },
  cases int.le.dest this,
  use w,
  linarith,
end

lemma height_sequence (k : ℤ) (hk : nosq k) (sn : solution_normal k)
  : ∃ (f : ℕ → ℕ), (∀ n, f (n+1) < f n) :=
begin
  let sns : ℕ → solution_normal k := λ n, nat.rec_on n sn (λ _ sn, step k hk sn),
  have hh : ∀ (n : ℕ), ∃ (n2 : ℕ ), height (sns n).s = n2,
  {
    intro n2,
    apply heightn,
  },
  choose s1 s2 using hh,
  use s1,

  intro n,
  rw ← int.coe_nat_lt_coe_nat_iff,
  rw ← s2 n,
  rw ← s2 (n+1),
  apply l7,
end

lemma wfseq (f : ℕ → ℕ) (H : ∀ n, f (n+1) < f n) : false :=
begin
  have : ∀ k n, f n > k,
  {
    intro k,

    induction k with k hk,
    {
      intro n,
      specialize H n,
      linarith,
    },
    {
      intro n,
      specialize H n,
      specialize hk (n+1),
      calc k+1 < f (n+1) +1 : by linarith
      ... ≤ f n : H
    },
  },
  linarith [this (f 0) 0],
end

theorem no_pos_solution (k : ℤ) (hk : nosq k) (sp : solution_pos k) : false :=
begin
  cases (height_sequence k hk (normal k sp)) with f hf,
  exact wfseq f hf,
end
