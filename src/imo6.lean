import Mathlib.Data.Int.Basic
import Mathlib.Tactic


structure solution (k : ℤ) where
  req0 : k ≥ 1
  a : ℤ
  b : ℤ
  req1 : a^2 + b^2 = k*(a*b+1)
  req2 : a ≥ 0 ∧ b ≥ 0

structure solution_pos (k : ℤ) where
  s : solution k
  pos : s.a > 0 ∧ s.b > 0

def nosq (k : ℤ) : Prop := ¬ ∃ l : ℤ , k = l*l

-- Goal is to prove that if k isn't a square then ∄ positive solution
-- Follows idea from https://www.youtube.com/watch?v=WCI5OaBKME4

def l1 (k  : ℤ) (s : solution k) (H2 : s.b ≥ 1) : solution k := by
  let a1 := k*s.b-s.a -- integer, must be positive
  let b := s.b
  let a := s.a
  have h : a1^2 + b^2 = k*(a1*b+1) := by
    dsimp [a1]
    calc (k*b-a)^2 + b^2 = k^2*b^2 - 2*k*b*a + (a^2+b^2) := by ring
      _ = k^2*b^2 - 2*k*b*a + k*(a*b+1) := by rw [s.req1]
      _ = k*((k*b-a)*b+1) := by ring
  have h2 : a1 ≥ 0 := by
    by_contra hh
    have h3 : a1 < 0 := by
      simp at hh ⊢
      assumption
    have h4 : a1*b+1 ≤ 0 := by
      have : a1 * s.b < 0 := Int.mul_neg_of_neg_of_pos h3 (by omega : s.b > 0)
      apply Int.lt_iff_add_one_le.mp
      dsimp [b]
      exact this
    have h5 : k*(a1*b+1) ≤ 0 := by
      rw [(by ring : 0 = k * 0)]
      apply Int.mul_le_mul_of_nonneg_left h4
      linarith [s.req0]
    have h6 : a1^2 + b^2 > 0 := by
      have : 1*1 ≤ b*b := by
        exact Int.mul_self_le_mul_self (by omega : 0 ≤ (1 : Int)) H2
      have : a1*a1 ≥ 0 := by
        exact mul_self_nonneg a1
      linarith
    omega
  have s : solution k := by
    exact solution.mk (s.req0) a1 b h ⟨h2, by omega⟩
  exact s

lemma l2 (k : ℤ ) (s : solution k) (H2 : s.b ≥ 1)
  : (l1 k s H2).a * s.a = (s.b^2 - k) := by
  dsimp [l1]
  have : s.b^2 = -s.a^2 + k*(s.a*s.b+1) := by linarith [s.req1]
  rw [this]
  ring_nf

lemma l3 (k : ℤ ) (s : solution k) (H2 : s.b ≥ 1) (H1 : s.a ≥ s.b)
  : (l1 k s H2).a < s.a := by
  have ha_pos : s.a > 0 := by
    calc s.a ≥ s.b := H1
      _ ≥ 1 := H2
      _ > 0 := by norm_num
  have h := l2 k s H2
  have : (l1 k s H2).a * s.a < s.a * s.a := by
    rw [h]
    calc s.b^2 - k < s.b^2 := by linarith [s.req0]
      _ = s.b * s.b := by ring_nf
      _ ≤ s.a * s.a := mul_self_le_mul_self (by linarith) H1
  exact Int.lt_of_mul_lt_mul_right this (Int.le_of_lt ha_pos)

-- can I define this to be `→ ℕ` ??
def height {k : ℤ}: solution k → ℤ :=
  fun s => (s.a + s.b)

lemma l4 (k : ℤ) (s : solution k) (H2 : s.b ≥ 1) (H1 : s.a ≥ s.b)
  : height (l1 k s H2) < height s := by
  dsimp [height]
  calc (l1 k s H2).a + (l1 k s H2).b = (l1 k s H2).a + s.b := rfl
    _ < s.a + s.b := by linarith [l3 k s H2 H1]

lemma l5 (k : ℤ) (s : solution k) (H2 : s.b ≥ 1) (H3 : nosq k)
  : (l1 k s H2).a > 0 := by
  cases' (l1 k s H2).req2.left.lt_or_eq with h h
  · assumption
  · exfalso
    -- l2 : (l1 k s H2).a * s.a = (s.b^2 - k) :=
    have : 0 = s.b^2 - k := by
      calc 0 = 0 * s.a := by ring
        _ = (l1 k s H2).a * s.a := by rw [h]
        _ = s.b^2 - k := l2 k s H2
    apply H3
    use s.b
    linarith [this]

structure solution_normal (k : ℤ) where
  s : solution k
  H2 : s.b ≥ 1
  H1 : s.a ≥ s.b

def normal (k : ℤ) (sp : solution_pos k) : solution_normal k := by
  by_cases h : sp.s.a ≥ sp.s.b
  · apply solution_normal.mk sp.s
    · linarith [sp.pos.right]
    · assumption
  · exact {
      s := by
        apply solution.mk sp.s.req0 sp.s.b sp.s.a
        · let hh := sp.s.req1
          calc sp.s.b ^ 2 + sp.s.a ^ 2 = sp.s.a ^ 2 + sp.s.b ^ 2 := by ring
            _ = k * (sp.s.a * sp.s.b + 1) := hh
            _ = k * (sp.s.b * sp.s.a + 1) := by ring
        · constructor <;> linarith [sp.s.req2, sp.pos]
      H2 := by
        simp
        linarith [sp.pos.left]
      H1 := by
        simp
        linarith [h]
    }

lemma l6 (k : ℤ) (sp : solution_pos k) : height sp.s = height (normal k sp).s := by
  by_cases h : sp.s.b ≤ sp.s.a
  · dsimp [normal]
    simp [h]
  · dsimp [normal]
    simp [h]
    dsimp [height]
    ring

def step (k : ℤ) (hk : nosq k) (sn : solution_normal k) : solution_normal k :=
  normal k {
    s := l1 k sn.s sn.H2,
    pos := by
      constructor
      · apply l5
        exact hk
      · dsimp [l1]
        linarith [sn.H2]
  }

lemma l7 (k : ℤ) (hk : nosq k) (sn : solution_normal k) : height (step k hk sn).s < height sn.s := by
  dsimp [step]
  rw [← l6]
  simp
  apply l4
  exact sn.H1

lemma heightn {k : ℤ} (s : solution k): ∃ (n : ℕ ), height s = n := by
  have : height s ≥ 0 := by
    dsimp [height]
    linarith [s.req2]
  cases' Int.le.dest this with w h
  use w
  linarith

lemma height_sequence (k : ℤ) (hk : nosq k) (sn : solution_normal k)
  : ∃ (f : ℕ → ℕ), (∀ n, f (n+1) < f n) := by
  let sns : ℕ → solution_normal k := fun n => Nat.recOn n sn (fun _ sn => step k hk sn)
  have hh : ∀ (n : ℕ), ∃ (n2 : ℕ ), height (sns n).s = n2 := by
    intro n2
    apply heightn
  choose s1 s2 using hh
  use s1
  intro n
  rw [← Nat.cast_lt (α := ℤ)]
  rw [← s2 n]
  rw [← s2 (n+1)]
  apply l7

lemma wfseq (f : ℕ → ℕ) (H : ∀ n, f (n+1) < f n) : False := by
  have : ∀ k n, f n > k := by
    intro k
    induction k with
    | zero =>
      intro n
      specialize H n
      exact Nat.pos_of_ne_zero (fun h => Nat.not_lt.mpr (Nat.zero_le _) (h ▸ H))
    | succ k hk =>
      intro n
      specialize H n
      specialize hk (n+1)
      calc k+1 < f (n+1) +1 := by linarith
        _ ≤ f n := H
  specialize this (f 0) 0
  linarith

theorem no_pos_solution (k : ℤ) (hk : nosq k) (sp : solution_pos k) : False := by
  cases' height_sequence k hk (normal k sp) with f hf
  exact wfseq f hf
