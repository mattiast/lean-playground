import data.real.basic

theorem imo6 (a b : ℕ ) :
  (∃ k, a^2 + b^2 = k*(a*b+1)) → (∃ l, a^2+b^2 = l*l*(a*b+1)) :=
begin
  rintro ⟨k, H⟩,
  sorry
end

-- pick (a,b) solution for that, which makes a+b minimal

lemma l1 (k a b : ℤ) (H2 : k ≥ 1 ∧ b ≥ 0) (H : a^2 + b^2 = k*(a*b+1)) (H1 : a ≤ b) : ℕ :=
begin
  let a1 := k*b-a, -- integer, must be positive
  have h : a1^2 + b^2 = k*(a1*b+1),
  {
    dsimp [a1],
    calc (k*b-a)^2 + b^2 = k^2*b^2 - 2*k*b*a + (a^2+b^2) : by ring
    ... = k^2*b^2 - 2*k*b*a + k*(a*b+1) : by rw H
    ... = k*((k*b-a)*b+1) : by ring
  },
  have h2 : a1 ≥ 0,
  {
    dsimp [a1],
    calc k * b - a ≥ k*b - b : by linarith
    ... = (k-1)*b : by ring
    ... ≥ 0 : int.mul_nonneg (by linarith) (by linarith)
  },
  exact 4,
end

-- data structure for such pairs (a,b)? prove functions and properties?

structure solution (k : ℤ) :=
  (req0 : k ≥ 1)
  (a : ℤ)
  (b : ℤ)
  (req1 : a^2 + b^2 = k*(a*b+1))
  (req2 : a ≥ 0 ∧ b ≥ 0)

def height {k : ℤ}: solution k → ℕ :=
  λ s, int.to_nat (s.a + s.b)
