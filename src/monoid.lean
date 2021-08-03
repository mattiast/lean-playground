import tactic

structure A := (a : int) (b : int) (c : int)

instance : has_mul A :=
  ⟨λ x y, A.mk (x.a+y.a) (x.b+y.b+x.a*y.c) (x.c+y.c)⟩

def A_assoc : @associative A has_mul.mul :=
begin
  intros x y z,
  cases x,
  cases y,
  cases z,

  dsimp only [has_mul.mul],
  congr' 1,
  linarith,
  simp,
  ring,
  linarith,
end

instance A_monoid : monoid A := {
  mul := has_mul.mul,
  mul_assoc := A_assoc,
  one := A.mk 0 0 0,
  one_mul := begin
    intro x,
    cases x,
    dsimp only [has_one.one ,has_mul.mul],
    congr' ; simp,
  end,
  mul_one := begin
    intro x,
    cases x,
    dsimp only [has_one.one ,has_mul.mul],
    congr' ; simp,
  end,
}
