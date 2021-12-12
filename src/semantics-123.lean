-- based on a paper by Graham Hutton: https://www.cs.nott.ac.uk/~pszgmh/123.pdf
inductive aexpr : Type
| val : ℤ → aexpr
| add : aexpr → aexpr → aexpr

open aexpr

def eval :  aexpr →  ℤ
| (val n) := n
| (add e1 e2) := eval e1 + eval e2

inductive rule : aexpr → aexpr → Type
| eka (m n : ℤ) : rule (add (val m) (val n)) (val (m+n))
| toka (x1 x2 y: aexpr) (r: rule x1 x2) : rule (add x1 y) (add x2 y)
| kolo (y1 y2 x: aexpr) (r: rule y1 y2) : rule (add x y1) (add x y2)

theorem rules_sound (x x': aexpr) : rule x x' → eval x = eval x' :=
begin
  intro r,
  induction r with m n x1 x2 y r hr y1 y2 x r hr,
  {
    dsimp [eval],
    refl,
  },
  {
    dsimp [eval],
    simp [hr],
  },
  {
    dsimp [eval],
    simp [hr],
  },
end

inductive CStack : Type
| halt : CStack
| add (n : ℤ ) : CStack → CStack
| eval (y : aexpr) : CStack → CStack

mutual def eval', exec
with eval' : aexpr → CStack → ℤ
| (val n) c := exec c n
| (add x y) c := eval' x (CStack.eval y c)
with exec : CStack → ℤ → ℤ
| CStack.halt n := n
| (CStack.eval y c) n := eval' y (CStack.add n c)
| (CStack.add m c) n := exec c (m+n)
using_well_founded { dec_tac := `[sorry] }

theorem abstract_machine (x: aexpr) : ∀ c, eval' x c = exec c (eval x) :=
begin
  induction x with n x y hx hy,
  {
    intro c,
    rw [eval, eval'],
  },
  {
    intro c,
    rw [eval', hx, exec, hy, exec, eval],
  }
end
