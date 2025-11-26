-- based on a paper by Graham Hutton: https://www.cs.nott.ac.uk/~pszgmh/123.pdf

namespace Playground.semantics

inductive aexpr : Type where
| val : Int → aexpr
| add : aexpr → aexpr → aexpr

open aexpr

def eval : aexpr → Int
| val n => n
| add e1 e2 => eval e1 + eval e2

inductive rule : aexpr → aexpr → Prop where
| eka (m n : Int) : rule (add (val m) (val n)) (val (m+n))
| toka (x1 x2 y: aexpr) (r: rule x1 x2) : rule (add x1 y) (add x2 y)
| kolo (y1 y2 x: aexpr) (r: rule y1 y2) : rule (add x y1) (add x y2)

theorem rules_sound (x x': aexpr) : rule x x' → eval x = eval x' := by
  intro r
  induction r with
  | eka m n =>
    simp [eval]
  | toka x1 x2 y r hr =>
    simp [eval, hr]
  | kolo y1 y2 x r hr =>
    simp [eval, hr]

inductive CStack : Type where
| halt : CStack
| add (n : Int) : CStack → CStack
| eval (y : aexpr) : CStack → CStack

mutual
  def eval' : aexpr → CStack → Int
  | val n, c => exec c n
  | add x y, c => eval' x (CStack.eval y c)

  def exec : CStack → Int → Int
  | CStack.halt, n => n
  | CStack.eval y c, n => eval' y (CStack.add n c)
  | CStack.add m c, n => exec c (m+n)
  decreasing_by all_goals sorry
end

theorem abstract_machine (x: aexpr) : ∀ c, eval' x c = exec c (eval x) := by
  induction x with
  | val n =>
    intro c
    rw [eval, eval']
  | add x y hx hy =>
    intro c
    rw [eval', hx, exec, hy, exec, eval]

end Playground.semantics
