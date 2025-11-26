import Mathlib.Tactic

inductive eexpr : Type where
| int : Int → eexpr
| str : String → eexpr
| var : Nat → eexpr
| plus : eexpr → eexpr → eexpr
| cat : eexpr → eexpr → eexpr
| len : eexpr → eexpr
| lett : eexpr → eexpr → eexpr

inductive typ : Type where
| num : typ
| str : typ

def env : Type := List typ

-- Helper function for list indexing (Lean 3's List.nth)
def nth {α : Type} : List α → Nat → Option α
| [], _ => none
| a :: _, 0 => some a
| _ :: l, n + 1 => nth l n

def lookup (n : Nat) (τ : typ) (Γ : env) : Prop :=
  nth Γ n = some τ

lemma lookup_lt (n : Nat) (τ : typ) (Γ : env) (h : lookup n τ Γ) :
  n < List.length Γ := by
  induction Γ generalizing n with
  | nil =>
    simp [lookup,nth] at h
  | cons head tail ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp
      have : n < tail.length := by
        apply ih
        simp [lookup] at h
        assumption
      omega

-- Typing derivations
inductive has_type : env → eexpr → typ → Prop where
| refl (n : Nat) (τ : typ) (Γ : env) :
      lookup n τ Γ →
      has_type Γ (eexpr.var n) τ
| strlit (s : String) (Γ : env) :
      has_type Γ (eexpr.str s) typ.str
| numlit (n : Int) (Γ : env) :
      has_type Γ (eexpr.int n) typ.num
| plus (e1 e2 : eexpr) (Γ : env) :
      has_type Γ e1 typ.num →
      has_type Γ e2 typ.num →
      has_type Γ (eexpr.plus e1 e2) typ.num
| cat (e1 e2 : eexpr) (Γ : env) :
      has_type Γ e1 typ.str →
      has_type Γ e2 typ.str →
      has_type Γ (eexpr.cat e1 e2) typ.str
| len (e1 : eexpr) (Γ : env) :
      has_type Γ e1 typ.str →
      has_type Γ (eexpr.len e1) typ.num
| lett (e1 e2 : eexpr) (τ1 τ2: typ) (Γ : env):
      has_type Γ e1 τ1 →
      has_type (τ1 :: Γ) e2 τ2 →
      has_type Γ (eexpr.lett e1 e2) τ2

-- ∅ ⊢ let 1+1 in x0 : int
-- [int] ⊢ x0 : int

-- ∅ ⊢ let 1+1 in let "foo" in len(x0) + x1 : int
-- [int] ⊢ let "foo" in len(x0) + x1 : int
-- [str, int] ⊢ len(x0) + x1 : int

-- Unicity: term can only have one type
lemma unicity (Γ : env) (e : eexpr) (τ1 : typ) (h1 : has_type Γ e τ1) :
  ∀ τ2, (has_type Γ e τ2) → τ1 = τ2 := by
  induction h1 with
  | refl v τ Γ h =>
    intros τ2 hh
    cases hh with
    | refl _ _ _ h' =>
      simp [lookup] at *
      apply Option.some.inj
      rw [← h, ← h']
  | strlit s Γ =>
    intros τ2 h2
    cases h2
    rfl
  | numlit n Γ =>
    intros τ2 h2
    cases h2
    rfl
  | plus e1 e2 Γ h1 h2 ih1 ih2 =>
    intros τ2 h
    cases h
    rfl
  | cat e1 e2 Γ h1 h2 ih1 ih2 =>
    intros τ2 h
    cases h
    rfl
  | len e1 Γ h ih =>
    intros τ2 h2
    cases h2
    rfl
  | lett e1 e2 τ1 τ2 Γ h1 h2 ih1 ih2 =>
    intros τ2' h2'
    cases h2' with
    | lett _ _ τ1' _ _ h1' h2'' =>
      have : τ1 = τ1' := by
        apply ih1
        exact h1'
      rw [← this] at h2''
      apply ih2
      exact h2''

lemma env_append (Γ : env) (stuff : List typ) (n : Nat) (τ : typ) :
  lookup n τ Γ → lookup n τ (List.append Γ stuff) := by
  induction Γ generalizing n with
  | nil => simp [lookup, nth]
  | cons head tail ih =>
    cases n with
    | zero => simp [lookup, nth]
    | succ n =>
      intro h
      simp [lookup, nth] at h ih ⊢
      apply ih
      exact h

-- Weakening: you can add extra stuff in the context and typing doesn't change
lemma weakening (Γ : env) (stuff : List typ) (e : eexpr) (τ : typ) :
  has_type Γ e τ → has_type (List.append Γ stuff) e τ := by
  intros ht
  induction ht with
  | refl n τ Γ h =>
    apply has_type.refl
    apply env_append
    assumption
  | strlit =>
    constructor
  | numlit =>
    constructor
  | lett e1 e2 τ1 τ Γ h1 h2 ih1 ih2 =>
    apply has_type.lett _ _ τ1 τ
    · apply ih1
    · simp [List.append] at ih2
      apply ih2
  | plus e1 e2 Γ h1 h2 ih1 ih2 =>
    constructor
    apply ih1
    apply ih2
  | cat e1 e2 Γ h1 h2 ih1 ih2 =>
    constructor
    apply ih1
    apply ih2
  | len e1 Γ h ih =>
    constructor
    apply ih

-- Example of typing inversion: plus expression and its parts can only have num type
lemma inversion_plus (Γ : env) (e1 e2 : eexpr) (τ : typ) (h : has_type Γ (eexpr.plus e1 e2) τ):
  τ = typ.num ∧ (has_type Γ e1 typ.num) ∧ (has_type Γ e2 typ.num) := by
  cases h
  constructor
  rfl
  constructor <;> assumption

def incr : Nat → eexpr → eexpr
| n, eexpr.var n1 => eexpr.var (if (n1 < n) then n1 else Nat.succ n1)
| _, eexpr.int x => eexpr.int x
| _, eexpr.str x => eexpr.str x
| n, eexpr.plus e1 e2 => eexpr.plus (incr n e1) (incr n e2)
| n, eexpr.cat e1 e2 => eexpr.cat (incr n e1) (incr n e2)
| n, eexpr.len e1 => eexpr.len (incr n e1)
| n, eexpr.lett e1 e2 => eexpr.lett (incr n e1) (incr (Nat.succ n) e2)

def subst : Nat → eexpr → eexpr → eexpr
| _, _, (eexpr.int n) => eexpr.int n
| _, _, (eexpr.str n) => eexpr.str n
| n, e, (eexpr.plus e1 e2) => eexpr.plus (subst n e e1) (subst n e e2)
| n, e, (eexpr.cat e1 e2) => eexpr.cat (subst n e e1) (subst n e e2)
| n, e, (eexpr.len e1) => eexpr.len (subst n e e1)
| n, e, (eexpr.var n1) => if (n = n1) then e else (eexpr.var n1)
| n, e, (eexpr.lett e1 e2) => (eexpr.lett (subst n e e1) (subst (Nat.succ n) (incr 0 e) e2))


lemma closed_incr (e : eexpr) (τ : typ) (Γ : env) (ht : has_type Γ e τ) (n : Nat) (hn : n >= List.length Γ):
  incr n e = e := by
  induction ht generalizing n with
  | refl v τ Γ h =>
    simp only [incr]
    have hv : v < List.length Γ := lookup_lt _ _ _ h
    have : (v < n) := by linarith
    simp [this]
  | lett e1 e2 τ1 τ Γ h1 h2 ih1 ih2 =>
    simp [incr]
    constructor
    exact ih1 n hn
    apply ih2 n.succ
    simp [List.length]
    omega
  | strlit => simp [incr]
  | numlit => simp [incr]
  | plus e1 e2 Γ h1 h2 ih1 ih2 =>
    simp [incr]
    constructor
    apply ih1
    assumption
    apply ih2
    assumption
  | cat e1 e2 Γ h1 h2 ih1 ih2 =>
    simp [incr]
    constructor
    apply ih1
    assumption
    apply ih2
    assumption
  | len e1 Γ h ih =>
    simp [incr]
    apply ih
    assumption

variable {α : Type}

@[simp] def insert_nth : ∀ (l : List α) (n : Nat) (h : n ≤ l.length), α → List α
| xs, 0, _, a => a :: xs
| (x::xs), (Nat.succ i), h, a => x :: insert_nth xs i (Nat.le_of_succ_le_succ h) a
| [], (Nat.succ i), h, _ => absurd h (by simp [List.length])

lemma blah (l : List α) (h : 0 ≤ l.length) (x : α):
  insert_nth l 0 h x = x :: l := by
  induction l with
  | nil => simp
  | cons => simp

lemma map_insert (l : List α) (x : α) (n n1 : Nat) (hn : n ≤ l.length) :
  (nth (insert_nth l n hn x) (if (n1 < n) then n1 else n1.succ)) = nth l n1 := by
  induction l generalizing n n1 with
  | nil =>
    have hh : n = 0 := by
      simp [List.length] at hn
      assumption
    cases n with
    | zero =>
      simp [nth, insert_nth]
    | succ n =>
      simp [List.length] at hn
  | cons head tail ih =>
    cases n with
    | zero => simp [nth, insert_nth]
    | succ n =>
      cases n1 with
      | zero => simp [nth, insert_nth]
      | succ n1 =>
        simp only [nth, insert_nth]
        have hn' : n ≤ tail.length := by
          simp [List.length] at hn
          omega
        have eq : (if n1 + 1 < n + 1 then n1 + 1 else (n1 + 1).succ) =
                  (if n1 < n then n1 else n1.succ) + 1 := by
          by_cases h : n1 < n <;> simp [h, Nat.add_comm]
        rw [eq]
        exact ih n n1 hn'

         


lemma incr_type (e : eexpr) (τ τ' : typ) (Γ : env)
  (ht : has_type Γ e τ) (n : Nat) (hn : n ≤ List.length Γ) :
  has_type (insert_nth Γ n hn τ') (incr n e) τ := by
  induction ht generalizing n τ' with
  | refl v τ Γ h =>
    simp [incr]
    constructor
    simp [lookup]
    rw [map_insert]
    simp [lookup] at h
    exact h
  | lett e1 e2 τ1 τ Γ h1 h2 ih1 ih2 =>
    simp [incr]
    apply has_type.lett _ _ τ1
    · apply ih1
    · have hn' : n.succ ≤ (τ1 :: Γ).length := by simp; omega
      have := @ih2 τ' n.succ hn'
      simp only [insert_nth] at this
      exact this
  | strlit =>
    simp [incr]
    constructor
  | numlit =>
    simp [incr]
    constructor
  | plus e1 e2 Γ h1 h2 ih1 ih2 =>
    simp [incr]
    constructor
    apply ih1
    apply ih2
  | cat e1 e2 Γ h1 h2 ih1 ih2 =>
    simp [incr]
    constructor
    apply ih1
    apply ih2
  | len e1 Γ h ih =>
    simp [incr]
    constructor
    apply ih

lemma type_subst
  (e e' : eexpr) (Γ : env) (τ τ' : typ)
  (n : Nat) (te : has_type Γ e τ)
  (hn : lookup n τ Γ)
  (te' : has_type Γ e' τ')
  : has_type Γ (subst n e e') τ'
  := by
  -- induction on the derivation of te'
  induction te' generalizing n e τ with
  | refl n1 τ' Γ h =>
    simp only [subst]
    by_cases hh : (n = n1)
    · rw [hh]
      simp
      have eq : τ' = τ := by
        simp only [lookup] at h hn
        have : some τ' = some τ := by
          rw [← h]
          rw [hh] at hn
          exact hn
        exact Option.some.inj this
      rw [eq]
      exact te
    · simp [hh]
      constructor
      exact h
  | lett e1 e2 τ1 τ' Γ h1 h2 ih1 ih2 =>
    simp [subst]
    apply has_type.lett _ _ τ1 τ'
    · apply ih1
      exact te
      exact hn
    · apply ih2 (incr 0 e) τ n.succ
      rw [← blah _ (Nat.zero_le Γ.length)]
      apply incr_type
      exact te
      simp [lookup]
      simp [lookup] at hn
      assumption
  | strlit =>
    apply has_type.strlit
  | numlit =>
    apply has_type.numlit
  | plus e1 e2 Γ h1 h2 ih1 ih2 =>
    simp [subst]
    apply has_type.plus
    exact ih1 _ _ _ te hn
    exact ih2 _ _ _ te hn
  | cat e1 e2 Γ h1 h2 ih1 ih2 =>
    simp [subst]
    apply has_type.cat
    exact ih1 _ _ _ te hn
    exact ih2 _ _ _ te hn
  | len e1 Γ h ih =>
    simp [subst]
    apply has_type.len
    exact ih _ _ _ te hn
