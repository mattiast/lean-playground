import tactic.induction
import tactic

inductive eexpr : Type
| int : ℤ → eexpr
| str : string → eexpr
| var : ℕ → eexpr
| plus : eexpr → eexpr → eexpr
| cat : eexpr → eexpr → eexpr
| len : eexpr → eexpr
| lett : eexpr → eexpr → eexpr

inductive typ : Type
| num : typ
| str : typ

def env : Type := list typ

def lookup (n : ℕ ) (τ : typ) (Γ : env) : Prop :=
  list.nth Γ n = some τ

lemma lookup_lt (n : ℕ ) (τ : typ) (Γ : env) (h : lookup n τ Γ ) :
  n < list.length Γ :=
begin
  induction' Γ ,
  simp [lookup] at h,
  contradiction,
  cases' n,
  simp,
  simp,
  have : n < Γ.length, {
    apply ih n τ,
    simp [lookup],
    simp [lookup] at h,
    assumption,
  },
  exact nat.succ_lt_succ this,
end

-- Typing derivations
inductive has_type : env → eexpr → typ → Prop
| refl (n : ℕ ) (τ : typ) (Γ : env) :
      lookup n τ Γ →
      has_type Γ (eexpr.var n) τ
| strlit (s : string) (Γ : env) :
      has_type Γ (eexpr.str s) typ.str
| numlit (n : ℤ) (Γ : env) :
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
  ∀ τ2, (has_type Γ e τ2) → τ1 = τ2 :=
begin
  induction' h1,
  all_goals {
    try {
      intros τ2 h2,
      cases h2,
      refl,
    }
  },
  case refl : v τ Γ h {
    intros τ2 hh,
    cases' hh,
    simp [lookup] at *,
    apply option.some.inj,
    rw ← h,
    rw ← h_1,
  },
  case has_type.lett {
    intros τ2 h2,
    cases' h2,
    have : τ1 = τ1_2,
    {
      apply ih_h1,
      assumption,
    },
    rw ← this at *,
    apply ih_h1_1,
    assumption,
  }
end

lemma env_append (Γ : env) (stuff : list typ) (n : ℕ ) (τ : typ) :
  lookup n τ Γ → lookup n τ (list.append Γ stuff) :=
begin
  induction' Γ ,
  simp [lookup],
  cases' n,
  simp [lookup],
  simp [lookup] at *,
  apply ih,
end

-- Weakening: you can add extra stuff in the context and typing doesn't change
lemma weakening (Γ : env) (stuff : list typ) (e : eexpr) (τ : typ) :
  has_type Γ e τ → has_type (list.append Γ stuff) e τ :=
begin
  intros ht,
  induction' ht,
  case refl {
    apply has_type.refl,
    apply env_append,
    assumption,
  },
  case strlit {
    constructor,
  },
  case numlit {
    constructor,
  },
  case lett {
    apply has_type.lett _ _ τ1 τ,
    {
      apply ih_ht,
    },
    {
      simp [list.append] at ih_ht_1,
      apply ih_ht_1,
    },
  },
  case plus {
    constructor,
    apply ih_ht,
    apply ih_ht_1,
  },
  case cat {
    constructor,
    apply ih_ht,
    apply ih_ht_1,
  },
  case len {
    constructor,
    apply ih,
  },
end

-- Example of typing inversion: plus expression and its parts can only have num type
lemma inversion_plus (Γ : env) (e1 e2 : eexpr) (τ : typ) (h : has_type Γ (eexpr.plus e1 e2) τ):
  τ = typ.num ∧ (has_type Γ e1 typ.num) ∧ (has_type Γ e2 typ.num) :=
begin
  cases' h,
  split,
  refl,
  split,
  assumption',
end

def incr : ℕ → eexpr → eexpr
| n (eexpr.var n1) := eexpr.var (if (n1 < n) then n1 else nat.succ n1)
| n (eexpr.int x) := eexpr.int x
| n (eexpr.str x) := eexpr.str x
| n (eexpr.plus e1 e2) := eexpr.plus (incr n e1) (incr n e2)
| n (eexpr.cat e1 e2) := eexpr.cat (incr n e1) (incr n e2)
| n (eexpr.len e1) := eexpr.len (incr n e1)
| n (eexpr.lett e1 e2) := eexpr.lett (incr n e1) (incr (nat.succ n) e2)

def subst : ℕ → eexpr → eexpr → eexpr
| _ _ (eexpr.int n) := eexpr.int n
| _ _ (eexpr.str n) := eexpr.str n
| n e (eexpr.plus e1 e2) := eexpr.plus (subst n e e1) (subst n e e2)
| n e (eexpr.cat e1 e2) := eexpr.cat (subst n e e1) (subst n e e2)
| n e (eexpr.len e1) := eexpr.len (subst n e e1)
| n e (eexpr.var n1) := ite (n = n1) e (eexpr.var n1)
| n e (eexpr.lett e1 e2) := (eexpr.lett (subst n e e1) (subst (nat.succ n) (incr 0 e) e2))


lemma closed_incr (e : eexpr) (τ : typ) (Γ : env) (ht : has_type Γ  e τ) (n : ℕ ) (hn : n >= list.length Γ ):
  incr n e = e :=
begin
  induction' ht,
  case refl {
    dsimp [incr],
    simp [hn],
    have : n_1 < list.length Γ, apply lookup_lt _ _ _ h,
    intro h1,
    linarith,
  },
  case lett {
    simp [incr],
    split,
    exact ih_ht n hn,
    apply ih_ht_1 n.succ,
    simp [list.length],
    apply nat.succ_le_succ,
    linarith,
  },
  all_goals { try { simp [incr]}},
  case plus {
    split,
    apply ih_ht, assumption,
    apply ih_ht_1, assumption,
  },
  case cat {
    split,
    apply ih_ht, assumption,
    apply ih_ht_1, assumption,
  },
  case len {
    apply ih, assumption,
  },
end

variable {α : Type}

@[simp] def insert_nth : ∀ (l : list α) (n : ℕ) (h : n ≤ l.length), α → list α
| xs 0 _ a := a :: xs
| (x::xs) (nat.succ i) h a := x :: insert_nth xs i (nat.le_of_succ_le_succ h) a
| []      (nat.succ i) h _ := absurd h (by {simp [list.length]})

lemma blah (l : list α) (h : 0 ≤ l.length) (x : α):
  insert_nth l 0 h x = x :: l :=
begin
  induction' l,
  simp,
  simp,
end

lemma map_insert (l : list α) (x : α) (n n1 : ℕ) (hn : n ≤ l.length) :
  (list.nth (insert_nth l n hn x) (ite (n1 < n) n1 n1.succ)) = list.nth l n1 :=
begin
  induction' l,
  simp [insert_nth],
  have hh : n = 0, {
    simp [list.length] at hn,
    assumption,
  },
  cases' n,
  simp,
  apply nat.succ_le_succ,
  exact zero_le n1,
  contradiction,


  cases' n,
  simp [insert_nth],
  simp [insert_nth],
  cases' n1,
  simp,
  simp [list.nth],
  have : n ≤ l.length, {
    simp [list.length] at hn,
    apply nat.succ_le_succ_iff.mp,
    assumption',
  },
  specialize ih x n n1 this,
  have : ite (n1.succ < n.succ) n1.succ n1.succ.succ = (ite (n1 < n) n1 n1.succ).succ, {
    by_cases (n1 < n),
    simp [h],
    intro hh,
    rw nat.succ_le_succ_iff at hh,
    exact nat.lt_le_antisymm h hh,
    simp [h],
    intro hh,
    rw nat.succ_lt_succ_iff at hh,
    contradiction,
  },
  rw this,
  simp [list.nth],
  exact ih,
end

lemma incr_type (e : eexpr) (τ τ' : typ) (Γ : env)
  (ht : has_type Γ e τ) (n : ℕ ) (hn : n ≤ list.length Γ ) :
  has_type (insert_nth Γ n hn τ') (incr n e) τ :=
begin
  induction' ht,
  all_goals { simp [incr]},
  case refl {
    constructor,
    simp [lookup],
    rw (map_insert),
    simp [lookup] at h,
    assumption,
  },
  case lett {
    apply has_type.lett _ _ τ1,
    apply ih_ht,
    specialize ih_ht_1 τ' n.succ,
    simp [insert_nth] at ih_ht_1,
    apply ih_ht_1,
    exact nat.succ_le_succ hn,
  },
  case strlit {
    constructor,
  },
  case numlit {
    constructor,
  },
  case plus {
    constructor,
    apply ih_ht,
    apply ih_ht_1,
  },
  case cat {
    constructor,
    apply ih_ht,
    apply ih_ht_1,
  },
  case len {
    constructor,
    apply ih,
  }
end

lemma type_subst
  (e e' : eexpr) (Γ : env) (τ τ' : typ)
  (n : ℕ ) (te : has_type Γ e τ)
  (hn : lookup n τ Γ )
  (te' : has_type Γ e' τ')
  : has_type Γ (subst n e e') τ'
  :=
begin
  -- induction on the derivation of te'
  induction' te',
  case refl {
    dsimp [subst],
    by_cases hh : (n=n_1),
    rw ← hh at *,
    simp,
    have : τ' = τ,
    {
      simp [lookup] at *,
      apply option.some.inj,
      rw ← hn,
      rw ← h,
    },
    rw this,
    assumption,
    simp [hh],
    constructor,
    assumption,
  },
  case lett {
    dsimp [subst],
    apply has_type.lett _ _ τ1 τ',
    {
      apply ih_te',
      exact te,
      exact hn,
    },
    {
      apply ih_te'_1 (incr 0 e) τ n.succ,
      rw ← blah _ (nat.zero_le Γ.length),
      apply incr_type,
      exact te,
      dsimp [lookup],
      dsimp [lookup] at hn,
      assumption,
    },
  },
  {
    apply has_type.strlit,
  },
  {
    apply has_type.numlit,
  },
  case plus {
    apply has_type.plus,
    exact ih_te' _ _ _ te hn,
    exact ih_te'_1 _ _ _ te hn,
  },
  case cat {
    apply has_type.cat,
    exact ih_te' _ _ _ te hn,
    exact ih_te'_1 _ _ _ te hn,
  },
  case len {
    apply has_type.len,
    exact ih _ _ _ te hn,
  },
end
