variables P Q R : Prop

theorem dmg1: ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  constructor,
  assume npq,
  constructor,
  assume p,
  apply npq,
  left,
  assumption,
  assume q,
  apply npq,
  right,
  assumption,
  assume npnq,
  cases npnq with np nq,
  assume pq,
  cases pq with p q,
  apply np,
  exact p,
  apply nq,
  exact q,
end

open classical

theorem raa: ¬ P ∨ P :=
begin
  cases (em P) with p np,
  right,
  exact p,
  left,
  exact np,
end

theorem dmg2: ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  constructor,
  assume npq,
  cases (em P) with p np,
  right,
  assume q,
  apply npq,
  constructor,
  exact p,
  assumption,
  left,
  exact np,

  assume npnq,
  assume pq,
  cases pq with p q,
  cases npnq with np nq,
  apply np,
  exact p,
  apply nq,
  exact q,
end

theorem q1c1 : P → (Q ∧ R) ↔ (P → Q) ∧ (P → R) :=
begin
  constructor,
  assume pqr,
  constructor,
  sorry,
  sorry,

  assume pqpr,
  cases pqpr with pq pr,
  assume p,
  constructor,
  apply pq,
  assumption,
  apply pr,
  assumption,
end

theorem q1c2 : (P ∧ Q) → R ↔ (P → R) ∧ (Q → R) :=
begin
  constructor,
  assume pqr,
  constructor,
  assume p,
  apply pqr,
  constructor,
  assumption,
  sorry,
  assume q,
  apply pqr,
  constructor,
  sorry,
  assumption,

  assume prqr,
  assume pq,
  cases prqr with pr qr,
  cases pq with p q,
  apply pr,
  exact p,
end

theorem q1c3 : P → (Q ∨ R) ↔ (P → Q) ∨ (P → R) :=
begin
  constructor,
  assume pqr,
  left,
  assume p,
  sorry,

  assume pqpr,
  assume p,
  cases pqpr with pq pr,
  left,
  apply pq,
  assumption,
  right,
  apply pr,
  assumption,
end

theorem q1c4 : (P ∨ Q) → R ↔ (P → R) ∧ (Q → R) :=
begin
  constructor,
  assume pqr,
  constructor,
  assume p,
  apply pqr,
  left,
  assumption,
  assume q,
  apply pqr,
  right,
  assumption,

  assume prqr,
  cases prqr with pr qr,
  assume pq,
  cases pq with p q,
  apply pr,
  exact p,
  apply qr,
  exact q,
end

theorem q1c5 : (P ∨ Q) → R ↔ (P → R) ∧ (Q → R) :=
begin
  constructor,
  assume pqr,
  constructor,
  assume p,
  apply pqr,
  left,
  assumption,
  assume q,
  apply pqr,
  right,
  assumption,

  assume prqr,
  cases prqr with pr qr,
  assume pq,
  cases pq with p q,
  apply pr,
  exact p,
  apply qr,
  exact q,
end

theorem neg_raa : ¬ ¬ ¬ P → ¬ P :=
begin
  assume nnnp,
  assume p,
  apply nnnp,
  assume np,
  apply np,
  assumption,
end

variable People : Type
variable Loves : People → People → Prop

-- (i)
theorem q2b1 : ∀ x : People, ∃ y : People, Loves x y := sorry

-- (ii)
theorem q2b2 : ∃ y : People, ∀ x : People, Loves x y := sorry

-- (iii)
theorem q2b3 : ∀ x y z : People, ¬ ((Loves x y) ∧ (Loves y z) → Loves x z) := sorry

-- (iv)
theorem q2b4 : ∃ x : People, ∀ y : People, ¬ (Loves x y) := sorry

-- (v)
theorem q2b5 : ∀ x y : People, ¬ (Loves x y → Loves y x) := sorry

def implb : bool → bool → bool
| x tt := tt
| tt _ := ff
| ff _ := tt

theorem q3a : ∀ x y : bool, (x = tt) → (y = tt) ↔ implb x y = tt :=
begin
  assume x y,
  constructor,
  assume xtyt,
  cases y,
  cases x,
  dsimp [implb],
  refl,
  dsimp [implb],
  apply xtyt,
  refl,
  cases x,
  dsimp [implb],
  refl,
  dsimp [implb],
  refl,
  assume ixyt,
  assume xt,
  rewrite xt at ixyt,
  cases y,
  dsimp [implb] at ixyt,
  exact ixyt,
  refl,
end

theorem q3b1 : ∀ x : bool, ∃ y : bool , x ≠ y :=
begin
  assume x,
  cases x,
  existsi tt,
  assume eq,
  cases eq,
  existsi ff,
  assume eq,
  cases eq,
end

theorem q3b2_neg : ¬ (∃ x : bool, ∀ y : bool , x ≠ y) :=
begin
  assume h,
  cases h with a b,
  cases a,
  have f: ff ≠ ff,
  apply b,
  apply f,
  refl,

  have t: tt ≠ tt,
  apply b,
  apply t,
  refl,
end

theorem q3b3 : ∀ x : bool, ∃ y : bool, x = y :=
begin
  assume x,
  existsi x,
  refl,
end

theorem q3b4_neg : ¬ (∃ x : bool, ∀ y : bool, x = y) :=
begin
  assume h,
  cases h with a b,
  cases a,
  have f: ff = tt,
  apply b,
  contradiction,

  have t: tt = ff,
  apply b,
  contradiction,
end

open nat

def foo : ℕ → ℕ 
| zero := 1
| (succ zero) := 0 
| (succ (succ n)) := succ (succ (foo n))

#eval foo 4
#eval foo 5

#eval foo 0
#eval foo 1

#eval foo 2
#eval foo 3

#eval foo 6
#eval foo 7

inductive my_list (A : Type)
| nil : my_list
| cons : A → my_list → my_list

inductive Tree : Type
| leaf : ℕ → Tree
| node : Tree → Tree → Tree

def t1 : Tree := Tree.node (Tree.node (Tree.leaf 1) (Tree.leaf 2)) (Tree.leaf 3)

def tree2list : Tree → list ℕ
| (Tree.leaf n) := [n]
| (Tree.node t1 t2) := (tree2list t1) ++ (tree2list t2)

#eval tree2list t1

variables {A B C : Type}

inductive Insert : A → list A → list A → Prop
| ins_hd : ∀ a : A, ∀ as : list A, Insert a as (a :: as)
| ins_tl : ∀ a b : A, ∀ as as' : list A, Insert a as as' → Insert a (b :: as) (b :: as')

inductive Perm : list A → list A → Prop
| perm_nil : Perm [] []
| perm_cons : ∀ a : A, ∀ as bs bs' : list A, Perm as bs → Insert a bs bs' → Perm (a :: as) bs'

open Insert
open Perm

example: Perm [1, 2] [2, 1] :=
begin
  apply perm_cons 1 [2] [2] [2, 1],
  apply perm_cons 2 [] [] [2],
  apply perm_nil,
  apply ins_hd,
  apply ins_tl,
  apply ins_hd,
end

def is_tt : bool → Prop
| ff := false
| tt := true 

theorem not_thm : ∀ x : bool, ¬ (is_tt x) ↔ is_tt (bnot x) :=
begin
  assume x,
  constructor,
  assume ntx,
  cases x,
  dsimp [bnot, is_tt],
  constructor,
  dsimp [bnot, is_tt],
  dsimp [is_tt] at ntx,
  apply ntx,
  constructor,

  assume tnx,
  cases x,
  dsimp [is_tt],
  assume f,
  assumption,
  dsimp [is_tt],
  assume t,
  dsimp [bnot, is_tt] at tnx,
  exact tnx,
end

theorem or_thm : ∀ x y: bool, is_tt x ∨ is_tt y ↔ is_tt (x || y) :=
begin
  assume x y,
  constructor,
  cases x,
  dsimp [bor, is_tt],
  assume txty,
  cases txty with tx ty,
  cases tx,
  exact ty,
  dsimp [is_tt],
  assume txty,
  constructor,

  cases x,
  dsimp [bor, is_tt],
  assume ttxy,
  right,
  exact ttxy,
  dsimp [bor, is_tt],
  assume t,
  left,
  constructor,
end

def my_implb: bool → bool → bool
| tt ff := ff
| _ _ := tt

-- def my : bool → bool → bool
-- | tt tt := tt
-- | ff tt := tt
-- | tt ff := ff
-- | ff ff := tt

def eqb : bool → bool → bool
| tt tt := tt
| ff ff := tt
| _ _ := ff
