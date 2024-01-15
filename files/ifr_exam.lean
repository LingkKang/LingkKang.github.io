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
