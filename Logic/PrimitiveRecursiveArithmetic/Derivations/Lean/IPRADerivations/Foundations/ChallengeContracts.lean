import IPRADerivations.Core.Order
import IPRADerivations.Core.Header

/-!
# Finite challenge contracts (`ipra_categorical_methods`, Section 3)

Packet: `foundations/ipra_categorical_methods`, Section "A category of finite challenge
contracts": the proposition "Realization transport" and the local law of the theorem
"Contract composition", for fixed presentations.

A contract `A` (`Contract`) consists of formulas `X_A(x)` (proposed data), `U_A(u)`
(questions) and a test `R_A(x, u)`. Its realization assertion is

`Real(A) ≡ ∃x (X_A(x) ∧ ∀u (U_A(u) → R_A(x, u)))`.

An arrow `A → B` (`Arrow`) is a forward term `f(x)` and a finite family of source questions
for every target question `v`: `q(i, x, v)` for `i < c(x, v)`. This is the finite query set
`Q_f(x, v)` of the packet, given by an indexed family, so that no coding of finite sets is
needed; `All_A(x, Q_f(x, v))` is the bounded statement `allQ`:
`∀ i < c(x, v). R_A(x, q(i, x, v))`. The laws (`Arrow.Laws`) are the typing of `f` and of the
queries and the local law (C) `All_A(x, Q_f(x, v)) → R_B(f(x), v)`, as rules derivable at
arbitrary terms and hypotheses.

* `transport_at`: a valid witness `x` answering every question of `A` is sent to `f(x)`
  answering every question of `B`;
* `transport` ("Realization transport"): `Real(A) → Real(B)`; closed form `transport_closed`.
  The witness for `B` is `f(x)`: there is no choice of a witness separately for each `v`;
* `idArrow`, `idArrow_laws`: the identity arrow `1_A(x) = x`, `Q(x, u) = {u}`;
* `comp_local` ("Contract composition", formula (D)): for `F : A → B` and `G : B → C`, the
  composite forward map `g(f(x))` with the union of query sets
  `⋃_{v ∈ Q_g(f(x), w)} Q_f(x, v)`, here the doubly indexed family `allQQ`, satisfies the
  local law (C);
* `comp_typ`: the composite queries are valid source questions;
* `transport_comp`: `Real(A) → Real(C)`.

Not derived here: the equality of arrows and the category laws up to it, the product and
terminal contracts, the finite-table category of contracts, the example of regular rational
names and variable-length chains.
-/

namespace LeanProofs.IPRA.Foundations.ChallengeContracts

open_ipra exports

variable {k : ℕ} {Γ : List (Fm PTm k)}

private theorem up_shift {m j : ℕ} (σ : Fin m → PTm j) (t : PTm m) :
    Syn.subst (Syn.up σ) (Syn.shift t) = Syn.shift (Syn.subst σ t) := by
  rw [Syn.subst_shift, Syn.shift_subst]; simp

/-! ## Contracts -/

/-- A contract: data `X(x)`, questions `U(u)` and a test `R(x, u)`. -/
structure Contract where
  /-- `X(x)`; variable `0 = x`. -/
  X : Fm PTm 1
  /-- `U(u)`; variable `0 = u`. -/
  U : Fm PTm 1
  /-- `R(x, u)`; variables `0 = x`, `1 = u`. -/
  R : Fm PTm 2

namespace Contract

variable (A : Contract)

/-- `x` is valid data. -/
def wit (x : PTm k) : Fm PTm k := A.X.subst ![x]
/-- `u` is a valid question. -/
def ch (u : PTm k) : Fm PTm k := A.U.subst ![u]
/-- `x` answers the question `u`. -/
def ans (x u : PTm k) : Fm PTm k := A.R.subst ![x, u]

@[simp] theorem subst_wit {m : ℕ} (σ : Fin k → PTm m) (x : PTm k) :
    (A.wit x).subst σ = A.wit (Syn.subst σ x) := by
  simp only [wit, Fm.subst_subst]
  congr 1; funext j; fin_cases j; rfl

@[simp] theorem subst_ch {m : ℕ} (σ : Fin k → PTm m) (u : PTm k) :
    (A.ch u).subst σ = A.ch (Syn.subst σ u) := by
  simp only [ch, Fm.subst_subst]
  congr 1; funext j; fin_cases j; rfl

@[simp] theorem subst_ans {m : ℕ} (σ : Fin k → PTm m) (x u : PTm k) :
    (A.ans x u).subst σ = A.ans (Syn.subst σ x) (Syn.subst σ u) := by
  simp only [ans, Fm.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

/-- `x` answers every question: `∀u (U(u) → R(x, u))`. -/
def allCh (x : PTm k) : Fm PTm k := Fm.all (A.ch (var 0) ⟶ A.ans (Syn.shift x) (var 0))

@[simp] theorem subst_allCh {m : ℕ} (σ : Fin k → PTm m) (x : PTm k) :
    (A.allCh x).subst σ = A.allCh (Syn.subst σ x) := by
  simp only [allCh, Fm.subst_all, Fm.subst_imp, subst_ch, subst_ans, Syn.subst_var, Syn.up_zero,
    up_shift]

/-- The realization assertion `∃x (X(x) ∧ ∀u (U(u) → R(x, u)))`. -/
def Real : Fm PTm k := Fm.ex (A.wit (var 0) ⋏ A.allCh (var 0))

theorem shift_wit (x : PTm k) : Fm.shift (A.wit x) = A.wit (Syn.shift x) := by
  simp [Fm.shift, Syn.shift]

theorem shift_ch (u : PTm k) : Fm.shift (A.ch u) = A.ch (Syn.shift u) := by
  simp [Fm.shift, Syn.shift]

theorem shift_allCh (x : PTm k) : Fm.shift (A.allCh x) = A.allCh (Syn.shift x) := by
  simp [Fm.shift, Syn.shift]

theorem shift_Real : Fm.shift (A.Real (k := k)) = A.Real := by
  simp only [Real, Fm.shift, Fm.subst_ex, Fm.subst_and, subst_wit, subst_allCh, Syn.subst_var,
    Syn.up_zero]

/-- Instantiating `∀u (U(u) → R(x, u))` at a valid question. -/
theorem allCh_elim {x u : PTm k} (h : Γ ⊢[PRAAx] A.allCh x) (hu : Γ ⊢[PRAAx] A.ch u) :
    Γ ⊢[PRAAx] A.ans x u := by
  have e := Prf.allE u h
  simp only [Fm.subst_imp, subst_ch, subst_ans, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at e
  exact .impE e hu

end Contract

/-! ## Arrows -/

/-- An arrow of contracts: a forward map and an indexed finite family of source questions. -/
structure Arrow where
  /-- The forward map `f(x)`; variable `0 = x`. -/
  fw : PTm 1
  /-- The number `c(x, v)` of source questions for the target question `v`; variables
  `0 = x`, `1 = v`. -/
  cnt : PTm 2
  /-- The `i`-th source question `q(i, x, v)`; variables `0 = i`, `1 = x`, `2 = v`. -/
  qr : PTm 3

namespace Arrow

variable (F : Arrow)

/-- `f(x)`. -/
def f (x : PTm k) : PTm k := Syn.subst ![x] F.fw
/-- `c(x, v)`. -/
def c (x v : PTm k) : PTm k := Syn.subst ![x, v] F.cnt
/-- `q(i, x, v)`. -/
def q (i x v : PTm k) : PTm k := Syn.subst ![i, x, v] F.qr

@[simp] theorem subst_f {m : ℕ} (σ : Fin k → PTm m) (x : PTm k) :
    Syn.subst σ (F.f x) = F.f (Syn.subst σ x) := by
  simp only [f, Syn.subst_subst]
  congr 1; funext j; fin_cases j; rfl

@[simp] theorem subst_c {m : ℕ} (σ : Fin k → PTm m) (x v : PTm k) :
    Syn.subst σ (F.c x v) = F.c (Syn.subst σ x) (Syn.subst σ v) := by
  simp only [c, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

@[simp] theorem subst_q {m : ℕ} (σ : Fin k → PTm m) (i x v : PTm k) :
    Syn.subst σ (F.q i x v) = F.q (Syn.subst σ i) (Syn.subst σ x) (Syn.subst σ v) := by
  simp only [q, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

theorem shift_f (x : PTm k) : Syn.shift (F.f x) = F.f (Syn.shift x) := by simp [Syn.shift]

theorem shift_c (x v : PTm k) : Syn.shift (F.c x v) = F.c (Syn.shift x) (Syn.shift v) := by
  simp [Syn.shift]

/-- `All_A(x, Q_f(x, v))`: `x` answers every source question asked for `v`,
`∀ i < c(x, v). R_A(x, q(i, x, v))`. -/
def allQ (A : Contract) (x v : PTm k) : Fm PTm k :=
  Fm.all (lt (var 0) (Syn.shift (F.c x v)) ⟶
    A.ans (Syn.shift x) (F.q (var 0) (Syn.shift x) (Syn.shift v)))

/-- The laws of an arrow `A → B`: typing of the forward map and of the queries, and the local
law (C). -/
structure Laws (A B : Contract) : Prop where
  fwd : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x : PTm k},
    (Γ ⊢[PRAAx] A.wit x) → (Γ ⊢[PRAAx] B.wit (F.f x))
  qtyp : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x v i : PTm k},
    (Γ ⊢[PRAAx] A.wit x) → (Γ ⊢[PRAAx] B.ch v) → (Γ ⊢[PRAAx] lt i (F.c x v)) →
      (Γ ⊢[PRAAx] A.ch (F.q i x v))
  loc : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {x v : PTm k},
    (Γ ⊢[PRAAx] A.wit x) → (Γ ⊢[PRAAx] B.ch v) → (Γ ⊢[PRAAx] F.allQ A x v) →
      (Γ ⊢[PRAAx] B.ans (F.f x) v)

end Arrow

open Contract Arrow

/-! ## Realization transport -/

section Transport

variable {A B C : Contract} {F G : Arrow}

/-- A witness of `A` answering every question is sent by `f` to a witness of `B` answering
every question. -/
theorem transport_at (H : F.Laws A B) {x : PTm k} (hx : Γ ⊢[PRAAx] A.wit x)
    (hall : Γ ⊢[PRAAx] A.allCh x) : Γ ⊢[PRAAx] B.wit (F.f x) ⋏ B.allCh (F.f x) := by
  refine .andI (H.fwd hx) (.allI (.impI ?_))
  -- a fresh target question `v = var 0`
  rw [shift_f]
  have hx₁ : (B.ch (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] A.wit (Syn.shift x) := by
    have h := hx.shift
    rw [shift_wit] at h
    exact h.wk
  have ha₁ : (B.ch (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] A.allCh (Syn.shift x) := by
    have h := hall.shift
    rw [shift_allCh] at h
    exact h.wk
  have hv₁ : (B.ch (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] B.ch (var 0) := Prf.hyp0
  refine H.loc hx₁ hv₁ (.allI (.impI ?_))
  -- a fresh index `i = var 0` below the number of source questions
  rw [shift_c]
  have hx₂ := hx₁.shift
  rw [shift_wit] at hx₂
  have ha₂ := ha₁.shift
  rw [shift_allCh] at ha₂
  have hv₂ := hv₁.shift
  rw [shift_ch] at hv₂
  exact allCh_elim A ha₂.wk (H.qtyp hx₂.wk hv₂.wk Prf.hyp0)

/-- Realization transport: `Real(A) → Real(B)` along an arrow `A → B`. -/
theorem transport (H : F.Laws A B) (h : Γ ⊢[PRAAx] A.Real) : Γ ⊢[PRAAx] B.Real := by
  refine .exE h ?_
  rw [shift_Real]
  refine .exI (F.f (var 0)) ?_
  simp only [Fm.subst_and, subst_wit, subst_allCh, Syn.subst_var, Syn.inst_zero]
  exact transport_at H (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)

/-- Realization transport as a closed theorem of iPRA. -/
theorem transport_closed (H : F.Laws A B) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] A.Real ⟶ B.Real :=
  .impI (transport H Prf.hyp0)

/-! ## The identity arrow -/

/-- `1_A(x) = x` with the single question `Q(x, u) = {u}`. -/
def idArrow : Arrow where
  fw := var 0
  cnt := succ zero
  qr := var 2

theorem idArrow_f (x : PTm k) : idArrow.f x = x := by simp [Arrow.f, idArrow]

theorem idArrow_c (x v : PTm k) : idArrow.c x v = succ zero := by simp [Arrow.c, idArrow]

theorem idArrow_q (i x v : PTm k) : idArrow.q i x v = v := by simp [Arrow.q, idArrow]

/-- The identity arrow satisfies the laws; (C) is `R_A(x, u) → R_A(x, u)`. -/
theorem idArrow_laws (A : Contract) : idArrow.Laws A A where
  fwd := fun h => by rw [idArrow_f]; exact h
  qtyp := fun _ hv _ => by rw [idArrow_q]; exact hv
  loc := fun {k Γ x v} _ _ hq => by
    rw [idArrow_f]
    have e := Prf.allE (zero : PTm k) hq
    simp only [Fm.subst_imp, subst_lt, subst_ans, idArrow_c, idArrow_q, Syn.subst_var,
      Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] at e
    exact .impE e (le_refl _)

/-! ## Composition: the demand formula (D) -/

/-- `All_A(x, Q_{g∘f}(x, w))` for the union (D)
`Q_{g∘f}(x, w) = ⋃_{v ∈ Q_g(f(x), w)} Q_f(x, v)`:
`∀ i < c_g(f(x), w). ∀ j < c_f(x, v_i). R_A(x, q_f(j, x, v_i))` with `v_i = q_g(i, f(x), w)`. -/
def allQQ (F G : Arrow) (A : Contract) (x w : PTm k) : Fm PTm k :=
  Fm.all (lt (var 0) (Syn.shift (G.c (F.f x) w)) ⟶
    F.allQ A (Syn.shift x) (G.q (var 0) (Syn.shift (F.f x)) (Syn.shift w)))

/-- The composite queries are valid source questions: for `i < c_g(f(x), w)` and
`j < c_f(x, v_i)`, `q_f(j, x, v_i)` is a question of `A`. -/
theorem comp_typ (HF : F.Laws A B) (HG : G.Laws B C) {x w i j : PTm k}
    (hx : Γ ⊢[PRAAx] A.wit x) (hw : Γ ⊢[PRAAx] C.ch w)
    (hi : Γ ⊢[PRAAx] lt i (G.c (F.f x) w))
    (hj : Γ ⊢[PRAAx] lt j (F.c x (G.q i (F.f x) w))) :
    Γ ⊢[PRAAx] A.ch (F.q j x (G.q i (F.f x) w)) :=
  HF.qtyp hx (HG.qtyp (HF.fwd hx) hw hi) hj

/-- The local law (C) of the composite: if `x` answers every question of the union (D), then
`g(f(x))` answers `w`. -/
theorem comp_local (HF : F.Laws A B) (HG : G.Laws B C) {x w : PTm k}
    (hx : Γ ⊢[PRAAx] A.wit x) (hw : Γ ⊢[PRAAx] C.ch w)
    (h : Γ ⊢[PRAAx] allQQ F G A x w) : Γ ⊢[PRAAx] C.ans (G.f (F.f x)) w := by
  refine HG.loc (HF.fwd hx) hw (.allI (.impI ?_))
  -- a fresh index `i = var 0` into `Q_g(f(x), w)`; put `v = q_g(i, f(x), w)`
  rw [shift_c, shift_f]
  have hx₁ := hx.shift
  rw [shift_wit] at hx₁
  have hw₁ := hw.shift
  rw [shift_ch] at hw₁
  have h₁ := h.allOpen
  rw [shift_c, shift_f] at h₁
  have hv : (lt (var 0) (G.c (F.f (Syn.shift x)) (Syn.shift w)) :: Γ.map Fm.shift) ⊢[PRAAx]
      B.ch (G.q (var 0) (F.f (Syn.shift x)) (Syn.shift w)) :=
    HG.qtyp (HF.fwd hx₁.wk) hw₁.wk Prf.hyp0
  exact HF.loc hx₁.wk hv (.impE h₁.wk Prf.hyp0)

/-- Realization transport along a composite. -/
theorem transport_comp (HF : F.Laws A B) (HG : G.Laws B C) (h : Γ ⊢[PRAAx] A.Real) :
    Γ ⊢[PRAAx] C.Real :=
  transport HG (transport HF h)

end Transport

end LeanProofs.IPRA.Foundations.ChallengeContracts
