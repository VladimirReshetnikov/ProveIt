import IPRADerivations.Foundations.ChallengeContracts
import IPRADerivations.Combinatorics.IndependentSets
import IPRADerivations.Core.SumReflect

/-!
# Products of challenge contracts (`ipra_categorical_methods`, Section 3)

Packet: `foundations/ipra_categorical_methods`, Subsection "Finite products express
conjunction of tasks". For contracts `A = (X, U, R)` and `B = (Y, V, S)`
(`Foundations/ChallengeContracts`) the product contract `prod A B` has

* witnesses: pairs `z = ⟨x, y⟩` with `X(x)` and `Y(y)` (the pairing of `Core/Pairing`);
* questions: tagged numbers, `inl u = 2u` and `inr v = 2v + 1`; a number `c` is a question
  when its half is a question of the component named by its parity;
* test: `T(z, inl u) = R(x, u)` and `T(z, inr v) = S(y, v)`.

Derived:

* `pair_real`: witnesses of `A` and `B` answering all questions give the pair, answering all
  questions of the product (the pairing);
* `prod_fst`, `prod_snd`: a witness of the product answering all questions gives its two
  components, each answering all questions of its contract (the projections; the question `u`
  of `A` is asked as `inl u`);
* `real_prod`: `Real(A × B) ↔ Real(A) ∧ Real(B)`: the product contract expresses the
  conjunction of the two tasks; closed form `real_prod_closed`.

`wit_congr`, `ch_congr`, `ans_congr`: the contract formulas respect derivable equality of
terms.

The projections and the pairing are not packaged as `Arrow`s, and the universal property
with respect to equality of arrows is not derived.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ContractProducts

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.ChallengeContracts
open LeanProofs.IPRA.Foundations.ChallengeContracts.Contract
open LeanProofs.IPRA.Combinatorics.IndependentSets (half_double half_double_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Congruence -/

section Congr

variable (A : Contract)

theorem wit_congr {x x' : PTm k} (h : Γ ⊢[PRAAx] x ≐ x') (hw : Γ ⊢[PRAAx] A.wit x) :
    Γ ⊢[PRAAx] A.wit x' :=
  Prf.eqSubst A.X ![x] ![x'] (fun i => by fin_cases i; exact h) hw

theorem ch_congr {u u' : PTm k} (h : Γ ⊢[PRAAx] u ≐ u') (hc : Γ ⊢[PRAAx] A.ch u) :
    Γ ⊢[PRAAx] A.ch u' :=
  Prf.eqSubst A.U ![u] ![u'] (fun i => by fin_cases i; exact h) hc

theorem ans_congr {x x' u u' : PTm k} (hx : Γ ⊢[PRAAx] x ≐ x') (hu : Γ ⊢[PRAAx] u ≐ u')
    (ha : Γ ⊢[PRAAx] A.ans x u) : Γ ⊢[PRAAx] A.ans x' u' :=
  Prf.eqSubst A.R ![x, u] ![x', u'] (fun i => by
    fin_cases i
    · exact hx
    · exact hu) ha

end Congr

/-! ## The product contract -/

/-- The product contract: pairs of witnesses, questions tagged by parity. -/
def prod (A B : Contract) : Contract where
  X := A.wit (fstT (var 0)) ⋏ B.wit (sndT (var 0))
  U := (par (var 0) ≐ zero ⟶ A.ch (half (var 0))) ⋏ (par (var 0) ≐ one ⟶ B.ch (half (var 0)))
  R := (par (var 1) ≐ zero ⟶ A.ans (fstT (var 0)) (half (var 1))) ⋏
    (par (var 1) ≐ one ⟶ B.ans (sndT (var 0)) (half (var 1)))

section Product

variable (A B : Contract)

theorem prod_wit (z : PTm k) :
    (prod A B).wit z = (A.wit (fstT z) ⋏ B.wit (sndT z)) := by
  show ((prod A B).X).subst ![z] = _
  simp [prod]

theorem prod_ch (c : PTm k) :
    (prod A B).ch c =
      ((par c ≐ zero ⟶ A.ch (half c)) ⋏ (par c ≐ one ⟶ B.ch (half c))) := by
  show ((prod A B).U).subst ![c] = _
  simp [prod]

theorem prod_ans (z c : PTm k) :
    (prod A B).ans z c =
      ((par c ≐ zero ⟶ A.ans (fstT z) (half c)) ⋏ (par c ≐ one ⟶ B.ans (sndT z) (half c))) := by
  show ((prod A B).R).subst ![z, c] = _
  simp [prod]

theorem shift_fstT (z : PTm k) : Syn.shift (fstT z) = fstT (Syn.shift z) := by simp [Syn.shift]

theorem shift_sndT (z : PTm k) : Syn.shift (sndT z) = sndT (Syn.shift z) := by simp [Syn.shift]

private theorem one_zero_absurd (φ : Fm PTm k) {a : PTm k} (h₀ : Γ ⊢[PRAAx] a ≐ zero)
    (h₁ : Γ ⊢[PRAAx] a ≐ one) : Γ ⊢[PRAAx] φ :=
  .botE _ (succ_ne_zero (a := zero) (h₁.eqSymm.eqTrans h₀))

variable {A B}

/-- The pairing: witnesses of `A` and `B` answering all questions give a witness of the
product answering all questions. -/
theorem pair_real {x y : PTm k} (hx : Γ ⊢[PRAAx] A.wit x) (hxa : Γ ⊢[PRAAx] A.allCh x)
    (hy : Γ ⊢[PRAAx] B.wit y) (hyb : Γ ⊢[PRAAx] B.allCh y) :
    Γ ⊢[PRAAx] (prod A B).wit (pairT x y) ⋏ (prod A B).allCh (pairT x y) := by
  refine .andI ?_ (.allI (.impI ?_))
  · rw [prod_wit]
    exact .andI (wit_congr A (fst_pair x y).eqSymm hx) (wit_congr B (snd_pair x y).eqSymm hy)
  · -- a fresh question `c = var 0` of the product
    rw [shift_pairT, prod_ans]
    have hU : ((prod A B).ch (var 0) :: Γ.map Fm.shift) ⊢[PRAAx]
        (par (var 0) ≐ zero ⟶ A.ch (half (var 0))) ⋏ (par (var 0) ≐ one ⟶ B.ch (half (var 0))) :=
      (congrArg (fun φ => ((prod A B).ch (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] φ)
        (prod_ch A B (var 0))).mp Prf.hyp0
    have ha : ((prod A B).ch (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] A.allCh (Syn.shift x) := by
      have h := hxa.shift
      rw [shift_allCh] at h
      exact h.wk
    have hb : ((prod A B).ch (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] B.allCh (Syn.shift y) := by
      have h := hyb.shift
      rw [shift_allCh] at h
      exact h.wk
    refine .andI (.impI ?_) (.impI ?_)
    · exact ans_congr A (fst_pair _ _).eqSymm (.eqRefl _)
        (allCh_elim A ha.wk (.impE (Prf.andE₁ hU).wk Prf.hyp0))
    · exact ans_congr B (snd_pair _ _).eqSymm (.eqRefl _)
        (allCh_elim B hb.wk (.impE (Prf.andE₂ hU).wk Prf.hyp0))

/-- The first projection: the question `u` of `A` is asked as `inl u = 2u`. -/
theorem prod_fst {z : PTm k} (hz : Γ ⊢[PRAAx] (prod A B).wit z)
    (hall : Γ ⊢[PRAAx] (prod A B).allCh z) :
    Γ ⊢[PRAAx] A.wit (fstT z) ⋏ A.allCh (fstT z) := by
  have hz' := hz
  rw [prod_wit] at hz'
  refine .andI (.andE₁ hz') (.allI (.impI ?_))
  rw [shift_fstT]
  have hP : (A.ch (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] (prod A B).allCh (Syn.shift z) := by
    have h := hall.shift
    rw [shift_allCh] at h
    exact h.wk
  -- the tagged question `2u` is a question of the product
  have hc : (A.ch (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] (prod A B).ch (two * var 0) := by
    rw [prod_ch]
    exact .andI (.impI (ch_congr A (half_double _).eqSymm Prf.hyp1))
      (.impI (one_zero_absurd _ (par_double _) Prf.hyp0))
  have r := allCh_elim (prod A B) hP hc
  rw [prod_ans] at r
  exact ans_congr A (.eqRefl _) (half_double _) (.impE (Prf.andE₁ r) (par_double _))

/-- The second projection: the question `v` of `B` is asked as `inr v = 2v + 1`. -/
theorem prod_snd {z : PTm k} (hz : Γ ⊢[PRAAx] (prod A B).wit z)
    (hall : Γ ⊢[PRAAx] (prod A B).allCh z) :
    Γ ⊢[PRAAx] B.wit (sndT z) ⋏ B.allCh (sndT z) := by
  have hz' := hz
  rw [prod_wit] at hz'
  refine .andI (.andE₂ hz') (.allI (.impI ?_))
  rw [shift_sndT]
  have hP : (B.ch (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] (prod A B).allCh (Syn.shift z) := by
    have h := hall.shift
    rw [shift_allCh] at h
    exact h.wk
  have hc : (B.ch (var 0) :: Γ.map Fm.shift) ⊢[PRAAx] (prod A B).ch (two * var 0 + one) := by
    rw [prod_ch]
    exact .andI (.impI (one_zero_absurd _ Prf.hyp0 (par_double_succ _)))
      (.impI (ch_congr B (half_double_succ _).eqSymm Prf.hyp1))
  have r := allCh_elim (prod A B) hP hc
  rw [prod_ans] at r
  exact ans_congr B (.eqRefl _) (half_double_succ _) (.impE (Prf.andE₂ r) (par_double_succ _))

/-- `Real(A × B) → Real(A) ∧ Real(B)`. -/
theorem real_of_prod (h : Γ ⊢[PRAAx] (prod A B).Real) : Γ ⊢[PRAAx] A.Real ⋏ B.Real := by
  refine .exE h ?_
  show _ ⊢[PRAAx] (Fm.shift A.Real ⋏ Fm.shift B.Real)
  rw [shift_Real, shift_Real]
  refine .andI (.exI (fstT (var 0)) ?_) (.exI (sndT (var 0)) ?_)
  · simp only [Fm.subst_and, subst_wit, subst_allCh, Syn.subst_var, Syn.inst_zero]
    exact prod_fst (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)
  · simp only [Fm.subst_and, subst_wit, subst_allCh, Syn.subst_var, Syn.inst_zero]
    exact prod_snd (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)

/-- `Real(A) ∧ Real(B) → Real(A × B)`. -/
theorem prod_of_real (hA : Γ ⊢[PRAAx] A.Real) (hB : Γ ⊢[PRAAx] B.Real) :
    Γ ⊢[PRAAx] (prod A B).Real := by
  refine .exE hA ?_
  rw [shift_Real]
  -- `x = var 0` is the witness of `A`
  have hB₁ : ((A.wit (var 0) ⋏ A.allCh (var 0)) :: Γ.map Fm.shift) ⊢[PRAAx] B.Real := by
    have h := hB.shift
    rw [shift_Real] at h
    exact h.wk
  refine .exE hB₁ ?_
  rw [shift_Real]
  -- now `y = var 0` is the witness of `B` and `x = Syn.shift (var 0)`
  have hx : ((B.wit (var 0) ⋏ B.allCh (var 0)) ::
      ((A.wit (var 0) ⋏ A.allCh (var 0)) :: Γ.map Fm.shift).map Fm.shift) ⊢[PRAAx]
      A.wit (Syn.shift (var 0)) ⋏ A.allCh (Syn.shift (var 0)) := by
    have h := (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift)
      (φ := A.wit (var 0) ⋏ A.allCh (var 0))).shift
    have e : Fm.shift (A.wit (var 0 : PTm (k + 1)) ⋏ A.allCh (var 0)) =
        (A.wit (Syn.shift (var 0)) ⋏ A.allCh (Syn.shift (var 0))) := by
      show (Fm.shift (A.wit (var 0)) ⋏ Fm.shift (A.allCh (var 0))) = _
      rw [shift_wit, shift_allCh]
    rw [e] at h
    exact h.wk
  refine .exI (pairT (Syn.shift (var 0)) (var 0)) ?_
  simp only [Fm.subst_and, subst_wit, subst_allCh, Syn.subst_var, Syn.inst_zero]
  exact pair_real (.andE₁ hx) (.andE₂ hx) (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)

/-- The product contract expresses the conjunction of the two tasks. -/
theorem real_prod : Γ ⊢[PRAAx] Fm.iff ((prod A B).Real) (A.Real ⋏ B.Real) :=
  .iffI (.impI (real_of_prod Prf.hyp0))
    (.impI (prod_of_real (.andE₁ Prf.hyp0) (.andE₂ Prf.hyp0)))

/-- `Real(A × B) ↔ Real(A) ∧ Real(B)` as a closed theorem of iPRA, for all contracts. -/
theorem real_prod_closed (A B : Contract) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] Fm.iff ((prod A B).Real) (A.Real ⋏ B.Real) :=
  real_prod

end Product

end LeanProofs.IPRA.Foundations.ContractProducts
