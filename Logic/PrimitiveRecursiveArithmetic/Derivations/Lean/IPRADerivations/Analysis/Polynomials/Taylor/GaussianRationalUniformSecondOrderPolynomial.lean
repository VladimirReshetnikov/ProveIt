/-
Second-order expansion of the original Horner polynomial at a moving
rational anchor. Two padded synthetic divisions preserve degree, including
the constant-polynomial case. The cubic bound uses the original coefficient
mass and is uniform over both evaluation points.
-/
import IPRADerivations.Analysis.Polynomials.Taylor.GaussianRationalUniformFirstOrderPolynomial
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalInverseQuadraticAlgebra
import IPRADerivations.Foundations.DisjointSums

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianRationalUniformSecondOrderPolynomial

open_ipra
open GaussianRationalFirstOrderPolynomial (paddedQuotient padded_length slope increment_distance)
open GaussianRationalHorner (evaluate horner qmul qadd positive_product)
open GaussianRationalHornerLipschitz (geometric size_prefix evaluation_bound)
open GaussianEuclideanResidualRadius (coefficientBounds)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr quotient quotient_length quotient_lookup)
open GaussianRationalUniformFirstOrderPolynomial (mass quotient_coefficients)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (C t N : PTm n) : PTm n := slope (paddedQuotient C t N) t N

def quadratic (C t h N : PTm n) : PTm n :=
  qadd (qmul h (slope C t N)) (qmul (qmul h h) (coefficient C t N))

def error (C t h N : PTm n) : PTm n :=
  qsub (qsub (evaluate C (qadd t h)) (evaluate C t)) (quadratic C t h N)

def coefficientCap (M N U : PTm n) : PTm n := M*geometric U (succ N)
def errorGain (C N U : PTm n) : PTm n :=
  GaussianRationalHornerLipschitz.constant N U (coefficientCap (mass C U) N U)

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (C t N : PTm n) :
    Syn.subst σ (coefficient C t N) = coefficient (Syn.subst σ C) (Syn.subst σ t) (Syn.subst σ N) := by
  simp [coefficient]

@[simp] theorem subst_quadratic {m : ℕ} (σ : Fin n → PTm m) (C t h N : PTm n) :
    Syn.subst σ (quadratic C t h N) = quadratic (Syn.subst σ C) (Syn.subst σ t) (Syn.subst σ h) (Syn.subst σ N) := by
  simp [quadratic]

@[simp] theorem subst_errorGain {m : ℕ} (σ : Fin n → PTm m) (C N U : PTm n) :
    Syn.subst σ (errorGain C N U) = errorGain (Syn.subst σ C) (Syn.subst σ N) (Syn.subst σ U) := by
  simp [errorGain,coefficientCap]

theorem error_identity (C t h N : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N) : Γ ⊢[PRAAx]
    error C t h N ≐ qmul h (GaussianRationalFirstOrderPolynomial.remainder (paddedQuotient C t N) t h N) := by
  let s := qadd t h
  let Q := quotient C t N
  let D := paddedQuotient C t N
  let d := qsub (evaluate Q s) (evaluate Q t)
  let e := qsub (evaluate D s) (evaluate D t)
  let k := coefficient C t N
  have pad_s : Γ ⊢[PRAAx] evaluate D s ≐ evaluate Q s := GaussianRationalPolynomialBuffers.pad_evaluation Q one s
  have pad_t : Γ ⊢[PRAAx] evaluate D t ≐ evaluate Q t := GaussianRationalPolynomialBuffers.pad_evaluation Q one t
  have eq : Γ ⊢[PRAAx] d ≐ e := qsub_congr pad_s.eqSymm pad_t.eqSymm
  have first := (GaussianRationalInverseQuadraticAlgebra.subtract_sum (Γ := Γ)
    (qsub (evaluate C s) (evaluate C t)) (qmul h (slope C t N)) (qmul (qmul h h) k)).eqSymm
  have second : Γ ⊢[PRAAx] qsub (GaussianRationalFirstOrderPolynomial.remainder C t h N) (qmul (qmul h h) k) ≐
      qsub (qmul h e) (qmul h (qmul h k)) :=
    qsub_congr ((GaussianRationalFirstOrderPolynomial.remainder_identity C t h N hLen).eqTrans
      (qmul_congr (.eqRefl _) eq)) (GaussianReciprocalHorner.qmul_associative h h k)
  exact first.eqTrans (second.eqTrans (GaussianRationalRoundedPower.multiplication_difference h e (qmul h k)))

private theorem coefficient_at (C t N U M i : PTm n) (hC : Γ ⊢[PRAAx] coefficientBounds C M)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (ht : Γ ⊢[PRAAx] bounded t U one)
    (hi : Γ ⊢[PRAAx] lt i (length (paddedQuotient C t N))) : Γ ⊢[PRAAx]
    bounded (entry (paddedQuotient C t N) i) (coefficientCap M N U) one := by
  have range : Γ ⊢[PRAAx] le i N :=
    (succ_monus_succ _ _).eqSymm.eqTrans (lt_congr (.eqRefl _) (padded_length C t N) hi)
  refine .orE (lt_or_le i one) ?_ ?_
  · exact bound_congr (GaussianRationalPolynomialBuffers.pad_leading _ one i Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianMonicResidualRadius.zero_bounded (coefficientCap M N U) one (le_refl one))
  · let j := monus i one
    have idx : (le one i :: Γ) ⊢[PRAAx] i ≐ one+j := eq_add_of_le Prf.hyp0
    have jN : (le one i :: Γ) ⊢[PRAAx] lt j N :=
      le_congr (by ipra_ring) (.eqRefl _) (le_congr idx (.eqRefl _) range.wk)
    have row : (le one i :: Γ) ⊢[PRAAx] entry (paddedQuotient C t N) i ≐ horner C t (succ j) :=
      (entry_congr (.eqRefl _) idx).eqTrans
        ((GaussianRationalPolynomialBuffers.pad_tail _ one j (lt_congr (.eqRefl _) (quotient_length C t N).eqSymm jN)).eqTrans
          (quotient_lookup C t N j jN))
    have cap : (le one i :: Γ) ⊢[PRAAx] le (succ j) (length C) :=
      le_congr (.eqRefl _) hLen.wk.eqSymm (le_trans jN (le_succ_self N))
    have v := size_prefix C t M U (succ j) hC.wk ht.wk cap
    have grow : (le one i :: Γ) ⊢[PRAAx] le (geometric U (succ j)) (geometric U (succ N)) :=
      Foundations.DisjointSums.prefix_mono AnalyticNumberTheory.GoldbachGeometric.gB U (le_trans jN (le_succ_self N))
    exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
      (le_congr (by ipra_ring) (by unfold coefficientCap; ipra_ring) (Common.mul_le_mul (le_refl M) grow))
      (bound_congr row.eqSymm (.eqRefl _) (.eqRefl _) v)

theorem quotient_cap (C t N U M : PTm n) (hC : Γ ⊢[PRAAx] coefficientBounds C M)
    (hLen : Γ ⊢[PRAAx] length C ≐ succ N) (ht : Γ ⊢[PRAAx] bounded t U one) :
    Γ ⊢[PRAAx] coefficientBounds (paddedQuotient C t N) (coefficientCap M N U) := by
  have Cs : Γ.map Fm.shift ⊢[PRAAx] coefficientBounds (Syn.shift C) (Syn.shift M) := by
    simpa [Fm.shift,Syn.shift] using hC.shift
  have Ls : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using hLen.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift t) (Syn.shift U) one := by
    simpa [Fm.shift,Syn.shift] using ht.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,GaussianRationalFirstOrderPolynomial.subst_paddedQuotient,
    coefficientCap,PTm.subst_mul,GaussianRationalHornerLipschitz.subst_geometric,ConciseIPRA.PTm.subst_succ] using
    coefficient_at (Syn.shift C) (Syn.shift t) (Syn.shift N) (Syn.shift U) (Syn.shift M) (var 0)
      Cs.wk Ls.wk ts.wk Prf.hyp0

theorem cubic_bound (C t h N U A B : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ N)
    (hU : Γ ⊢[PRAAx] le one U) (ht : Γ ⊢[PRAAx] bounded t U one)
    (hx : Γ ⊢[PRAAx] bounded (qadd t h) U one) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] bounded h A B) : Γ ⊢[PRAAx]
    bounded (error C t h N) (errorGain C N U*A*A*A) (B*B*B) := by
  let D := paddedQuotient C t N
  let Q := quotient D t N
  let P := paddedQuotient D t N
  let M := coefficientCap (mass C U) N U
  let s := qadd t h
  have shape : Γ ⊢[PRAAx] length D ≐ succ N := padded_length C t N
  have cap := quotient_cap D t N U (mass C U) (quotient_coefficients C t N U hLen hU ht) shape ht
  have v := evaluation_bound P s t N U M A B (padded_length D t N) cap hx ht hB (increment_distance t h A B hB hh)
  have d : Γ ⊢[PRAAx] distanceBounded (evaluate Q s) (evaluate Q t) (errorGain C N U*A) B :=
    GaussianRationalDistanceOrder.distance_congr (GaussianRationalPolynomialBuffers.pad_evaluation Q one s)
      (GaussianRationalPolynomialBuffers.pad_evaluation Q one t) (.eqRefl _) (.eqRefl _) v
  have product := bounded_product _ _ _ _ _ _ hB hB hh d
  have r := bound_congr (GaussianRationalFirstOrderPolynomial.remainder_identity D t h N shape).eqSymm
    (.eqRefl _) (.eqRefl _) product
  have final := bounded_product _ _ _ _ _ _ hB (positive_product _ _ hB hB) hh r
  exact bound_congr (error_identity C t h N hLen).eqSymm (by ipra_ring) (by ipra_ring) final

theorem actual_horner_second_order_cubic_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (((length (var 0) ≐ succ (var 3)) ⋏ (le one (var 4) ⋏
      (bounded (var 1) (var 4) one ⋏ (bounded (qadd (var 1) (var 2)) (var 4) one ⋏
        (le one (var 6) ⋏ bounded (var 2) (var 5) (var 6)))))) ⟶
      bounded (error (var 0) (var 1) (var 2) (var 3)) (errorGain (var 0) (var 3) (var 4)*var 5*var 5*var 5)
        (var 6*var 6*var 6)) :=
  closeUniv 7 (.impI (cubic_bound _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalUniformSecondOrderPolynomial
