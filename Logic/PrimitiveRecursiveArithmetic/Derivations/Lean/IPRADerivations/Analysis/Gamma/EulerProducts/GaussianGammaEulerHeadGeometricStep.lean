import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerHeadExponentStep
import IPRADerivations.Analysis.Polynomials.GaussianCoefficientGeometricCancellation

/-!
# Original head factors under the actual geometric coefficient convolution

The unchanged original head reader's proved numerical successor is
lifted through the genuine finite geometric convolution. Every terminal
zero coefficient is proved before trimming the original sum. For the
newly added actual reciprocal point, the original geometric cancellation
then leaves exactly that reciprocal times the original preceding head
coefficient. This is the finite cancellation step for Newton's identity.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadGeometricStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qadd qmul)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianGammaEulerHeadPolynomial (polynomial)
open GaussianGammaEulerHeadExponentStep (reader reader_congr reader_zero original_reader_step)
open GaussianGammaHarmonicIncrement (reciprocalPoint)
open GaussianCoefficientGeometricCancellation (body)
open GaussianRationalFiniteSum (sum)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (a N s : PTm n) : PTm n := GaussianCoefficientGeometricCancellation.data a (polynomial N) (succ N) s
def term (a N s j : PTm n) : PTm n := GaussianCoefficientGeometricCancellation.term a (polynomial N) (succ N) s j
def value (a N s : PTm n) : PTm n := GaussianCoefficientGeometricCancellation.geometricSum a (polynomial N) (succ N) s
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (a N s : PTm n) :
    Syn.subst σ (data a N s) = data (Syn.subst σ a) (Syn.subst σ N) (Syn.subst σ s) := by simp [data]
@[simp] theorem subst_term {l : ℕ} (σ : Fin n → PTm l) (a N s j : PTm n) :
    Syn.subst σ (term a N s j) = term (Syn.subst σ a) (Syn.subst σ N) (Syn.subst σ s) (Syn.subst σ j) := by simp [term]
@[simp] theorem subst_value {l : ℕ} (σ : Fin n → PTm l) (a N s : PTm n) :
    Syn.subst σ (value a N s) = value (Syn.subst σ a) (Syn.subst σ N) (Syn.subst σ s) := by simp [value]

theorem term_at (a N s j : PTm n) : Γ ⊢[PRAAx] inst2 body j (data a N s) ≐ term a N s j :=
  GaussianCoefficientGeometricCancellation.term_at _ _ _ _ _

theorem last_zero (a N s : PTm n) : Γ ⊢[PRAAx] term a N s s ≐ qzero :=
  (qmul_congr (.eqRefl _) (qmul_congr (.eqRefl _)
    ((reader_congr (.eqRefl N) (monus_self s)).eqTrans (reader_zero N)))).eqTrans
      ((qmul_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qmul_zero_right _)).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_right _))

theorem trim (a N s : PTm n) : Γ ⊢[PRAAx] value a N s ≐ sum body s (data a N s) :=
  (GaussianRationalFiniteSum.sum_succ body s (data a N s)).eqTrans
    ((qadd_congr (.eqRefl _) ((term_at _ _ _ _).eqTrans (last_zero _ _ _))).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalFiniteSum.sum_canonical _ _ _)))

theorem value_zero (a N : PTm n) : Γ ⊢[PRAAx] value a N zero ≐ qzero :=
  (trim a N zero).eqTrans (GaussianRationalFiniteSum.sum_zero _ _)

theorem commute_nested (x y z : PTm n) : Γ ⊢[PRAAx] qmul x (qmul y z) ≐ qmul y (qmul x z) :=
  (GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
    ((qmul_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _)).eqTrans
      (GaussianReciprocalHorner.qmul_associative _ _ _))

theorem term_step (a N s j : PTm n) (hj : Γ ⊢[PRAAx] le j s) : Γ ⊢[PRAAx]
    term a (succ N) (succ s) j ≐ qadd (term a N (succ s) j) (qmul (reciprocalPoint N) (term a N s j)) := by
  have idx := GaussianRationalPowerExpansion.remaining_before (Γ := Γ) s j hj
  have input : Γ ⊢[PRAAx] reader (succ N) (monus (succ s) j) ≐
      qadd (reader N (monus (succ s) j)) (qmul (reciprocalPoint N) (reader N (monus s j))) :=
    (reader_congr (.eqRefl _) idx).eqTrans
      ((original_reader_step N (monus s j)).eqTrans
        (qadd_congr (reader_congr (.eqRefl _) idx.eqSymm) (.eqRefl _)))
  exact (qmul_congr (.eqRefl _) (qmul_congr (.eqRefl _) input)).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianRationalCoefficientScaling.qmul_add _ _ _)).eqTrans
      ((GaussianRationalCoefficientScaling.qmul_add _ _ _).eqTrans
        (qadd_congr (.eqRefl _) ((qmul_congr (.eqRefl _) (commute_nested _ _ _)).eqTrans (commute_nested _ _ _)))))

theorem linear_terms (a N s : PTm n) : Γ ⊢[PRAAx] GaussianInverseBinomialRows.linearTerms body body body
    (succ s) (data a (succ N) (succ s)) (data a N (succ s)) (data a N s) (reciprocalPoint N) := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift s)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift s) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have h := (term_at (Γ := Δ) (Syn.shift a) (succ (Syn.shift N)) (succ (Syn.shift s)) (var 0)).eqTrans
    ((term_step _ _ _ _ hi).eqTrans (qadd_congr (term_at _ _ _ _).eqSymm
      (qmul_congr (.eqRefl _) (term_at _ _ _ _).eqSymm)))
  simpa only [Δ,Syn.shift,subst_data,GaussianGammaHarmonicIncrement.subst_reciprocalPoint,PTm.subst_succ] using h

theorem original_geometric_step (a N s : PTm n) : Γ ⊢[PRAAx]
    value a (succ N) (succ s) ≐ qadd (value a N (succ s)) (qmul (reciprocalPoint N) (value a N s)) :=
  (trim a (succ N) (succ s)).eqTrans
    ((GaussianInverseBinomialRows.linear_sum body body body _ _ _ _ _ (linear_terms a N s)).eqTrans
      (qadd_congr (trim a N (succ s)).eqSymm (.eqRefl _)))

theorem original_new_factor_cancellation (N s : PTm n) : Γ ⊢[PRAAx]
    value (reciprocalPoint N) (succ N) (succ s) ≐ qmul (reciprocalPoint N) (reader N (succ s)) :=
  (original_geometric_step (reciprocalPoint N) N s).eqTrans
    (GaussianCoefficientGeometricCancellation.exact_cancellation _ _ _ _)

theorem original_Euler_head_geometric_convolution_successor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (value (var 0) (succ (var 1)) (succ (var 2)) ≐
      qadd (value (var 0) (var 1) (succ (var 2)))
        (qmul (reciprocalPoint (var 1)) (value (var 0) (var 1) (var 2)))) :=
  closeUniv 3 (original_geometric_step _ _ _)

theorem original_Euler_head_new_factor_geometric_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (value (reciprocalPoint (var 0)) (succ (var 0)) (succ (var 1)) ≐
      qmul (reciprocalPoint (var 0)) (reader (var 0) (succ (var 1)))) :=
  closeUniv 2 (original_new_factor_cancellation _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerHeadGeometricStep
