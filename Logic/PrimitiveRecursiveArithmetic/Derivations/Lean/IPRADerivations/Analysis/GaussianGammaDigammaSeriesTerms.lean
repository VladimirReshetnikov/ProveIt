import IPRADerivations.Analysis.GaussianGammaDigammaSeries

/-!
# The literal reciprocal differences in the native digamma series

The original finite correction equals the actual sum of the Gaussian
rational terms 1/(j+1) − 1/(x+j), at every numerical cutoff.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaSeriesTerms

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (harmonicPoint)
open GaussianGammaDigammaFiniteSum (index reciprocalBody reciprocalSum reciprocal_entry)
open GaussianGammaDigammaSeries (partialValue)
open GaussianGammaHarmonicIncrement (reciprocalPoint harmonic_point_increment)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qadd_represents canonical_unique represents_congr)
open GaussianRationalL1 (rawGaussian rawDen raw_represents)
open GaussianRationalMetric (qsub qsub_represents qsub_canonical)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr rescale_to remainingDen remaining_den_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def termBody : PTm 2 := qsub (fraction one (succ (var 0))) reciprocalBody
def partialSum (a b N : PTm n) : PTm n := GaussianRationalFiniteSum.sum termBody N (pairT a b)

@[simp] theorem subst_partialSum {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (partialSum a b N) = partialSum (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [partialSum]

theorem term_at (a b j : PTm n) : Γ ⊢[PRAAx] inst2 termBody j (pairT a b) ≐
    qsub (reciprocalPoint j) (fraction b (index a b j)) := by
  have e : inst2 termBody j (pairT a b) = qsub (fraction one (succ j)) (inst2 reciprocalBody j (pairT a b)) := by
    simp [termBody,inst2]
  rw [e]
  exact qsub_congr (GaussianGammaDigammaStep.unit_step_value (succ j) (zero_lt_succ j)) (reciprocal_entry a b j)

theorem subtract_add_exchange (x y u v : PTm n) : Γ ⊢[PRAAx]
    qadd (qsub x y) (qsub u v) ≐ qsub (qadd x u) (qadd y v) := by
  let E := remainingDen x y u v
  have he := remaining_den_positive (Γ := Γ) x y u v
  have hx := rescale_to x (rawGaussian x) (rawDen x) (rawDen y*rawDen u*rawDen v) E
    (raw_represents (Γ := Γ) x) (by unfold E remainingDen; ipra_ring)
  have hy := rescale_to y (rawGaussian y) (rawDen y) (rawDen x*rawDen u*rawDen v) E
    (raw_represents (Γ := Γ) y) (by unfold E remainingDen; ipra_ring)
  have hu := rescale_to u (rawGaussian u) (rawDen u) (rawDen x*rawDen y*rawDen v) E
    (raw_represents (Γ := Γ) u) (by unfold E remainingDen; ipra_ring)
  have hv := rescale_to v (rawGaussian v) (rawDen v) (rawDen x*rawDen y*rawDen u) E
    (raw_represents (Γ := Γ) v) (by unfold E remainingDen; ipra_ring)
  have left := qadd_represents _ _ _ _ _ he (qsub_represents _ _ _ _ _ he hx hy) (qsub_represents _ _ _ _ _ he hu hv)
  have right := qsub_represents _ _ _ _ _ he (qadd_represents _ _ _ _ _ he hx hu) (qadd_represents _ _ _ _ _ he hy hv)
  apply canonical_unique _ _ _ _ (GaussianRationalHorner.qadd_canonical _ _) (qsub_canonical _ _) he (hrv := right)
  apply represents_congr (.eqRefl _) _ (.eqRefl _) left
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add] <;> ring

def equality (a b N : PTm n) : Fm PTm n := partialSum a b N ≐ partialValue a b N
@[simp] theorem subst_equality {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    (equality a b N).subst σ = equality (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [equality]

private theorem partial_zero (a b : PTm n) : Γ ⊢[PRAAx] equality a b zero :=
  (GaussianRationalFiniteSum.sum_zero termBody (pairT a b)).eqTrans
    ((qsub_congr GaussianGammaEulerHeadQuadratic.harmonic_zero (GaussianRationalFiniteSum.sum_zero reciprocalBody (pairT a b))).eqTrans
      GaussianRationalDeflationError.qsub_zero_zero).eqSymm

private theorem partial_succ (a b N : PTm n) (h : Γ ⊢[PRAAx] equality a b N) : Γ ⊢[PRAAx] equality a b (succ N) := by
  have e := (GaussianRationalFiniteSum.sum_succ (Γ := Γ) reciprocalBody N (pairT a b)).eqTrans (qadd_congr (.eqRefl _) (reciprocal_entry a b N))
  exact (GaussianRationalFiniteSum.sum_succ termBody N (pairT a b)).eqTrans ((qadd_congr h (term_at a b N)).eqTrans
    ((subtract_add_exchange (harmonicPoint N) (reciprocalSum a b N) (reciprocalPoint N) (fraction b (index a b N))).eqTrans
      (qsub_congr (harmonic_point_increment N).eqSymm e.eqSymm)))

theorem literal_partial_sum (a b N : PTm n) : Γ ⊢[PRAAx] partialSum a b N ≐ partialValue a b N := by
  have h : Γ ⊢[PRAAx] .all (equality (Syn.shift a) (Syn.shift b) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simpa only [subst_equality,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using partial_zero (Γ := Γ) a b
    · simpa only [subst_equality,Syn.subst_var,Syn.repl_zero,subst_repl_shift] using
        partial_succ (Syn.shift a) (Syn.shift b) (var 0) Prf.hyp0
  have e : Γ ⊢[PRAAx] equality a b N := by
    simpa only [subst_equality,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE N
  exact e

def literalData (a b N : PTm n) : PTm n :=
  GaussianNameArithmetic.addData GaussianGammaDerivativeAtOne.negativeGammaData (partialSum a b N)

@[simp] theorem subst_literalData {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (literalData a b N) = literalData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [literalData]

theorem literal_rate (a b N : PTm n) (hs : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b)
    (hn : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianNamedInverseRate.independentRate GaussianGammaDigammaNative.nameF GaussianGammaDigammaSeries.nameF
      (GaussianGammaDigammaNative.data a b) (literalData a b N) a N := by
  have goal : Γ ⊢[PRAAx] literalData a b N ≐ GaussianGammaDigammaSeries.data a b N := by
    simpa only [literalData,GaussianGammaDigammaSeries.data,GaussianNameArithmetic.subst_addData,
      GaussianGammaDerivativeAtOne.subst_negativeGammaData,Syn.subst_var,Matrix.cons_val_zero] using
      Prf.eqCongr (GaussianNameArithmetic.addData GaussianGammaDerivativeAtOne.negativeGammaData (var 0) : PTm 1)
        (σ := ![partialSum a b N]) (σ' := ![partialValue a b N]) (fun i => by fin_cases i; exact literal_partial_sum a b N)
  let F := GaussianGammaDigammaNative.nameF
  let G := GaussianGammaDigammaSeries.nameF
  let x := GaussianGammaDigammaNative.data a b
  let y := GaussianGammaDigammaSeries.data a b N
  let z := literalData a b N
  have hZ : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN G z :=
    GaussianNameArithmetic.add_fast _ _ _ _ GaussianGammaDerivativeAtOne.negativeGamma_regular
      (GaussianGammaCanonicalExponent.constant_regular _)
  exact GaussianNamedRateTransport.transport F G F G x y x z a N hn
    (GaussianGammaDigammaSeries.original_rate a b N hs hn)
    (GaussianNameEquivalence.cross_refl _ _ (GaussianGammaDigammaNative.name_regular a b hs))
    (GaussianGammaInputProperness.code_data_cross G z y hZ (GaussianGammaDigammaSeries.name_regular a b N) goal)

theorem actual_original_literal_digamma_reciprocal_series_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianStirlingGammaLogarithm.source (var 0) (var 1) ⟶ le one (var 2) ⟶
      GaussianNamedInverseRate.independentRate GaussianGammaDigammaNative.nameF GaussianGammaDigammaSeries.nameF
        (GaussianGammaDigammaNative.data (var 0) (var 1)) (literalData (var 0) (var 1) (var 2)) (var 0) (var 2)) :=
  closeUniv 3 (.impI (.impI (literal_rate _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaSeriesTerms
