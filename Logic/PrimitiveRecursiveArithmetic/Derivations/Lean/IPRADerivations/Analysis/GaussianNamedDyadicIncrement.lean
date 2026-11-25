import IPRADerivations.Analysis.GaussianGammaUnitEulerDifference
import IPRADerivations.Analysis.GaussianRationalLowerBounds
import IPRADerivations.Analysis.GaussianStirlingNames

/-!
# A certified dyadic increment with a supplied exponent

The original constant name at (2^{-h}) has real samples and a reciprocal
certificate at the same index (h). Any positive demand bounded by (2^h)
is paid by this one named increment.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDyadicIncrement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode normSq normSq_one scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialSmallPerturbation (smallSamples)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (ofGaussian ofGaussian_represents)
open GaussianRationalReciprocal (bound_congr)
open GaussianRealNameExponentialInjectivity (axisSamples)
open RationalGaussianEmbedding (axis axis_congr)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (h : PTm n) : PTm n := ofGaussian oneCode (unit h)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (h : PTm n) :
    Syn.subst σ (data h) = data (Syn.subst σ h) := by
  simp [data]

theorem sample_at (h p : PTm n) : Γ ⊢[PRAAx] ap2 constantF p (data h) ≐ data h :=
  constant_at p (data h)

theorem reciprocal_input (h : PTm n) :
    Γ ⊢[PRAAx] GaussianNameReciprocal.input constantF h (data h) := by
  let D := unit h
  let q := data h
  have hd := unit_positive (Γ := Γ) h
  have square : Γ ⊢[PRAAx] (D*D)*normSq oneCode ≐ D*D :=
    (congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring)
  have lower : Γ ⊢[PRAAx] GaussianNameReciprocal.lower q D :=
    GaussianRationalLowerBounds.lower_from_representation q oneCode D one D hd hd
      (ofGaussian_represents _ _ hd) (le_congr (by ipra_ring) square.eqSymm (le_refl (D*D)))
  exact .andI (constant_regular q)
    (GaussianNameReciprocal.lower_congr (sample_at h (GaussianNameReciprocal.anchor h)).eqSymm (.eqRefl _) lower)

theorem data_axis (h : PTm n) : Γ ⊢[PRAAx] axis (data h) := by
  have hd := unit_positive (Γ := Γ) h
  have scalar : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (scale one oneCode) oneCode := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring
  exact axis_congr (GaussianGammaFiniteValueProperness.fraction_equal _ _ (unit h) hd scalar)
    (GaussianStirlingNames.fraction_axis one (unit h) hd)

theorem axis_samples (h : PTm n) : Γ ⊢[PRAAx] axisSamples constantF (data h) := by
  let Δ := Γ.map Fm.shift
  refine .allI ?_
  simpa only [axisSamples,Syn.shift,subst_data,Δ] using
    axis_congr (sample_at (Γ := Δ) (Syn.shift h) (var 0)).eqSymm (data_axis (Γ := Δ) (Syn.shift h))

theorem small_samples (h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hBD : Γ ⊢[PRAAx] le B (unit h)) :
    Γ ⊢[PRAAx] smallSamples constantF (data h) one B := by
  let Δ := Γ.map Fm.shift
  let sh (v : PTm n) := Syn.shift v
  have hb : Δ ⊢[PRAAx] le one (sh B) := by
    simpa only [Δ,Fm.shift,Syn.shift,sh,subst_le,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using hB.shift
  have hm : Δ ⊢[PRAAx] le (sh B) (unit (sh h)) := by
    simpa only [Δ,Fm.shift,Syn.shift,sh,subst_le,GaussianCoefficientNameBounds.subst_unit] using hBD.shift
  have bound := GaussianGammaUnitEulerDifference.increment_bound (sh B) (unit (sh h)) hb hm
  have read := sample_at (Γ := Δ) (sh h) (var 0)
  refine .allI ?_
  simpa only [smallSamples,Syn.shift,subst_data,sh,Δ,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    bound_congr read.eqSymm (.eqRefl _) (.eqRefl _) bound

theorem source (h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hBD : Γ ⊢[PRAAx] le B (unit h)) :
    Γ ⊢[PRAAx] axisSamples constantF (data h) ⋏
      (GaussianNameReciprocal.input constantF h (data h) ⋏ smallSamples constantF (data h) one B) :=
  .andI (axis_samples h) (.andI (reciprocal_input h) (small_samples h B hB hBD))

theorem actual_named_dyadic_increment_demand_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((le one (var 1) ⋏ le (var 1) (unit (var 0))) ⟶
        (axisSamples constantF (data (var 0)) ⋏
          (GaussianNameReciprocal.input constantF (var 0) (data (var 0)) ⋏
            smallSamples constantF (data (var 0)) one (var 1)))) :=
  closeUniv 2 (.impI (source _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedDyadicIncrement
