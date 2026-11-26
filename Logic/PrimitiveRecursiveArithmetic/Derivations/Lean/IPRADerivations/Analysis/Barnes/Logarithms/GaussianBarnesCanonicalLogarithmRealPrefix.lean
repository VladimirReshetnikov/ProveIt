import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalSingleExponential
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalFiniteSumAxis
import IPRADerivations.Analysis.Stirling.GaussianStirlingNames

/-!
# Real observations of the Barnes prefactor exponent and finite correction

The original Stirling and Euler constants are real. At a real center,
the original polynomial and each finite correction row use only real
rational operations.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogarithmRealPrefix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (re im eval_re_code eval_im_code)
open GaussianBarnesCanonicalPrefactor (quadraticCoefficientF quadraticCoefficientData negativeHalf)
open GaussianBarnesCanonicalPrefactorExponentDerivative (exponentOf)
open GaussianGammaCanonicalExponent (constantF gammaF gamma_sample_at)
open GaussianNameRingLaws (oneF one_at)
open GaussianRationalFiniteSumAxis (rowAxes sum_axis)
open GaussianRationalHorner (canonical canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents
  positive_product qmul qmul_canonical represents_congr)
open GaussianRootAlgebra (equal_of_values)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingNames (constant_real multiply_real add_real)
open RationalGaussianEmbedding (axis axis_congr axis_multiply axis_negative axis_add embed native embed_axis)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem fraction_axis (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) : Γ ⊢[PRAAx] axis (ofGaussian z B) := by
  let a := ofGaussian z B
  have r := ofGaussian_represents z B hB
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (native (re z)) z := by
    apply equal_of_values
    · simp only [native,eval_re_code]
    · simpa only [native,eval_im_code] using (ZT.toZ_eq h).symm
  exact axis_congr (canonical_unique _ _ _ _ (RationalGaussianEmbedding.embed_canonical _) (ofGaussian_canonical z B hB)
    hB (represents_congr (.eqRefl _) e (.eqRefl _)
      (RationalGaussianEmbedding.embed_from_representation (fstT a) (re z) B r.andE₁)) r) (embed_axis _)

private theorem one_real : Γ ⊢[PRAAx] realSamples oneF (zero : PTm n) := by
  refine .allI ?_
  have e := one_at (Γ := Γ.map Fm.shift) (var 0) (zero : PTm (n+1))
  simpa only [Syn.shift,PTm.subst_zero] using
    (Prf.andI (GaussianRationalHorner.canonical_congr e GaussianRationalSyntheticDivision.qone_canonical)
      (axis_congr e.eqSymm RationalGaussianEmbedding.axis_one))

private theorem gamma_real : Γ ⊢[PRAAx] realSamples gammaF (zero : PTm n) := by
  refine .allI ?_
  have e := gamma_sample_at (Γ := Γ.map Fm.shift) (var 0)
  simpa only [Syn.shift,PTm.subst_zero] using
    (Prf.andI (GaussianRationalHorner.canonical_congr e (RationalGaussianEmbedding.embed_canonical _))
      (axis_congr e.eqSymm (embed_axis _)))

theorem exponent_real (a b : PTm n) (ha : Γ ⊢[PRAAx] canonical a) (hb : Γ ⊢[PRAAx] canonical b)
    (ar : Γ ⊢[PRAAx] axis a) (br : Γ ⊢[PRAAx] axis b) : Γ ⊢[PRAAx]
    realSamples GaussianBarnesCanonicalPrefactorInverse.exponentF (exponentOf a b) := by
  have coef : Γ ⊢[PRAAx] realSamples quadraticCoefficientF quadraticCoefficientData :=
    add_real oneF gammaF _ _ one_real gamma_real
  have A := constant_real a ha ar
  have L := multiply_real constantF GaussianStirlingConstant.nameF a _ A (GaussianStirlingConstant.name_real zero)
  have Q := multiply_real constantF quadraticCoefficientF b _ (constant_real b hb br) coef
  have P := add_real constantF GaussianBarnesCanonicalPrefactor.quadraticF _ _ A Q
  have half := constant_real (Γ := Γ) (negativeHalf : PTm n) (GaussianRationalMetric.qnegative_canonical _)
    (axis_negative _ (GaussianStirlingNames.fraction_axis one two (le_succ_self one)))
  exact add_real _ _ _ _ L (multiply_real constantF GaussianBarnesCanonicalPrefactor.polynomialF _ _ half P)

theorem correction_axis (z B N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) : Γ ⊢[PRAAx]
    axis (GaussianBarnesCanonicalCorrectionShift.total z B N) := by
  apply sum_axis _ _ _ (.allI ?_)
  let i : PTm (n+1) := var 0
  let x := Syn.shift z
  let d := Syn.shift B
  let E := two*(d*succ i)
  let Δ := Γ.map Fm.shift
  have dpos : Δ ⊢[PRAAx] le one d := by simpa [Fm.shift,Syn.shift,d,Δ,one] using hB.shift
  have xr : Δ ⊢[PRAAx] ZT.eq (im x) (ZT.ofNat zero) := by simpa [Fm.shift,Syn.shift,x,Δ] using hz.shift
  have epos := positive_product (Γ := Δ) two (d*succ i) (le_succ_self one)
    (positive_product _ _ dpos (zero_lt_succ i))
  have q := fraction_axis x d dpos xr
  have r := fraction_axis x E epos xr
  simpa only [Syn.shift,GaussianBarnesCanonicalCorrectionShift.subst_parameters,x,d,Δ] using
    axis_congr (GaussianBarnesCanonicalCorrectionShift.body_at (Γ := Δ) i x d).eqSymm
      (axis_add _ _ (axis_multiply _ _ q r) (axis_negative _ q))

theorem prefactor_real (z B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) : Γ ⊢[PRAAx]
    realSamples GaussianBarnesCanonicalPrefactorInverse.exponentF
      (GaussianBarnesCanonicalSingleExponential.prefactorExponentData z B) :=
  let q := fraction_axis z B hB hz
  exponent_real (ofGaussian z B) (qmul (ofGaussian z B) (ofGaussian z B))
    (ofGaussian_canonical z B hB) (qmul_canonical _ _) q (axis_multiply _ _ q q)

theorem prefix_real (z R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) : Γ ⊢[PRAAx]
    realSamples GaussianBarnesCanonicalSingleExponential.prefixF (GaussianBarnesCanonicalSingleExponential.prefixData z R B) := by
  let N := GaussianBarnesCanonicalLogSchedule.initial R
  let c := GaussianBarnesCanonicalCorrectionShift.total z B N
  have const := constant_real c
    (GaussianRationalFiniteSum.sum_canonical GaussianBarnesCanonicalCorrectionShift.body N
      (GaussianBarnesCanonicalCorrectionShift.parameters z B)) (correction_axis z B N hB hz)
  exact add_real _ _ _ _ (prefactor_real z B hB hz) const

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogarithmRealPrefix
