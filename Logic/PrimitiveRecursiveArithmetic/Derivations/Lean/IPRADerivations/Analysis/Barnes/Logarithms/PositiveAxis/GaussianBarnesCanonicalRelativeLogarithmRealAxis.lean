import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalHeadRelativeRealAxis
import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.GaussianBarnesCanonicalPositiveLogarithmRealAxis
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalRelativeLogIncrement

/-! All observations of the original relative Barnes logarithm are real for real centers and steps. -/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeLogarithmRealAxis

open_ipra
open ComplexLogarithmRemainder (add im)
open GaussianBarnesCanonicalPositiveLogarithmRealAxis (real_axis)
open GaussianBarnesCanonicalRelativeLogIncrement (nameF data)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianRealNameExponentialInjectivity (axisSamples difference_real_samples)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingNames (constant_real add_real)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem samples_axis (z h R B : PTm n) (hb : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ZT.eq (im z) (ZT.ofNat zero)) (hh : Γ ⊢[PRAAx] ZT.eq (im h) (ZT.ofNat zero)) :
    Γ ⊢[PRAAx] axisSamples nameF (data z h R B) := by
  let w := add z h
  let N := initial R
  have hw : Γ ⊢[PRAAx] ZT.eq (im w) (ZT.ofNat zero) := by
    apply ZT.derive
    dsimp only [w]
    rw [GaussianRootAlgebra.im_add,ZT.toZ_eq hz,ZT.toZ_eq hh]
    simp
  have pf := difference_real_samples _ _ _ _
    (real_axis _ _ (GaussianBarnesCanonicalLogarithmRealPrefix.prefactor_real w B hb hw))
    (real_axis _ _ (GaussianBarnesCanonicalLogarithmRealPrefix.prefactor_real z B hb hz))
  let t := GaussianBarnesCanonicalCorrectionShift.body
  let a := @GaussianBarnesCanonicalCorrectionShift.parameters n
  let s := @GaussianBarnesCanonicalCorrectionShift.total n
  have cr := difference_real_samples _ _ _ _
    (real_axis _ _ (constant_real (s w B N) (GaussianRationalFiniteSum.sum_canonical t N (a w B))
      (GaussianBarnesCanonicalLogarithmRealPrefix.correction_axis w B N hb hw)))
    (real_axis _ _ (constant_real (s z B N) (GaussianRationalFiniteSum.sum_canonical t N (a z B))
      (GaussianBarnesCanonicalLogarithmRealPrefix.correction_axis z B N hb hz)))
  have hd := add_real _ _ _ _ (GaussianBarnesCanonicalHeadRelativeRealAxis.relative_real z h B N hb hz hh) cr
  have tl := difference_real_samples _ _ _ _
    (real_axis _ _ (GaussianBarnesCanonicalLogarithmRealTail.cofinal_real w R B hw))
    (real_axis _ _ (GaussianBarnesCanonicalLogarithmRealTail.cofinal_real z R B hz))
  exact real_axis _ _ (add_real _ _ _ _ (add_real _ _ _ _ pf hd) tl)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeLogarithmRealAxis
