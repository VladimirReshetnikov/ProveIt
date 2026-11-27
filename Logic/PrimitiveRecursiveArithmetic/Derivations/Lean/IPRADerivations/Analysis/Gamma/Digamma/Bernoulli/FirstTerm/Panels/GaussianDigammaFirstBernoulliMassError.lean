import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.FirstTerm.Panels.GaussianDigammaFirstBernoulliHarmonic
import IPRADerivations.Analysis.Stirling.AllOrders.PowerIntegrals.GaussianStirlingAllOrderPowerIntegralPrefix
import IPRADerivations.Analysis.Stirling.AllOrders.FirstPanel.FiniteSums.GaussianStirlingAllOrderFirstPanelReadback

/-!
# Explicit local reciprocal mass errors for the digamma panel

The inverse square and cube masses approximate their primitive
differences, while the inverse first power agrees with the harmonic
interval up to the two exact boundary terms of the left mesh.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliMassError

open_ipra
open GaussianEuclideanDistanceName (fraction fraction_order)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingAllOrderDiscreteParts (sub)
open GaussianStirlingAllOrderPanelPartsOuter (data)
open GaussianStirlingAllOrderPanelPartsOuterFold (massBody massPrefix mass_at)
open GaussianStirlingAllOrderPanelPartsRecurrence (panelMass)
open GaussianStirlingAllOrderPowerIntegralMeshCells (primitive)
open GaussianStirlingAllOrderPowerIntegralPrefix (corrected_prefix_bounds)
open GaussianStirlingAllOrderReciprocalWeightError (power)
open GaussianStirlingAllOrderFirstPanelReadback (upper_of_add_order)
open RationalAlgebra (add_congr add_commutative swap_tail)
open RationalArgmin (rationalLE rationalLE_congr reflexive transitive)
open RationalArithmetic (add negative multiply_guard)
open RationalFiniteSum (sum sum_zero sum_succ term)
open RationalGaussianEmbedding (embed)
open RationalGaussianNameEmbedding (distance_from_radius)
open RationalHalfNinthProductLower (add_negative_cancel)
open RationalHarmonicInterval (interval common_canonical horizon)
open RationalReciprocalPowerTail (add_zero_right zero_fraction)
open RationalValueBounds (upper_of_order radius_of_upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def integral (e : ℕ) (U B : PTm n) : PTm n :=
  sub (primitive e U B) (primitive e (U+B) B)

private theorem mass_at_one (e : ℕ) (U B M : PTm n) : Γ ⊢[PRAAx] massPrefix e U B M one ≐ panelMass e U B M := by
  let f := massBody e
  let d := data U B M
  let P := panelMass e U B M
  let z : PTm n := fraction zero one
  have first : Γ ⊢[PRAAx] sum f one d ≐ add (sum f zero d) (term f zero d) := RationalFiniteSum.sum_succ f zero d
  have ea : Γ ⊢[PRAAx] U+B*zero ≐ U := by ipra_ring
  have ep : Γ ⊢[PRAAx] panelMass e (U+B*zero) B M ≐ P := by
    simpa only [GaussianStirlingAllOrderPanelPartsOuterFold.subst_panelMass,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using
      Prf.eqCongr (Γ := Γ) (panelMass e (var 0) (Syn.shift B) (Syn.shift M))
        (σ := Syn.inst (U+B*zero)) (σ' := Syn.inst U) (fun i => Fin.cases ea (fun j => .eqRefl (var j)) i)
  have row := (mass_at e U B M zero).eqTrans ep
  exact first.eqTrans ((add_congr ((RationalFiniteSum.sum_zero f d).eqTrans zero_fraction.eqSymm) row).eqTrans
    ((add_commutative z P).eqTrans (add_zero_right P (multiply_guard _ _))))

theorem power_mass_error (e : ℕ) (he : 2≤e) (U B M : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] distanceBounded (embed (panelMass e U B M)) (embed (integral e U B)) (power e B) M := by
  let P := panelMass e U B M
  let F := primitive e U B
  let G := primitive e (U+B) B
  let I := integral e U B
  let E := fraction (power e B) M
  have raw := corrected_prefix_bounds e he U B M one hU hM
  have terminal : Γ ⊢[PRAAx] primitive e (U+B*one) B ≐ G := by
    have eU : Γ ⊢[PRAAx] U+B*one ≐ U+B := by ipra_ring
    simpa only [GaussianStirlingAllOrderPowerIntegralMeshCells.subst_primitive,Syn.subst_var,Syn.subst_inst_shift,Syn.inst_zero] using
      Prf.eqCongr (Γ := Γ) (primitive e (var 0) (Syn.shift B)) (σ := Syn.inst (U+B*one)) (σ' := Syn.inst (U+B))
        (fun i => Fin.cases eU (fun j => .eqRefl (var j)) i)
  have read := add_congr (mass_at_one e U B M) terminal
  have lo : Γ ⊢[PRAAx] rationalLE F (add P G) := rationalLE_congr (.eqRefl _) read raw.andE₁
  have hi : Γ ⊢[PRAAx] rationalLE (add P G) (add F E) := rationalLE_congr read (.eqRefl _) raw.andE₂
  have reduced := add_negative_cancel (Γ := Γ) P G (multiply_guard _ _)
  have lower : Γ ⊢[PRAAx] rationalLE I P := rationalLE_congr (.eqRefl _) reduced
    (add_monotone _ _ (negative G) (negative G) lo (reflexive _))
  have upper : Γ ⊢[PRAAx] rationalLE P (add I E) := rationalLE_congr reduced (swap_tail F E (negative G))
    (add_monotone _ _ (negative G) (negative G) hi (reflexive _))
  exact distance_from_radius _ _ _ _ hM (radius_of_upper _ _ _ _
    (upper_of_add_order _ _ _ _ hM upper) (upper_of_order _ _ _ _ lower))

theorem harmonic_mass_error (U B Q : PTm n) (hU : Γ ⊢[PRAAx] le one U)
    (hB : Γ ⊢[PRAAx] le one B) (hQ : Γ ⊢[PRAAx] le one Q) :
    Γ ⊢[PRAAx] distanceBounded (embed (panelMass 1 U B (B*Q))) (embed (interval (U+B) U Q)) one Q := by
  let Y := interval (U+B) U Q
  let X := panelMass 1 U B (B*Q)
  let a := Q*U
  let b := Q*(U+B)
  let L := fraction one a
  let R := fraction one b
  let C := fraction one Q
  let z : PTm n := fraction zero one
  have hA : Γ ⊢[PRAAx] le one a := positive_product _ _ hQ hU
  have hab : Γ ⊢[PRAAx] le a b := by unfold a b; ipra_le 𝔞 Q*𝔞 B
  have hB' := le_trans hA hab
  have hQa : Γ ⊢[PRAAx] le Q a := by unfold a; ipra_le 𝔞 Q*sl hU
  have lastFirst : Γ ⊢[PRAAx] rationalLE R L :=
    fraction_order _ _ _ _ hB' hA (le_congr (by ipra_ring) (by ipra_ring) hab)
  have firstCap : Γ ⊢[PRAAx] rationalLE L C :=
    fraction_order _ _ _ _ hA hQ (le_congr (by ipra_ring) (by ipra_ring) hQa)
  have lastPositive : Γ ⊢[PRAAx] rationalLE z R := fraction_order _ _ _ _ (le_refl one) hB' (by ipra_le 1)
  have eq : Γ ⊢[PRAAx] add X R ≐ add L Y := GaussianDigammaFirstBernoulliHarmonic.exact_harmonic_mass U B Q hU hB hQ
  have upper : Γ ⊢[PRAAx] rationalLE X (add Y C) := by
    have lower := rationalLE_congr (add_zero_right X (multiply_guard _ _)) eq
      (add_monotone X X z R (reflexive _) lastPositive)
    exact transitive lower (rationalLE_congr (add_commutative Y L) (.eqRefl _)
      (add_monotone Y Y L C (reflexive _) firstCap))
  have lower : Γ ⊢[PRAAx] rationalLE Y X := by
    have edge := rationalLE_congr (.eqRefl _) ((add_commutative Y L).eqTrans eq.eqSymm)
      (add_monotone Y Y R L (reflexive _) lastFirst)
    exact rationalLE_congr (add_negative_cancel Y R (common_canonical (U+B) U Q (horizon (U+B) U Q)))
      (add_negative_cancel X R (multiply_guard _ _)) (add_monotone _ _ (negative R) (negative R) edge (reflexive _))
  exact distance_from_radius _ _ _ _ hQ (radius_of_upper _ _ _ _
    (upper_of_add_order _ _ _ _ hQ upper) (upper_of_order _ _ _ _ lower))

end LeanProofs.IPRA.Analysis.GaussianDigammaFirstBernoulliMassError
