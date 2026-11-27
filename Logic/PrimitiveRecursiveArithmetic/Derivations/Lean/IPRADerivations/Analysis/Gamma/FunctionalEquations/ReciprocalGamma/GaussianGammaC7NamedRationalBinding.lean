import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaC7NamedFrozen
import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamed

/-!
# The named entire reciprocal Gamma extends the original rational evaluator

A constant input freezes to the same canonical rational at every
input clock. The original C7 evaluator is independent of that
rational's native chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaC7NamedRationalBinding

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianGammaC7Named (source nameF data clock sample_at proper)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianRationalDistanceOrder (distance_congr distance_at_earlier_precisions)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "disk" => GaussianGammaCanonicalExponent.source
local notation "V" => GaussianGammaC7Name.nameF
local notation "VD" => GaussianGammaC7Name.data

theorem constant_source (z R B : PTm n) (h : Γ ⊢[PRAAx] disk z R B) :
    Γ ⊢[PRAAx] source constantF (ofGaussian z B) R :=
  .andI (GaussianBarnesCanonicalNamed.constant_source z R B h.andE₂) h.andE₁

private theorem constant_observations (p q z R B : PTm n) (h : Γ ⊢[PRAAx] disk z R B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF constantF) p (data (ofGaussian z B) R)) (ap2 V q (VD z R B))
      (unit p+unit q) (unit p*unit q) := by
  let x := ofGaussian z B
  let k := clock p R
  let y := ap2 constantF k x
  have admitted := GaussianGammaC7Named.native_source constantF k x R (constant_source z R B h)
  have same : Γ ⊢[PRAAx] ofGaussian (rawGaussian y) (rawDen y) ≐ x :=
    (GaussianNameArithmetic.recode_congr (constant_at k x)).eqTrans
      (GaussianExponentialReference.recode_fixed x (ofGaussian_canonical z B h.andE₂.andE₁))
  have sameC := GaussianGammaC7NamedFrozen.chart_cross (rawGaussian y) z R (rawDen y) B admitted h same
  have qNear := cross_at _ _ _ _ (succ p) q sameC
  have widened := distance_at_earlier_precisions p q (succ p) q (le_succ_self p) (le_refl q) qNear
  exact distance_congr (sample_at constantF p x R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) widened

theorem constant_cross (z R B : PTm n) (h : Γ ⊢[PRAAx] disk z R B) :
    Γ ⊢[PRAAx] crossEquivalent (nameF constantF) V (data (ofGaussian z B) R) (VD z R B) := by
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] disk (sh z) (sh R) (sh B) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,Syn.shift,sh,Δ,GaussianBarnesCanonicalNamedDemand.subst_data,
    GaussianGammaC7Name.subst_data,GaussianRationalHorner.subst_ofGaussian] using
    constant_observations (var 1) (var 0) (sh z) (sh R) (sh B) hs

theorem bind (f : PR 2) (x z R B : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R) (hz : Γ ⊢[PRAAx] disk z R B)
    (he : Γ ⊢[PRAAx] crossEquivalent f constantF x (ofGaussian z B)) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) V (data x R) (VD z R B) :=
  cross_trans (nameF f) (nameF constantF) V (data x R) (data (ofGaussian z B) R) (VD z R B)
    (proper f constantF x (ofGaussian z B) R hf (constant_source z R B hz) he) (constant_cross z R B hz)

theorem actual_original_C7_named_rational_binding_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source f (var 0) (var 2) ⟶ disk (var 1) (var 2) (var 3) ⟶
        crossEquivalent f constantF (var 0) (ofGaussian (var 1) (var 3)) ⟶
        crossEquivalent (nameF f) V (data (var 0) (var 2)) (VD (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (bind f _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaC7NamedRationalBinding
