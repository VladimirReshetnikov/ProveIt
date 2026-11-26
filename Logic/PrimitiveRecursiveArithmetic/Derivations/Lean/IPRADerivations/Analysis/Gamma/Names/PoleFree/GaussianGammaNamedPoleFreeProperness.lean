import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaNamedPoleFreeFrozen
import IPRADerivations.Analysis.Gamma.Names.PoleFree.GaussianGammaRadiusOverlap
import IPRADerivations.Analysis.Trigonometry.SineProducts.Bounds.GaussianSineProductReflectionLower
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# Extensionality of named pole-free Gamma

The disk bound supplies every pole inequality beyond the finite native
guard. Two input certificates therefore admit a common larger disk
and a common smaller pole separation. Changing a certificate alone
preserves the output because both programs freeze at the same late input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeProperness

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaEulerHeadLower (poleAt pole_at)
open GaussianGammaNamedPoleFree (source source_at nameF data clock name_regular)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawGaussian rawDen)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "nativeSource" => GaussianGammaReciprocalInverse.source

theorem every_pole_at (z R B E k : PTm n) (h : Γ ⊢[PRAAx] nativeSource z R B one E) :
    Γ ⊢[PRAAx] poleAt z B one E k := by
  have side : Γ ⊢[PRAAx] le (succ R) (two*R) :=
    le_congr ((add_comm one R).eqTrans (succ_eq_add_one R).eqSymm)
      (show Γ ⊢[PRAAx] (R+R) ≐ two*R by ipra_ring) (add_le_add_right R h.andE₁.andE₁)
  refine .orE (le_total k (two*R))
    (pole_at z B one E (two*R) k h.andE₂.andE₂.andE₂.wk Prf.hyp0) ?_
  exact GaussianSineProductReflectionLower.automatic_pole_at z R B one E k
    h.andE₁.andE₂.andE₂.wk h.andE₂.andE₂.andE₁.wk (le_trans side.wk Prf.hyp0)

private theorem weaken_pole_at (z B E D k : PTm n) (hED : Γ ⊢[PRAAx] le E D)
    (h : Γ ⊢[PRAAx] poleAt z B one E k) : Γ ⊢[PRAAx] poleAt z B one D k :=
  le_trans h (mul_le_mul_right _ (le_mul_mono hED hED))

theorem enlarge_native (z R S B E D : PTm n) (h : Γ ⊢[PRAAx] nativeSource z R B one E)
    (hRS : Γ ⊢[PRAAx] le R S) (hED : Γ ⊢[PRAAx] le E D) :
    Γ ⊢[PRAAx] nativeSource z S B one D := by
  have disk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (S*B) :=
    le_trans h.andE₁.andE₂.andE₂ (le_mul_mono (mul_le_mul_right B hRS) (mul_le_mul_right B hRS))
  refine .andI (.andI (le_trans h.andE₁.andE₁ hRS) (.andI h.andE₁.andE₂.andE₁ disk))
    (.andI (le_refl one) (.andI (le_trans h.andE₂.andE₂.andE₁ hED) (.allI (.impI ?_))))
  let sh (t : PTm n) := Syn.shift t
  let Δ := le (var 0) (Syn.shift (two*S)) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] nativeSource (sh z) (sh R) (sh B) one (sh E) := by
    simpa [Δ,sh,Fm.shift,Syn.shift,one] using h.shift.wk
  have he : Δ ⊢[PRAAx] le (sh E) (sh D) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hED.shift.wk
  simpa only [Δ,sh,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    weaken_pole_at (sh z) (sh B) (sh E) (sh D) (var 0) he
      (every_pole_at (sh z) (sh R) (sh B) (sh E) (var 0) hs)

theorem enlarge_source (f : PR 2) (x R S E D : PTm n) (hf : Γ ⊢[PRAAx] source f x R E)
    (hRS : Γ ⊢[PRAAx] le R S) (hED : Γ ⊢[PRAAx] le E D) :
    Γ ⊢[PRAAx] source f x S D := by
  refine .andI hf.andE₁ (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source f (sh x) (sh R) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianGammaNamedPoleFree.subst_source] using hf.shift
  have r : Δ ⊢[PRAAx] le (sh R) (sh S) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hRS.shift
  have e : Δ ⊢[PRAAx] le (sh E) (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hED.shift
  let q := ap2 f (var 0) (sh x)
  exact enlarge_native (rawGaussian q) (sh R) (sh S) (rawDen q) (sh E) (sh D)
    (source_at f (var 0) (sh x) (sh R) (sh E) h) r e

theorem certificate_rate (f : PR 2) (s x R S E D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R E) (hg : Γ ⊢[PRAAx] source f x S D) :
    Γ ⊢[PRAAx] independentRate (nameF f) (nameF f) (data x R E) (data x S D) two (unit s) := by
  let F := nameF f
  let u := data x R E
  let v := data x S D
  let r := clock s R E
  let t := clock s S D
  let k := r+t
  let z := GaussianGammaNamedPoleFree.encodedData f k x R E
  let w := GaussianGammaNamedPoleFree.encodedData f k x S D
  let q := ap2 f k x
  have left := GaussianGammaNamedPoleFreeFrozen.original_frozen_rate f s k x R E hf (le_add_right r t)
  have right := GaussianGammaNamedPoleFreeFrozen.original_frozen_rate f s k x S D hg (le_add_left t r)
  have agree : Γ ⊢[PRAAx] crossEquivalent gammaF gammaF z w :=
    GaussianGammaRadiusOverlap.original_Gamma_overlap (rawGaussian q) R S (rawDen q) one E one D
      (source_at f k x R E hf) (source_at f k x S D hg)
  have move := GaussianNamedRateTransport.transport F gammaF F gammaF v w v z one (unit s)
    (unit_positive s) right (cross_refl _ _ (name_regular f x S D hg)) agree
  have back := GaussianNamedRateComposition.symmetric F gammaF v z one (unit s) (unit_positive s) move
  exact GaussianNamedDifferenceRate.rate_parameters_congr F F u v (one+one) (unit s) two (unit s)
    (by ipra_ring) (.eqRefl _)
    (GaussianNamedRateComposition.same_denominator F gammaF F u z v one (unit s) one (unit_positive s) left back)

private theorem certificate_observation (f : PR 2) (p x R S E D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R E) (hg : Γ ⊢[PRAAx] source f x S D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x R E)) (ap2 (nameF f) p (data x S D))
      (num 4) (unit p) := by
  have hU := unit_positive (Γ := Γ) p
  have obs := diagonal_rate (nameF f) (nameF f) (data x R E) (data x S D) two (unit p) p hU
    (certificate_rate f p x R S E D hf hg)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) hU
    (le_of_eq_add (d := zero) (by ipra_ring)) obs

theorem certificate_independent (f : PR 2) (x R S E D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R E) (hg : Γ ⊢[PRAAx] source f x S D) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF f) (data x R E) (data x S D) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 4)
    (name_regular f x R E hf) (name_regular f x S D hg) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have a : Δ ⊢[PRAAx] source f (sh x) (sh R) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianGammaNamedPoleFree.subst_source] using hf.shift
  have b : Δ ⊢[PRAAx] source f (sh x) (sh S) (sh D) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianGammaNamedPoleFree.subst_source] using hg.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianGammaNamedPoleFree.subst_data,
    LeanProofs.IPRA.PTm.subst_num,sh,Syn.shift] using
    certificate_observation f (var 0) (sh x) (sh R) (sh S) (sh E) (sh D) a b

theorem proper (f g : PR 2) (x y R S E D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x R E) (hg : Γ ⊢[PRAAx] source g y S D)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x R E) (data y S D) := by
  let U := R+S
  let V := E+D
  have lf := enlarge_source f x R U E V hf (le_add_right R S) (le_add_right E D)
  have rg := enlarge_source g y S U D V hg (le_add_left S R) (le_add_left D E)
  have a := certificate_independent f x R U E V hf lf
  have b := GaussianGammaNamedPoleFree.proper f g x y U V lf rg he
  have c := certificate_independent g y U S V D rg hg
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b c)

theorem actual_named_pole_free_Gamma_extensional_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      ((source f (var 0) (var 2) (var 4) ⋏ source g (var 1) (var 3) (var 5)) ⟶
        crossEquivalent f g (var 0) (var 1) ⟶
        crossEquivalent (nameF f) (nameF g) (data (var 0) (var 2) (var 4)) (data (var 1) (var 3) (var 5))) :=
  closeUniv 6 (.impI (.impI (proper f g _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaNamedPoleFreeProperness
