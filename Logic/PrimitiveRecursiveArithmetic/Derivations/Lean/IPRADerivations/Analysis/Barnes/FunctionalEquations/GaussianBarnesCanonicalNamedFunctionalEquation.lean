import IPRADerivations.Analysis.Barnes.FunctionalEquations.GaussianBarnesCanonicalFunctionalEquation
import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamedFrozen
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianEulerNamedShiftInput
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaC7NamedFrozen

/-!
# The original cleared Barnes functional equation on regular Gaussian names

A common late observation of the unit-shifted input determines the
exact same rational chart for the Barnes and reciprocal-Gamma factors.
The original shift's input clock determines the corresponding unshifted
chart. Apply the rational recurrence and remove the three freeze errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFunctionalEquation

open_ipra
open GaussianBarnesCanonicalNamedDemand (source data native_source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerNamedShiftInput (shiftF shiftData sample_fraction decoded_shift clock_later)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaEulerHeadLower (translated)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_refl cross_symm)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedMultiplyRate (sampleBound leadingNumerator)
open GaussianNamedRateComposition (same_denominator symmetric)
open GaussianRationalDistanceOrder (distance_radius_mono norm_from_distance_same)
open GaussianRationalHorner (ofGaussian positive_product ofGaussian_represents)
open GaussianRationalL1 (rawDen rawGaussian)
open GaussianRationalMetric (bounded distanceBounded bounded_of_cleared)
open GaussianRationalReciprocal (bound_congr)
open GaussianRootApproximationWitness (pointBounds)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "VD" => GaussianBarnesCanonicalValue.data
local notation "C" => GaussianGammaC7Name.nameF
local notation "CD" => GaussianGammaC7Name.data
local notation "G" => GaussianBarnesCanonicalNamed.nameF
local notation "P" => GaussianGammaC7Named.nameF

abbrev resultF (f : PR 2) : PR 2 := multiplyF (G (shiftF f)) (P (shiftF f))

def resultData (f : PR 2) (x R : PTm n) : PTm n :=
  multiplyData (G (shiftF f)) (P (shiftF f)) (data (shiftData x) (R+one)) (data (shiftData x) (R+one))

@[simp] theorem subst_resultData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x R : PTm n) :
    Syn.subst σ (resultData f x R) = resultData f (Syn.subst σ x) (Syn.subst σ R) := by simp [resultData,one]

private theorem shifted_bound_at (f : PR 2) (k x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) : Γ ⊢[PRAAx]
    bounded (ap2 (shiftF f) k (shiftData x)) (R+one) one := by
  let q := ap2 f (GaussianEulerNamedShiftInput.clock k) x
  let B := rawDen q
  let z := rawGaussian q
  let w := translated z B one
  have hz := native_source f (GaussianEulerNamedShiftInput.clock k) x R h
  have hw := GaussianBarnesCanonicalShiftChart.translated_bound z R B hz.andE₂
  have bound := bounded_of_cleared (ofGaussian w B) w B (R+one) one hz.andE₁ (le_refl one)
    (ofGaussian_represents _ _ hz.andE₁) (le_congr (by ipra_ring) (by ipra_ring) hw)
  exact bound_congr (sample_fraction f k x).eqSymm (.eqRefl _) (.eqRefl _) bound

theorem shifted_source (f : PR 2) (x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] source (shiftF f) (shiftData x) (R+one) := by
  refine .andI (GaussianEulerNamedShiftInput.regular f x h.andE₁) (.allI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  simpa only [pointBounds,Syn.shift,sh,Δ,one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
    GaussianEulerNamedShiftInput.subst_shiftData,PTm.subst_add] using
      shifted_bound_at f (var 0) (sh x) (sh R) hs

private theorem frozen_cap_at (F H : PR 2) (x y s i : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (h : Γ ⊢[PRAAx] independentRate F H x y one (unit s)) :
    Γ ⊢[PRAAx] bounded (ap2 H i y) (U F x+num 3) one := by
  let D := unit s
  let I := unit i
  have hd := unit_positive (Γ := Γ) s
  have hi := unit_positive (Γ := Γ) i
  have close := diagonal_rate H F y x one D i hd (symmetric F H x y one D hd h)
  have clear : Γ ⊢[PRAAx] le ((one*I+two*D)*one) (num 3*(D*I)) := by
    ipra_le 𝔞 I*sl hd+2*𝔞 D*sl hi
  have small := distance_radius_mono _ _ _ _ (num 3) one (positive_product D I hd hi) (le_refl _) clear close
  exact bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (norm_from_distance_same (le_refl one) small
      (GaussianNameBounds.sample_bound F x i hf))

private theorem frozen_cap (F H : PR 2) (x y s : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x)
    (h : Γ ⊢[PRAAx] independentRate F H x y one (unit s)) :
    Γ ⊢[PRAAx] sampleBound H y (U F x+num 3) := by
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have r : Δ ⊢[PRAAx] pointCN F (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift
  have e : Δ ⊢[PRAAx] independentRate F H (sh x) (sh y) one (unit (sh s)) :=
    by simpa [Δ,sh,Fm.shift,Syn.shift,one] using h.shift
  simpa only [sampleBound,GaussianNameBounds.subst_U,PTm.subst_num,Syn.shift,sh,Δ,one,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using frozen_cap_at F H (sh x) (sh y) (sh s) (var 0) r e

private def capLeft (f : PR 2) (x R : PTm n) : PTm n := U (P (shiftF f)) (data (shiftData x) (R+one))
private def capRight (f : PR 2) (x R : PTm n) : PTm n := U (G (shiftF f)) (data (shiftData x) (R+one))+num 3

def cost (f : PR 2) (x R : PTm n) : PTm n := (capLeft f x R*one+capRight f x R*one)+one+two

@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x R : PTm n) :
    Syn.subst σ (cost f x R) = cost f (Syn.subst σ x) (Syn.subst σ R) := by simp [cost,capLeft,capRight,one,two]

theorem comparison_at (f : PR 2) (p x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (resultF f) p (resultData f x R)) (ap2 (G f) p (data x R)) (cost f x R) (unit p) := by
  let S := R+one
  let sf := shiftF f
  let sx := shiftData x
  let a := GaussianBarnesCanonicalNamed.clock p S
  let b := GaussianGammaC7Named.clock p S
  let c := GaussianBarnesCanonicalNamed.clock p R
  let k := (a+b)+c
  let l := GaussianEulerNamedShiftInput.clock k
  let q := ap2 f l x
  let z := rawGaussian q
  let B := rawDen q
  let w := translated z B one
  let r := ap2 sf k sx
  let v := rawGaussian r
  let D := rawDen r
  let hS : Γ ⊢[PRAAx] le one S := le_add_left one R
  have hz := native_source f l x R h
  have hw : Γ ⊢[PRAAx] GaussianBarnesCanonicalHead.source w S B :=
    .andI hz.andE₁ (GaussianBarnesCanonicalShiftChart.translated_bound z R B hz.andE₂)
  have hs := shifted_source f x R h
  have hv := native_source sf k sx S hs
  have haa : Γ ⊢[PRAAx] le a k := le_trans (le_add_right a b) (le_add_right (a+b) c)
  have hbb : Γ ⊢[PRAAx] le b k := le_trans (le_add_left b a) (le_add_right (a+b) c)
  have hcc : Γ ⊢[PRAAx] le c l := le_trans (le_add_left c (a+b)) (clock_later k)
  let X := data sx S
  let Y := data x R
  let t := VD v S D
  let u := CD v S D
  let T := multiplyData V C t u
  let W := VD z R B
  let M := capLeft f x R
  let N := capRight f x R
  let U' := unit p
  have up := unit_positive (Γ := Γ) p
  have gb := GaussianBarnesCanonicalNamed.name_regular sf sx S hs
  have gc := GaussianGammaC7Named.name_regular sf sx S (.andI hs hS)
  have rb := GaussianBarnesCanonicalValue.regular v S D hv
  have rc := GaussianGammaC7Name.name_regular v S D (.andI hS hv)
  have fr := GaussianBarnesCanonicalNamedFrozen.frozen_rate sf p k sx S hs haa
  have cr := GaussianGammaC7NamedFrozen.frozen_rate sf p k sx S (.andI hs hS) hbb
  have mul := GaussianNamedMultiplyRate.independent_rate (G sf) (P sf) V C X X t u one U' one U' M N up up
    gb gc rb rc (GaussianNameBounds.all_samples_bounded _ _ gc) (frozen_cap _ _ _ _ p gb fr) fr cr
  have prod := GaussianNamedRateRadius.weaken (resultF f) (multiplyF V C) (resultData f x R) T
    _ _ (M*one+N*one) U' (positive_product _ _ up up) up
      (le_of_eq_add (d := zero) (by unfold leadingNumerator; ipra_ring)) mul
  have chart : Γ ⊢[PRAAx] ofGaussian v D ≐ ofGaussian w B := decoded_shift f k x
  have sameB := GaussianBarnesCanonicalProperness.proper v w S S D B hv hw chart
  have sameC := GaussianGammaC7NamedFrozen.chart_cross v w S D B (.andI hS hv) (.andI hS hw) chart
  have aligned := multiply_cross V V C C t (VD w S B) u (CD w S B)
    rb (GaussianBarnesCanonicalValue.regular w S B hw) rc (GaussianGammaC7Name.name_regular w S B (.andI hS hw)) sameB sameC
  have finite := cross_trans _ _ _ _ _ _ aligned (GaussianBarnesCanonicalFunctionalEquation.functional_equation z R B hz)
  have regularLeft := multiply_fast (G sf) (P sf) X X gb gc
  have moved := GaussianNamedRateTransport.transport (resultF f) (multiplyF V C) (resultF f) V (resultData f x R) T
    (resultData f x R) W (M*one+N*one) U' up prod (cross_refl _ _ regularLeft)
    (cross_symm _ _ _ _ finite)
  have back := GaussianBarnesCanonicalNamedFrozen.frozen_rate f p l x R h hcc
  have merged := same_denominator (resultF f) V (G f) (resultData f x R) W Y (M*one+N*one) U' one up moved
    (symmetric (G f) V Y W one U' up back)
  let L := M*one+N*one+one
  have clear : Γ ⊢[PRAAx] le ((L*U'+two*U')*U') ((L+two)*(U'*U')) :=
    le_of_eq_add (d := zero) (by ipra_ring)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ up up) up clear
    (diagonal_rate (resultF f) (G f) (resultData f x R) Y (M*one+N*one+one) U' p up merged)

theorem functional_equation (f : PR 2) (x R : PTm n) (h : Γ ⊢[PRAAx] source f x R) :
    Γ ⊢[PRAAx] crossEquivalent (resultF f) (G f) (resultData f x R) (data x R) := by
  let sf := shiftF f
  let sx := shiftData x
  let S := R+one
  let X := data sx S
  have hs := shifted_source f x R h
  have b := GaussianBarnesCanonicalNamed.name_regular sf sx S hs
  have c := GaussianGammaC7Named.name_regular sf sx S (.andI hs (le_add_left one R))
  refine GaussianNameRingLaws.equivalent_of_envelope (resultF f) (G f) (resultData f x R) (data x R)
    (cost f x R) (multiply_fast (G sf) (P sf) X X b c) (GaussianBarnesCanonicalNamed.name_regular f x R h)
    (.allI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have e : Δ ⊢[PRAAx] source f (sh x) (sh R) := by simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,subst_resultData,subst_cost,
    GaussianBarnesCanonicalNamedDemand.subst_data,Syn.shift,sh,Δ] using comparison_at f (var 0) (sh x) (sh R) e

theorem actual_Barnes_named_functional_equation_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (let x := var 0
     let R := var 1
     source f x R ⟶ crossEquivalent (resultF f) (G f) (resultData f x R) (data x R)) :=
  closeUniv 2 (.impI (functional_equation f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalNamedFunctionalEquation
