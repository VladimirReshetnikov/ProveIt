import IPRADerivations.Analysis.Barnes.FunctionalEquations.Duplication.GaussianBarnesCanonicalDuplicationGamma
import IPRADerivations.Analysis.Barnes.FunctionalEquations.Duplication.GaussianBarnesCanonicalDuplicationNormalizer

/-!
# The cleared half-period of the original Barnes duplication quotient

With `z=A/(2B)`, the original normalized four-factor product and
`G(2z)` advance by the same original Gamma sampler. The resulting
cross-product identity is the periodicity part of duplication.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDuplicationPeriodicity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHyperfactorial (barnesData barnes_regular)
open GaussianBarnesCanonicalHyperfactorialBarnesStep (denominatorF denominatorData denominator_step)
open GaussianBarnesCanonicalHyperfactorialPowerStep (gammaPowerF gammaPowerData gamma_power_regular)
open GaussianBarnesCanonicalHyperfactorialRecurrence (regroup)
open GaussianBarnesCanonicalDuplicationShift (half_step gammaPairF gammaPairData)
open GaussianBarnesCanonicalDuplicationGamma (duplication_multiplier canonical_gamma)
open GaussianBarnesCanonicalDuplicationNormalizer (factorF factorData factor_regular correction_step)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (multiply_associative multiply_commutative)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGammaLogarithm (source gammaData gamma_regular)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "G" => GaussianBarnesCanonicalValue.nameF
local notation "T" => GaussianGammaReciprocalInverse.gammaF
local notation "N" => GaussianBarnesCanonicalDuplicationNormalizer.nameF
local notation "Nd" => GaussianBarnesCanonicalDuplicationNormalizer.data
local notation "P" => GaussianBarnesCanonicalDuplicationShift.nameF
local notation "Pd" => GaussianBarnesCanonicalDuplicationShift.data
local notation "M" => multiplyF
local notation "Md" => multiplyData

abbrev nameF : PR 2 := M N P
def data (A B : PTm n) : PTm n := Md N P (Nd A B) (Pd A B)
def gammaFactorData (A B : PTm n) : PTm n := gammaData (two*A) (two*B)
abbrev stepF : PR 2 := M nameF T
def stepData (A B : PTm n) : PTm n := Md nameF T (data A B) (gammaFactorData A B)

private theorem gamma_factor_regular (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] pointCN T (gammaFactorData A B) :=
  gamma_regular _ _ (GaussianStirlingNativeDuplication.double_source A (two*B)
    (.andI h.andE₁ (positive_product two B (le_succ_self one) h.andE₂)))

theorem regular (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] pointCN nameF (data A B) :=
  multiply_fast _ _ _ _ (GaussianBarnesCanonicalDuplicationNormalizer.regular A B)
    (GaussianBarnesCanonicalDuplicationShift.regular A B hB)

theorem normalized_half_step (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent nameF stepF (data (A+B) B) (stepData A B) := by
  let a := Nd (A+B) B
  let b := Pd A B
  let c := factorData A B
  let d := gammaFactorData A B
  let w := gammaPairData A B
  let u := Md factorF T c d
  have ha := GaussianBarnesCanonicalDuplicationNormalizer.regular (Γ := Γ) (A+B) B
  have hb := GaussianBarnesCanonicalDuplicationShift.regular A B h.andE₂
  have hc := factor_regular A B h
  have hd := gamma_factor_regular A B h
  have hw := multiply_fast _ _ _ _
    (gamma_power_regular A (two*B) h.andE₁ (positive_product two B (le_succ_self one) h.andE₂))
    (gamma_power_regular (A+B) (two*B) (le_trans h.andE₁ (le_add_right _ _))
      (positive_product two B (le_succ_self one) h.andE₂))
  have hu := multiply_fast factorF T c d hc hd
  have left := multiply_cross N N P (M P gammaPairF) a a (Pd (A+B) B) (Md P gammaPairF b w)
    ha ha (GaussianBarnesCanonicalDuplicationShift.regular (A+B) B h.andE₂)
    (multiply_fast _ _ _ _ hb hw) (cross_refl _ _ ha) (half_step A B h.andE₁ h.andE₂)
  have replace := multiply_cross P P gammaPairF (M factorF T) b b w u hb hb hw hu
    (cross_refl _ _ hb) (duplication_multiplier A B h)
  have move := multiply_cross N N (M P gammaPairF) (M P (M factorF T)) a a (Md P gammaPairF b w) (Md P (M factorF T) b u)
    ha ha (multiply_fast _ _ _ _ hb hw) (multiply_fast _ _ _ _ hb hu) (cross_refl _ _ ha) replace
  have assoc := cross_symm _ _ _ _ (multiply_associative N P (M factorF T) a b u ha hb hu)
  have turn := regroup N P factorF T a b c d ha hb hc hd
  have hN := GaussianBarnesCanonicalDuplicationNormalizer.regular (Γ := Γ) A B
  have toOrdered := multiply_cross (M N factorF) N (M T P) (M P T) (Md N factorF a c) (Nd A B)
    (Md T P d b) (Md P T b d) (multiply_fast _ _ _ _ ha hc) hN
    (multiply_fast _ _ _ _ hd hb) (multiply_fast _ _ _ _ hb hd)
    (correction_step A B h) (multiply_commutative T P d b hd hb)
  have last := cross_symm _ _ _ _ (multiply_associative N P T (Nd A B) b d hN hb hd)
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ move
    (cross_trans _ _ _ _ _ _ assoc (cross_trans _ _ _ _ _ _ turn (cross_trans _ _ _ _ _ _ toOrdered last))))

private theorem numerator_half_step (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent G (M G T) (barnesData (A+B) B)
      (Md G T (barnesData A B) (gammaFactorData A B)) := by
  let x := barnesData A B
  let y := gammaPowerData A B
  let w := gammaFactorData A B
  have hG := barnes_regular A B h.andE₂
  have hY := gamma_power_regular A B h.andE₁ h.andE₂
  have e := cross_trans _ _ _ _ _ _ (canonical_gamma A B h)
    (cross_symm _ _ _ _ (GaussianStirlingNativeDuplication.gamma_rescale A B two h (le_succ_self one)))
  have move := multiply_cross G G gammaPowerF T x x y w hG hG hY (gamma_factor_regular A B h)
    (cross_refl _ _ hG) e
  exact cross_trans _ _ _ _ _ _ (denominator_step A B h.andE₁ h.andE₂) move

theorem periodicity_cleared (A B : PTm n) (h : Γ ⊢[PRAAx] source A B) :
    Γ ⊢[PRAAx] crossEquivalent (M G nameF) (M G nameF)
      (Md G nameF (barnesData (A+B) B) (data A B))
      (Md G nameF (barnesData A B) (data (A+B) B)) := by
  let a := barnesData A B
  let c := barnesData (A+B) B
  let b := data A B
  let d := data (A+B) B
  let t := gammaFactorData A B
  have ha := barnes_regular A B h.andE₂
  have hc := barnes_regular (A+B) B h.andE₂
  have hb := regular A B h.andE₂
  have hd := regular (A+B) B h.andE₂
  have ht := gamma_factor_regular A B h
  have left := multiply_cross G (M G T) nameF nameF c (Md G T a t) b b hc
    (multiply_fast _ _ _ _ ha ht) hb hb (numerator_half_step A B h) (cross_refl _ _ hb)
  have group := multiply_associative G T nameF a t b ha ht hb
  have permute := multiply_cross G G (M T nameF) stepF a a (Md T nameF t b) (stepData A B) ha ha
    (multiply_fast _ _ _ _ ht hb) (multiply_fast _ _ _ _ hb ht) (cross_refl _ _ ha)
    (multiply_commutative T nameF t b ht hb)
  have replace := multiply_cross G G stepF nameF a a (stepData A B) d ha ha
    (multiply_fast _ _ _ _ hb ht) hd (cross_refl _ _ ha)
    (cross_symm _ _ _ _ (normalized_half_step A B h))
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ group (cross_trans _ _ _ _ _ _ permute replace))

theorem actual_Barnes_duplication_half_period_cleared_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (let A := var 0; let B := var 1
       source A B ⟶ crossEquivalent (M G nameF) (M G nameF)
         (Md G nameF (barnesData (A+B) B) (data A B))
         (Md G nameF (barnesData A B) (data (A+B) B))) :=
  closeUniv 2 (.impI (periodicity_cleared _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDuplicationPeriodicity
