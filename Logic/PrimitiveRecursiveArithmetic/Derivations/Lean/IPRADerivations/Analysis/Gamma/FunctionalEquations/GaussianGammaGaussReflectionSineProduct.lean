import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGammaGaussReflectionFamily
import IPRADerivations.Analysis.Trigonometry.GaussianCyclicSineProductName

/-!
# The sine factor of the Gauss reflection family is the original M1 product

An exact finite loop comparison identifies both PR3 row samplers.
Their independent normalizers are compared to the same cofinal
original sine observations, yielding the explicit M1 ratio for
the finite family occurring in the Gauss reflection proof.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionSineProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCyclicSineProductSquare (data)
open GaussianCyclicSineProductNormalization (clock_later)
open GaussianCyclicSineProductRatio (ratio original_product_error)
open GaussianCyclicOriginalSineProduct (originalF original_at budget)
open GaussianGammaGaussReflectionFamily (sineBody sine_at sine_rows numerator)
open GaussianNamedFiniteProduct (sample sample_zero sample_succ)
open GaussianNamedFiniteProductFamily (rowF row_at productData family_bounds family_regular)
open GaussianNamedFiniteProductName (rawF rawData raw_regular raw_at)
open GaussianFastValueCut (regular_at)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_symmetric distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianNamedSineFromExponential.sineF GaussianCyclicExponentialRoots.angleF

def familyRowF : PR 3 := rowF S sineBody
def radius (N x : PTm n) : PTm n := GaussianNamedFiniteProductFamily.radius S sineBody N (data N x)
def nameF : PR 2 := GaussianNamedFiniteProductName.nameF familyRowF
def nameData (N x : PTm n) : PTm n := productData S sineBody N (data N x)
def rate (N x : PTm n) : PTm n := two*GaussianNamedFiniteProductName.modulus N (radius N x) one+budget N

@[simp] theorem subst_radius {l : ℕ} (σ : Fin n → PTm l) (N x : PTm n) :
    Syn.subst σ (radius N x) = radius (Syn.subst σ N) (Syn.subst σ x) := by simp [radius]
@[simp] theorem subst_nameData {l : ℕ} (σ : Fin n → PTm l) (N x : PTm n) :
    Syn.subst σ (nameData N x) = nameData (Syn.subst σ N) (Syn.subst σ x) := by simp [nameData,productData,one]
@[simp] theorem subst_rate {l : ℕ} (σ : Fin n → PTm l) (N x : PTm n) :
    Syn.subst σ (rate N x) = rate (Syn.subst σ N) (Syn.subst σ x) := by simp [rate,one,two]

theorem native_row_at (p N x i : PTm n) :
    Γ ⊢[PRAAx] ap3 familyRowF p i (data N x) ≐ ap3 originalF p i (data N x) :=
  (row_at S sineBody p i (data N x)).eqTrans
    ((congrAp2 S (.eqRefl _) (sine_at N x i)).eqTrans (original_at p N x i).eqSymm)

private def sampleLaw (p N x i : PTm n) : Fm PTm n :=
  sample familyRowF p i (data N x) ≐ sample originalF p i (data N x)

@[simp] private theorem subst_sampleLaw {l : ℕ} (σ : Fin n → PTm l) (p N x i : PTm n) :
    (sampleLaw p N x i).subst σ = sampleLaw (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ i) := by
  simp [sampleLaw]

theorem native_product_at (p N x i : PTm n) :
    Γ ⊢[PRAAx] sample familyRowF p i (data N x) ≐ sample originalF p i (data N x) := by
  have all : Γ ⊢[PRAAx] .all (sampleLaw (Syn.shift p) (Syn.shift N) (Syn.shift x) (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_sampleLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (sample_zero _ _ _).eqTrans (sample_zero _ _ _).eqSymm
    · simp only [subst_sampleLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let P' := Syn.shift p
      let N' := Syn.shift N
      let X := Syn.shift x
      let j : PTm (n+1) := var 0
      let Δ := sampleLaw P' N' X j :: Γ.map Fm.shift
      have h : Δ ⊢[PRAAx] sampleLaw P' N' X j := Prf.hyp0
      exact (sample_succ _ _ _ _).eqTrans
        ((qmul_congr h (native_row_at P' N' X j)).eqTrans (sample_succ _ _ _ _).eqSymm)
  change Γ ⊢[PRAAx] sampleLaw p N x i
  simpa only [subst_sampleLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE i

theorem name_regular (N x : PTm n) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF (nameData N x) :=
  GaussianNamedFiniteProductFamily.family_product_regular S sineBody N (data N x) (sine_rows N x)

private theorem raw_ratio_at (p N x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (rawF familyRowF) p (rawData N (data N x))) (ratio N) (rate N x) (unit p) := by
  let t := GaussianCyclicSineProductNormalization.clock p (succ N)
  let q := rawData N (data N x)
  let A := rawF familyRowF
  let C := GaussianNamedFiniteProductName.modulus N (radius N x) one
  let U := unit p
  let V := unit t
  have hp := unit_positive (Γ := Γ) p
  have ht := unit_positive (Γ := Γ) t
  have hpv : Γ ⊢[PRAAx] le U V := unit_monotone (clock_later p (succ N))
  have hF := raw_regular familyRowF N (radius N x) one (data N x)
    (family_bounds S sineBody N (data N x) (sine_rows (Γ := Γ) N x))
    (family_regular S sineBody N (data N x) (sine_rows N x))
  have hC : Γ ⊢[PRAAx] distanceBounded (ap2 A p q) (ap2 A t q) (C*(U+V)) (U*V) :=
    regular_at A C q p t hF
  have cmp : Γ ⊢[PRAAx] le ((C*(U+V))*U) ((two*C)*(U*V)) :=
    le_congr (.eqRefl _) (by ipra_ring)
      (le_mul_mono (le_mul_mono (le_refl C) (add_le_add₂ hpv (le_refl V))) (le_refl U))
  have a := distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp ht) hp cmp hC
  have code_eq := (raw_at (Γ := Γ) familyRowF t N (data N x)).eqTrans (native_product_at t N x N)
  have cofinal := distance_congr code_eq.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_symmetric _ _ _ _ ht (original_product_error p N x))
  have b := distance_radius_mono _ _ _ _ _ _ ht hp (le_mul_mono (le_refl (budget N)) hpv) cofinal
  exact distance_triangle_same _ _ _ _ _ _ hp a b

theorem diagonal (p N x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (nameData N x)) (ap2 constantF p (ratio N)) (rate N x) (unit p) := by
  let t := GaussianNamedFiniteProductName.clock N (radius N x) one p
  have h := raw_ratio_at (Γ := Γ) t N x
  have c := distance_congr (raw_at familyRowF t N (data N x)) (.eqRefl _) (.eqRefl _) (.eqRefl _) h
  have a := distance_radius_mono _ _ _ _ _ _ (unit_positive t) (unit_positive p)
    (le_mul_mono (le_refl (rate N x)) (unit_monotone (GaussianNamedFiniteProductName.clock_later N (radius N x) one p))) c
  exact distance_congr (GaussianNamedFiniteProductName.name_at familyRowF p N (radius N x) one (data N x)).eqSymm
    (constant_at p (ratio N)).eqSymm (.eqRefl _) (.eqRefl _) a

theorem normalized_sine_product (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent nameF constantF (nameData N x) (ratio N) := by
  apply cross_of_diagonal_rate _ _ _ _ (rate N x) (name_regular N x) (constant_regular _)
  refine .allI ?_
  simpa [diagonalRate,Syn.shift,ratio] using diagonal (var 0) (Syn.shift N) (Syn.shift x)

theorem actual_Gauss_reflection_sine_family_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (crossEquivalent nameF constantF (nameData (var 1) (var 0)) (ratio (var 1))) :=
  closeUniv 2 (normalized_sine_product _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionSineProduct
