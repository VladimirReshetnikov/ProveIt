import OAI.Combinatorics.Progressions.Estimates.AllocatedMaskedFactorBounds
import OAI.Combinatorics.Progressions.Linear.AllocatedGoodKernelIdealFamily

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

def allocatedFiniteIdealProfileLog {A : Type*} [Semiring A] (D p : A) : A :=
  3 * D + (2 * D + 2) * p + 1

def allocatedFiniteIdealCoefficientLog {A : Type*} [Semiring A]
    (m : ℕ) (D p : A) : A :=
  (2 ^ (m + 1) : ℕ) * D * (4 * allocatedFiniteIdealProfileLog D p + 8) +
    allocatedFiniteIdealProfileLog D p

def allocatedFiniteIdealLipschitzLog {A : Type*} [Semiring A] (D p c : A) : A :=
  D + 6 * allocatedFiniteIdealProfileLog D p + c + 14

theorem idealSiteLogBudget_le_finite_profile {outputs dim : ℕ} {D p : ℝ}
    (hp : 0 ≤ p) (hout : (outputs : ℝ) ≤ D) (hdim : (dim : ℝ) ≤ D)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D) :
    idealSiteLogBudget outputs dim p ≤ allocatedFiniteIdealProfileLog D p := by
  have hm := mul_le_mul_of_nonneg_right hout hp
  dsimp only [idealSiteLogBudget, affineProfileLogBound, allocatedFiniteIdealProfileLog]
  nlinarith only [hout, hdim, hprofile, hm]

theorem allocatedFiniteIdeal_budget_nonneg (m : ℕ) {D p c : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hc : 0 ≤ c) :
    0 ≤ allocatedFiniteIdealProfileLog D p ∧
      0 ≤ allocatedFiniteIdealCoefficientLog m D p ∧
      0 ≤ allocatedFiniteIdealLipschitzLog D p c := by
  dsimp only [allocatedFiniteIdealProfileLog, allocatedFiniteIdealCoefficientLog,
    allocatedFiniteIdealLipschitzLog]
  refine ⟨?_, ?_, ?_⟩ <;> positivity

theorem allocatedFiniteIdeal_coefficient_log_le {m dim axes outputs : ℕ} {D p : ℝ}
    (hp : 0 ≤ p) (hD : 0 ≤ D) (hdim : dim ≤ m + 1) (hcube : (dim : ℝ) ≤ D)
    (haxes : (axes : ℝ) ≤ D) (hout : (outputs : ℝ) ≤ D)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D) :
    ((2 ^ dim * axes : ℕ) : ℝ) * (4 * idealSiteLogBudget outputs dim p + 8) +
        idealSiteLogBudget outputs dim p ≤ allocatedFiniteIdealCoefficientLog m D p := by
  have hQ := idealSiteLogBudget_le_finite_profile hp hout hcube hprofile
  have hQ0 := (idealSiteLogBudget_bounds outputs dim hp).1
  have hsites : ((2 ^ dim : ℕ) : ℝ) ≤ (2 ^ (m + 1) : ℕ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hdim
  have hprod : ((2 ^ dim * axes : ℕ) : ℝ) ≤ (2 ^ (m + 1) : ℕ) * D := by
    rw [Nat.cast_mul]
    exact mul_le_mul hsites haxes (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact add_le_add (mul_le_mul hprod (by linarith only [hQ])
    (by positivity) (by positivity)) hQ

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hR : ∀ j, 0 < R j)
variable {δ : ℝ≥0} {ε p M D : ℝ} (F : AllocatedFiniteIdealData (Fin dim) I n)
variable (hF : F.Bounds B U b S rowSets x y₀ q d period hb o bW hR δ ε p M)

local notation "axes" => LayerSamplerAxis I n
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin dim) // s ∈ rowSets j})
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

include hF in
theorem allocatedFiniteIdeal_coefficient_budget (hp : 0 ≤ p) (hD : 0 ≤ D)
    (hdim : dim ≤ m + 1) (hcube : (dim : ℝ) ≤ D)
    (haxes : (Fintype.card axes : ℝ) ≤ D)
    (hout : (Fintype.card (Σ a : axes, rowTypes a.1) : ℝ) ≤ D)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D) :
    (∑ i, ‖F.coefficient i‖) ≤ Real.exp (allocatedFiniteIdealCoefficientLog m D p) := by
  apply hF.2.2.1.trans
  apply Real.exp_le_exp.mpr
  simpa only [Fintype.card_finset, Fintype.card_fin] using
    allocatedFiniteIdeal_coefficient_log_le hp hD hdim hcube haxes hout hprofile

include hF in
theorem allocatedFiniteIdeal_buffered_lipschitz_budget (hp : 0 ≤ p) (hD : 0 ≤ D)
    (hcube : (dim : ℝ) ≤ D) (haxes : (Fintype.card axes : ℝ) ≤ D)
    (hout : (Fintype.card (Σ a : axes, rowTypes a.1) : ℝ) ≤ D)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D)
    (i : F.Term) (s : Finset (Fin dim)) :
    LipschitzWith
      ⟨Real.exp (allocatedFiniteIdealLipschitzLog D p (normalizedSiteCutoffBound : ℝ)), Real.exp_nonneg _⟩
      (bufferedCoordinateProjection (allocatedGridAxis (I := I) U b S.value)
        radius positiveRadius (F.factor i s)) := by
  have hQ := idealSiteLogBudget_le_finite_profile hp hout hcube hprofile
  have hQ0 := (allocatedFiniteIdeal_budget_nonneg m hD hp (le_refl (0 : ℝ))).1
  have hf := hF.2.2.2.1 i s
  have hLip := hF.2.2.2.2.1 i s
  have hbuf := bufferedCoordinateProjection_lipschitz_uniform
    (allocatedGridAxis (I := I) U b S.value) radius positiveRadius
    (allocatedProductIdealSiteRadius_one_le B rowSets) (F.factor i s) hLip hf
  apply hbuf.weaken
  apply NNReal.coe_le_coe.mp
  change (Real.exp ((Fintype.card axes : ℝ) + 6 * idealSiteLogBudget
      (Fintype.card (Σ a : axes, rowTypes a.1)) (Fintype.card (Fin dim)) p + 12) +
      (Fintype.card axes : ℝ) * normalizedSiteCutoffBound / (2 * (radius : ℝ))) +
      (Fintype.card axes : ℝ) * normalizedSiteCutoffBound ≤
    Real.exp (allocatedFiniteIdealLipschitzLog D p (normalizedSiteCutoffBound : ℝ))
  have hden : (1 : ℝ) ≤ 2 * (radius : ℝ) := by
    have hr : (1 : ℝ) ≤ radius := allocatedProductIdealSiteRadius_one_le B rowSets
    linarith only [hr]
  have hcut := div_le_self
    (mul_nonneg (Nat.cast_nonneg (Fintype.card axes)) normalizedSiteCutoffBound.coe_nonneg) hden
  let Q := allocatedFiniteIdealProfileLog D p
  let c : ℝ := normalizedSiteCutoffBound
  let A := D + 6 * Q + 12 + c
  have hc : 0 ≤ c := normalizedSiteCutoffBound.coe_nonneg
  have hraw : Real.exp (Fintype.card axes + 6 * idealSiteLogBudget
      (Fintype.card (Σ a : axes, rowTypes a.1)) (Fintype.card (Fin dim)) p + 12) ≤ Real.exp A := by
    apply Real.exp_le_exp.mpr
    simp only [Fintype.card_fin]
    dsimp only [A, Q]
    linarith only [haxes, hQ, hc]
  have hDc : (Fintype.card axes : ℝ) * c ≤ Real.exp A := by
    calc
      _ ≤ D * c := mul_le_mul_of_nonneg_right haxes hc
      _ ≤ Real.exp D * Real.exp c := mul_le_mul
        (by linarith [Real.add_one_le_exp D]) (by linarith [Real.add_one_le_exp c]) hc (Real.exp_pos _).le
      _ = Real.exp (D + c) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [A, Q]; linarith only [hQ0])
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ 3 * Real.exp A := by linarith only [hraw, hcut, hDc]
    _ ≤ Real.exp 2 * Real.exp A := mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [A, Q, c, allocatedFiniteIdealLipschitzLog]; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

def allocatedFiniteIdealMaskedLog {A : Type*} [Semiring A]
    (m : ℕ) (D p w eP : A) : A :=
  (2 * D ^ 2 * (2 ^ (m + 1) : ℕ)) * eP + (D * w + D ^ 3 * eP) +
    allocatedFiniteIdealCoefficientLog m D p

theorem allocatedFiniteIdeal_mask_cost {m dim : ℕ}
    (I : Fin m → Type*) [∀ j, Fintype (I j)] (n : Fin m → ℕ)
    (O E : Fin m → Type*) [∀ j, Fintype (O j)] [∀ j, Fintype (E j)]
    (period : ℕ) [NeZero period] {M D w eP : ℝ}
    (hD : 0 ≤ D) (hw : 0 ≤ w) (heP : 0 ≤ eP) (hM : 0 ≤ M)
    (hMw : M ≤ Real.exp w) (hperiod : (period : ℝ) ≤ Real.exp eP)
    (hm : (m : ℝ) ≤ D) (hdim : dim ≤ m + 1)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (hO : ∀ j, (Fintype.card (O j) : ℝ) ≤ D)
    (hE : ∀ j, (Fintype.card (E j) : ℝ) ≤ D) (hn : ∀ j, (n j : ℝ) ≤ D) :
    M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap O E period ≤
      Real.exp (D * w + D ^ 3 * eP) ∧
    (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ^
      Fintype.card (Finset (Fin dim)) ≤ Real.exp ((2 * D ^ 2 * (2 ^ (m + 1) : ℕ)) * eP) := by
  have hmask := pow_le_exp_mul_of_le_exp hM hMw hw _ haxes
  have hdeck := coefficientDeckPeriodCap_exp_bound O E period hD heP hm hO hE hperiod
  refine ⟨(mul_le_mul hmask hdeck (coefficientDeckPeriodCap_nonneg O E period)
    (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm, ?_⟩
  have hnSum : (∑ j, (n j : ℝ)) ≤ D ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin m, D := Finset.sum_le_sum (fun j _ => hn j)
      _ = (m : ℝ) * D := by simp
      _ ≤ D ^ 2 := by simpa only [pow_two] using mul_le_mul_of_nonneg_right hm hD
  have hESum : (∑ j, (Fintype.card (E j) : ℝ)) ≤ D ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin m, D := Finset.sum_le_sum (fun j _ => hE j)
      _ = (m : ℝ) * D := by simp
      _ ≤ D ^ 2 := by simpa only [pow_two] using mul_le_mul_of_nonneg_right hm hD
  have hcoordinates : (((∑ j, n j) + ∑ j, Fintype.card (E j) : ℕ) : ℝ) ≤ 2 * D ^ 2 := by
    push_cast
    linarith only [hnSum, hESum]
  have hsites : (Fintype.card (Finset (Fin dim)) : ℝ) ≤ (2 ^ (m + 1) : ℕ) := by
    simp only [Fintype.card_finset, Fintype.card_fin]
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hdim
  have hcard := mixedCoveredSiteResidueLabels_card_le_exp n E (Finset (Fin dim)) period hperiod
  simp only [Fintype.card_fun, Nat.cast_pow] at hcard
  apply hcard.trans
  apply Real.exp_le_exp.mpr
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hcoordinates hsites (Nat.cast_nonneg _) (by positivity)) heP

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (rowSets : Fin m → Finset (Finset (Fin dim)))
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hR : ∀ j, 0 < R j)
variable {δ : ℝ≥0} {ε p M D w eP : ℝ} (F : AllocatedFiniteIdealData (Fin dim) I n)
variable (hF : F.Bounds B U b S rowSets x y₀ q d period hb o bW hR δ ε p M)

local notation "axes" => LayerSamplerAxis I n
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin dim) // s ∈ rowSets j})

include hF in
theorem allocatedFiniteIdeal_masked_coefficient_budget
    (hp : 0 ≤ p) (hD : 0 ≤ D) (hw : 0 ≤ w) (heP : 0 ≤ eP)
    (hM : 0 ≤ M) (hMw : M ≤ Real.exp w) (hperiod : (period : ℝ) ≤ Real.exp eP)
    (hm : (m : ℝ) ≤ D) (hdim : dim ≤ m + 1) (hcube : (dim : ℝ) ≤ D)
    (haxes : (Fintype.card axes : ℝ) ≤ D)
    (hout : (Fintype.card (Σ a : axes, rowTypes a.1) : ℝ) ≤ D)
    (hrows : ∀ j, (Fintype.card (rowTypes j) : ℝ) ≤ D)
    (hE : ∀ j, (Fintype.card (E j) : ℝ) ≤ D) (hn : ∀ j, (n j : ℝ) ≤ D)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ D) :
    (∑ label : Finset (Fin dim) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
      ∑ i, ‖allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period
        F.coefficient label i‖) ≤
      ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ *
        Real.exp (allocatedFiniteIdealMaskedLog m D p w eP) := by
  obtain ⟨hmask, hlabels⟩ := allocatedFiniteIdeal_mask_cost I n rowTypes E period
    hD hw heP hM hMw hperiod hm hdim haxes hrows hE hn
  have hraw := allocatedFiniteIdeal_coefficient_log_le hp hD hdim hcube haxes hout hprofile
  have hrawExp : Real.exp
      (((Fintype.card (Finset (Fin dim)) * Fintype.card axes : ℕ) : ℝ) *
        (4 * idealSiteLogBudget (Fintype.card (Σ a : axes, rowTypes a.1))
          (Fintype.card (Fin dim)) p + 8) +
        idealSiteLogBudget (Fintype.card (Σ a : axes, rowTypes a.1)) (Fintype.card (Fin dim)) p) ≤
      Real.exp (allocatedFiniteIdealCoefficientLog m D p) := by
    simpa only [Fintype.card_finset, Fintype.card_fin] using Real.exp_le_exp.mpr hraw
  apply hF.2.2.2.2.2.2.1.trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤ (Real.exp ((2 * D ^ 2 * (2 ^ (m + 1) : ℕ)) * eP) *
        Real.exp (D * w + D ^ 3 * eP)) * Real.exp (allocatedFiniteIdealCoefficientLog m D p) :=
      mul_le_mul (mul_le_mul hlabels hmask
        (mul_nonneg (pow_nonneg hM _) (coefficientDeckPeriodCap_nonneg rowTypes E period))
        (Real.exp_pos _).le) hrawExp (Real.exp_pos _).le (by positivity)
    _ = _ := by simp only [← Real.exp_add, allocatedFiniteIdealMaskedLog]

end Erdos3.VectorPolynomial

end

end OAI
