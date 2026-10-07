/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.AllocatedMixedFixedSupport
import OAI.Combinatorics.Progressions.Probability.AllocatedConditionalSampledError
import OAI.Combinatorics.Progressions.Sampling.AllocatedPhysicalGridMask
import OAI.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedGridMarginal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

noncomputable def allocatedFullGridSiteValues
    (z : AllocatedFrozenJetRows B U b S (rowTypes)) (s : Finset α) (a : gridAxes) : ℤ :=
  integerBooleanSitesFromRows (rowSets (ig a).1) (allocatedGridIntegerValues B U b S rowSets a (z a)) s

noncomputable def allocatedFullGridSiteApproximation
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : AllocatedFrozenJetRows B U b S (rowTypes)) : ℂ :=
  siteFamilyEval e (allocatedFullGridSiteValues B U b S rowSets z)
    (fun s a => (allocatedFullGridSiteValues B U b S rowSets z s a : ℝ) / axisN a)

noncomputable def allocatedFullGridNaturalVolume : ℝ :=
  ∏ a : gridAxes, (axisN a : ℝ) ^ (rowSets (ig a).1).card

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] [DecidableEq α] in
theorem allocatedFullGridNaturalVolume_pos : 0 < allocatedFullGridNaturalVolume B U b S rowSets :=
  Finset.prod_pos (fun a _ => pow_pos (Nat.cast_pos.mpr (allocatedGridNaturalScale_pos B U b hR S a)) _)

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem allocatedFullGridSiteApproximation_error
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {ε : ℝ}
    (he : ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → gridAxes → ℤ),
      (∀ a t, t ∉ rowSets (ig a).1 → booleanCoefficient (fun s => y s a) t = 0) →
      ‖(((∏ a : gridAxes, (axisN a : ℝ) ^ (rowSets (ig a).1).card) *
          (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell ig
            (fun a => rowSets (ig a).1) x (fun a t => booleanCoefficient (fun s => y s a) t)).toReal : ℝ) : ℂ) -
        siteFamilyEval e y (fun s a => (y s a : ℝ) / axisN a)‖ ≤ ε)
    (x : G → IntegerScalarCubeBox α S.value)
    (z : AllocatedFrozenJetRows B U b S (rowTypes)) :
    ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
        ((∏ a : gridAxes, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell
          a (z a)).toReal : ℝ) : ℂ) - allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ ε := by
  let y := allocatedFullGridSiteValues B U b S rowSets z
  have hc (a : gridAxes) (t : rowSets (ig a).1) :
      booleanCoefficient (fun s => y s a) t.val = allocatedGridIntegerValues B U b S rowSets a (z a) t :=
    integerBooleanSitesFromRows_coefficient_mem _ _ t
  have hy (a : gridAxes) (t : Finset α) (ht : t ∉ rowSets (ig a).1) :
      booleanCoefficient (fun s => y s a) t = 0 := integerBooleanSitesFromRows_coefficient_outside _ _ t ht
  have hmass : (allocatedSupportedPhysicalJointPMF B U b hR hσ S q r hcell ig
      (fun a => rowSets (ig a).1) x (fun a t => booleanCoefficient (fun s => y s a) t)).toReal =
      ∏ a : gridAxes, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell a (z a)).toReal := by
    rw [allocatedSupportedPhysicalGrid_joint_mass B U b hR hσ S q r hcell ig
      (fun a => rowSets (ig a).1) x (allocatedGridIntegerAxis_injective B U b S)
      (allocatedGridIntegerAxis_grid B U b S)]
    apply Finset.prod_congr rfl
    intro a _
    rw [allocatedSupportedGridJetPMF_integer B U b hR hσ S rowSets x q r hcell]
    apply congrArg (fun v : rowSets (ig a).1 → ℤ =>
      (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell
        (ig a).1 (ig a).2 (rowSets (ig a).1) x v).toReal)
    funext t
    exact hc a t
  have h := he x y hy
  rw [hmass, Complex.ofReal_mul] at h
  exact h

theorem exists_allocated_full_grid_site_approximation
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (rowTypes) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hq : 0 < q) (hqv : (q : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E) (hδE : δ⁻¹ ≤ Real.exp E)
    (hsize : (Fintype.card α + 1) * q ≤ S.value)
    (hgamma : ∀ a : gridAxes, principalProfileSize (R (ig a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a).1 (ig a).2)) ≤ 1)
    (hσ1 : ∀ a : gridAxes, σ (ig a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hB : ∀ a : gridAxes, max
      (positiveModerateSpectrumBlockCount (ig a).1.val (rowSets (ig a).1).card
        ((layerTailDegree m + 2) * (rowSets (ig a).1).card))
      (uniformSpectrumBlockCount (ig a).1.val (rowSets (ig a).1).card
        (((ig a).1.val + 1) * (rowSets (ig a).1).card)) ≤
      Fintype.card (B ⟨(ig a).1, Sum.inr (ig a).2⟩)) :
    let O := allocatedMixedJointSiteLog m D p v E
    ∃ e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α),
      (∀ a, (e a).Bounds (Real.exp O) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩
        (Real.exp (allocatedInactiveSupportLog D))) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (z : AllocatedFrozenJetRows B U b S (rowTypes)),
        ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
          ((∏ a : gridAxes, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell
            a (z a)).toReal : ℝ) : ℂ) - allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ δ := by
  obtain ⟨e, hb, he⟩ := exists_allocated_mixed_fixed_support_joint_site_expansion
    B U b hR hσ S rowSets q hq r hcell ig hD hα hP hp hv hPp hqv hδ hE hδE
    (allocatedGridIntegerAxis_injective B U b S) hsize hgamma (allocatedGridIntegerAxis_grid B U b S)
    hσ1 L hL hcP hsP (fun a => hrows (ig a).1) hB
  exact ⟨e, hb, allocatedFullGridSiteApproximation_error B U b hR hσ S rowSets q r hcell e he⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (rowSets : Fin m → Finset (Finset α))

omit [DecidableEq α] in
theorem allocatedFullGridNaturalVolume_le_exp
    (hR : ∀ j, 0 < R j) {P L D : ℝ}
    (hP : 0 ≤ P) (hL : 0 ≤ L) (_hD : 0 ≤ D)
    (hRP : ∀ j, R j ≤ Real.exp P) (hSL : (S.value : ℝ) ≤ Real.exp L)
    (hrows : ∀ j, ((rowSets j).card : ℝ) ≤ D) :
    allocatedFullGridNaturalVolume B U b S rowSets ≤
      Real.exp ((Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} : ℝ) *
        (D * (P + ((layerTailDegree m + 1 : ℕ) : ℝ) * L + 1))) := by
  let T := P + ((layerTailDegree m + 1 : ℕ) : ℝ) * L
  have hT : 0 ≤ T := add_nonneg hP (mul_nonneg (Nat.cast_nonneg _) hL)
  have hscale (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
      (allocatedGridNaturalScale B U b S a : ℝ) ≤ Real.exp (T + 1) := by
    let j := (allocatedGridIntegerAxis B U b S a).1
    let i := (allocatedGridIntegerAxis B U b S a).2
    have hbnd : (basisAxisScale (b j) i : ℝ) ≤ Real.exp (((layerTailDegree m + 1 : ℕ) : ℝ) * L) := by
      have hh := allocatedGridIntegerAxis_grid B U b S a
      change basisAxisScale (b j) i ≤ S.value ^ (layerTailDegree m + 1) at hh
      have hh' : (basisAxisScale (b j) i : ℝ) ≤ (S.value : ℝ) ^ (layerTailDegree m + 1) := by exact_mod_cast hh
      exact hh'.trans (by
        simpa only [← Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg _) hSL (layerTailDegree m + 1))
    have hγ : principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) ≤ Real.exp P := by
      apply le_trans _ (hRP j)
      unfold principalProfileSize
      apply div_le_self (hR j).le
      have hh := Nat.cast_nonneg (α := ℝ) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
      linarith
    have hp : 0 ≤ principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) *
        (basisAxisScale (b j) i : ℝ) :=
      mul_nonneg (principalProfileSize_pos (hR j) _).le (Nat.cast_nonneg _)
    have hc := (Nat.ceil_lt_add_one hp).le
    have hprod := mul_le_mul hγ hbnd (Nat.cast_nonneg _) (Real.exp_nonneg P)
    rw [← Real.exp_add] at hprod
    have hN : (allocatedGridNaturalScale B U b S a : ℝ) ≤ Real.exp T + 1 :=
      hc.trans (add_le_add hprod le_rfl)
    have h1 : 1 ≤ Real.exp T := Real.one_le_exp hT
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp T + 1 := hN
      _ ≤ Real.exp T * 2 := by linarith
      _ ≤ Real.exp T * Real.exp 1 := mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  unfold allocatedFullGridNaturalVolume
  calc
    _ ≤ ∏ a : {a // allocatedGridAxis (I := I) U b S.value a}, Real.exp (D * (T + 1)) := by
      apply Finset.prod_le_prod₀ (fun a _ => pow_nonneg (Nat.cast_nonneg _) _)
      intro a _
      apply (pow_le_pow_left₀ (Nat.cast_nonneg _) (hscale a) _).trans
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (hrows _) (by linarith)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]
      rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

def allocatedFullGridCoefficientLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 5 * D + 9

def allocatedFullGridWindowLog {A : Type*} [Semiring A] (D : A) : A :=
  D * (D * (allocatedFullGridCoefficientLog D + 4))

theorem allocatedFullGridCoefficientLog_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedFullGridCoefficientLog D := by unfold allocatedFullGridCoefficientLog; positivity

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

noncomputable def allocatedFullGridSiteWindow (D : ℝ) (a : gridAxes) :
    Finset (CoefficientJetAxisRow (rowTypes) a.val) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact naturalScaleIntegerWindow (rowSets j) (Real.exp (allocatedFullGridCoefficientLog D))
      (allocatedPrincipalGridScale (G := G) B U b (R := R) j i)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] [DecidableEq α] in
theorem allocatedFullGridSiteWindow_integer (D : ℝ) (a : gridAxes)
    (z : CoefficientJetAxisRow (rowTypes) a.val) :
    z ∈ allocatedFullGridSiteWindow B U b S rowSets D a ↔
      allocatedGridIntegerValues B U b S rowSets a z ∈ naturalScaleIntegerWindow
        (rowSets (ig a).1) (Real.exp (allocatedFullGridCoefficientLog D)) (axisN a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · rfl

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] [DecidableEq α] in
theorem allocatedFullGridSiteWindow_nonempty (D : ℝ) (a : gridAxes) :
    (allocatedFullGridSiteWindow B U b S rowSets D a).Nonempty := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · refine ⟨fun _ => 0, mem_naturalScaleIntegerWindow_of_bound _ _ _ ?_⟩
    intro t
    simp only [Int.cast_zero, abs_zero]
    positivity

variable {D : ℝ} (hd : AllocatedComparisonDimensions (G := G) B α (fun j : Fin m => (rowSets j : Type uα)) D)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [DecidableEq α] in
include hd in
theorem allocatedFullGridCoefficientLog_sites (j : Fin m) :
    (2 : ℝ) ^ (j.val + 1) * Real.exp (allocatedInactiveSupportLog D) ≤
      Real.exp (allocatedFullGridCoefficientLog D) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ) ^ (j.val + 1) ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (j.val + 1) (hd.layer_degree B j)
  have hh := (mul_le_mul_of_nonneg_right hp (Real.exp_pos (allocatedInactiveSupportLog D)).le).trans_eq
    (Real.exp_add _ _).symm
  exact hh.trans_eq (by unfold allocatedInactiveSupportLog allocatedFullGridCoefficientLog; congr 1; ring)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [DecidableEq α] in
include hd hR in
theorem allocatedFullGridSiteWindow_card (a : gridAxes) :
    ((allocatedFullGridSiteWindow B U b S rowSets D a).card : ℝ) ≤
      Real.exp (D * (allocatedFullGridCoefficientLog D + 4)) *
        (axisN a : ℝ) ^ (rowSets (ig a).1).card := by
  have hH := allocatedFullGridCoefficientLog_nonneg hd.nonneg
  have hbase := two_mul_add_three_exp_bound hH (le_refl (Real.exp (allocatedFullGridCoefficientLog D)))
  have hrow : ((rowSets (ig a).1).card : ℝ) ≤ D := by simpa only [Fintype.card_coe] using hd.rows (ig a).1
  have hpow := pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) (rowSets (ig a).1).card hrow
  have hraw : ((allocatedFullGridSiteWindow B U b S rowSets D a).card : ℝ) ≤
      (2 * Real.exp (allocatedFullGridCoefficientLog D) + 3) ^ (rowSets (ig a).1).card *
        (axisN a : ℝ) ^ (rowSets (ig a).1).card := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · dsimp only [allocatedFullGridSiteWindow, allocatedGridNaturalScale, allocatedGridIntegerAxis]
      convert naturalScaleIntegerWindow_card_le (rowSets j)
        (Real.exp_pos (allocatedFullGridCoefficientLog D)).le
        (allocatedPrincipalGridScale_pos_of_radius (G := G) B U b hR j i) using 1
      · congr 2
      · simp only [Fintype.card_coe]
  exact hraw.trans (mul_le_mul_of_nonneg_right hpow (by positivity))

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [DecidableEq α] in
include hd hR in
theorem allocatedFullGridSiteWindow_volume :
    (∏ a : gridAxes, ((allocatedFullGridSiteWindow B U b S rowSets D a).card : ℝ)) ≤
      Real.exp (allocatedFullGridWindowLog D) * allocatedFullGridNaturalVolume B U b S rowSets := by
  have hD := hd.nonneg
  have hH := allocatedFullGridCoefficientLog_nonneg hD
  have hcount : (Fintype.card gridAxes : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_le_of_injective ig (allocatedGridIntegerAxis_injective B U b S))).trans
      (allocatedIntegerAxes_card_le B rowSets hd)
  have hpow := pow_le_exp_mul_of_le_exp (Real.exp_pos (D * (allocatedFullGridCoefficientLog D + 4))).le
    (le_refl (Real.exp (D * (allocatedFullGridCoefficientLog D + 4)))) (by positivity)
    (Fintype.card gridAxes) hcount
  calc
    _ ≤ ∏ a : gridAxes, Real.exp (D * (allocatedFullGridCoefficientLog D + 4)) *
        (axisN a : ℝ) ^ (rowSets (ig a).1).card :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _) (fun a _ =>
        allocatedFullGridSiteWindow_card B U b hR S rowSets hd a)
    _ = Real.exp (D * (allocatedFullGridCoefficientLog D + 4)) ^ Fintype.card gridAxes *
        allocatedFullGridNaturalVolume B U b S rowSets := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, allocatedFullGridNaturalVolume]
    _ ≤ _ := mul_le_mul_of_nonneg_right hpow (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

include hd in
theorem allocatedFullGridPhysicalCoefficient_bound (j : Fin m) (i : Fin (n j))
    (hσ1 : σ j ≤ 1) (x : G → IntegerScalarCubeBox α S.value) (z : rowSets j → ℤ)
    (hmass : allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i (rowSets j) x z ≠ 0)
    (t : rowSets j) : |(z t : ℝ)| ≤ Real.exp (allocatedFullGridCoefficientLog D) *
      (allocatedPrincipalGridScale (G := G) B U b (R := R) j i : ℝ) := by
  let K : ℝ := (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
    ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) *
      (8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hrow : (1 : ℝ) ≤ (rowSets j).card := by
    exact_mod_cast (Finset.card_pos.mpr (show (rowSets j).Nonempty from ⟨t.val, t.property⟩))
  have hKshort : K ≤ allocatedInactiveShortRadius (G := G) B rowSets ⟨j, i⟩ := by
    change K ≤ (rowSets j).card * K
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrow hK
  have hD := hd.nonneg
  have hKbound : K ≤ Real.exp (allocatedFullGridCoefficientLog D) :=
    (hKshort.trans (allocatedInactiveShortRadius_exp_bound B rowSets hd ⟨j, i⟩)).trans
      (Real.exp_le_exp.mpr (by unfold allocatedFullGridCoefficientLog; linarith))
  have hb := allocatedPhysicalGridPMF_natural_support B U b hR hσ S q r hcell j i hσ1
    (rowSets j) x z hmass t
  have hn : (0 : ℝ) < allocatedPrincipalGridScale (G := G) B U b (R := R) j i :=
    Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)
  rw [abs_div, abs_of_pos hn] at hb
  exact ((div_le_iff₀ hn).mp hb).trans (mul_le_mul_of_nonneg_right hKbound hn.le)

include hd in
theorem allocatedFullGridSiteWindow_zero
    (hσ1 : ∀ a : gridAxes, σ (ig a).1 ≤ 1)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (he : ∀ a i s r v, Real.exp (allocatedInactiveSupportLog D) ≤ |v| → (e a).factor i s r v = 0)
    (x : G → IntegerScalarCubeBox α S.value) (z : AllocatedFrozenJetRows B U b S (rowTypes))
    (hz : ∃ a, z a ∉ allocatedFullGridSiteWindow B U b S rowSets D a) :
    (∏ a : gridAxes, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell a (z a)).toReal) = 0 ∧
      allocatedFullGridSiteApproximation B U b S rowSets e z = 0 := by
  obtain ⟨a, ha⟩ := hz
  constructor
  · apply Finset.prod_eq_zero (Finset.mem_univ a)
    by_contra hmass
    apply ha
    rw [allocatedFullGridSiteWindow_integer]
    apply mem_naturalScaleIntegerWindow_of_bound
    intro t
    rw [allocatedSupportedGridJetPMF_integer B U b hR hσ S rowSets x q r hcell] at hmass
    have hp : allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell
        (ig a).1 (ig a).2 (rowSets (ig a).1) x (allocatedGridIntegerValues B U b S rowSets a (z a)) ≠ 0 := by
      intro hzero
      exact hmass (by rw [hzero, ENNReal.toReal_zero])
    exact allocatedFullGridPhysicalCoefficient_bound B U b hR hσ S rowSets hd q r hcell
      (ig a).1 (ig a).2 (hσ1 a) x (allocatedGridIntegerValues B U b S rowSets a (z a)) hp t
  · rw [allocatedFullGridSiteApproximation, siteFamilyEval_eq]
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    exact reconstructedSiteEval_zero_off_window (rowSets (ig a).1) (e a)
      (allocatedGridNaturalScale_pos B U b hR S a) (hrows _) (Real.exp_pos _).le
      (allocatedFullGridCoefficientLog_sites B rowSets hd (ig a).1) (he a)
      (allocatedGridIntegerValues B U b S rowSets a (z a))
      (fun hm => ha ((allocatedFullGridSiteWindow_integer B U b S rowSets D a (z a)).mpr hm))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q r hcell grid
local notation "height" => (fun a : gridAxes => basisAxisScale (b (Sigma.fst (ig a))) (Sigma.snd (ig a)))

noncomputable def allocatedSupportedSlicedFullGridDensity (x : G → IntegerScalarCubeBox α S.value)
    (z : AllocatedFrozenJetRows B U b S rowTypes) : ℝ :=
  ∏ a : gridAxes, (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
    (ig a).1 (ig a).2 (rowSets (ig a).1) x (allocatedGridIntegerValues B U b S rowSets a (z a))).toReal

theorem allocatedSupportedSlicedFullGridDensity_mean (x : G → IntegerScalarCubeBox α S.value)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (z : AllocatedFrozenJetRows B U b S rowTypes) :
    (gridLaw).mean (fun u => allocatedGridJetDensity B U b hR hσ S x u v₀ rows z) =
      allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z := by
  have hm := allocatedSupportedSlicedPhysicalJointPMF_grid_mean B U b hR hσ S q r H step c hH hsubset hcell
    ig (fun a => rowSets (ig a).1) x (allocatedGridIntegerAxis_grid B U b S) v₀
    (fun a => allocatedGridIntegerValues B U b S rowSets a (z a))
  have hp := allocatedSupportedSlicedPhysicalGrid_joint_mass B U b hR hσ S q r H step c hH hsubset hcell
    ig (fun a => rowSets (ig a).1) x (allocatedGridIntegerAxis_injective B U b S)
    (allocatedGridIntegerAxis_grid B U b S) (fun a => allocatedGridIntegerValues B U b S rowSets a (z a))
  refine Eq.trans ?_ (hm.symm.trans hp)
  apply congrArg (gridLaw).mean
  funext u
  apply Finset.prod_congr rfl
  intro a _
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · rfl

noncomputable def allocatedSlicedGridPhysicalVolume : ℝ :=
  ∏ a : gridAxes, (height a : ℝ) ^ (rowSets (ig a).1).card

noncomputable def allocatedSlicedGridSiteApproximation
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : AllocatedFrozenJetRows B U b S rowTypes) : ℂ :=
  siteFamilyEval e (allocatedFullGridSiteValues B U b S rowSets z)
    (fun s a => (allocatedFullGridSiteValues B U b S rowSets z s a : ℝ) / height a)

theorem allocatedSlicedGridSiteApproximation_error
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hcap : ∀ a (x : G → IntegerScalarCubeBox α S.value) z,
      ‖(((height a : ℝ) ^ (rowSets (ig a).1).card *
        (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
          (ig a).1 (ig a).2 (rowSets (ig a).1) x z).toReal : ℝ) : ℂ)‖ ≤ C)
    (he : ∀ a (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
      (∀ t ∉ rowSets (ig a).1, booleanCoefficient y t = 0) →
      ‖(((height a : ℝ) ^ (rowSets (ig a).1).card *
        (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
          (ig a).1 (ig a).2 (rowSets (ig a).1) x (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) -
        (e a).integerEval (height a) y‖ ≤ uniformProductAccuracy (Fintype.card gridAxes) C δ)
    (x : G → IntegerScalarCubeBox α S.value) (z : AllocatedFrozenJetRows B U b S rowTypes) :
    ‖(allocatedSlicedGridPhysicalVolume B U b S rowSets : ℂ) *
        (allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z : ℂ) -
      allocatedSlicedGridSiteApproximation B U b S rowSets e z‖ ≤ δ := by
  let y := allocatedFullGridSiteValues B U b S rowSets z
  have hc (a : gridAxes) (t : rowSets (ig a).1) :
      booleanCoefficient (fun s => y s a) t.val = allocatedGridIntegerValues B U b S rowSets a (z a) t :=
    integerBooleanSitesFromRows_coefficient_mem _ _ t
  have hy (a : gridAxes) (t : Finset α) (ht : t ∉ rowSets (ig a).1) :
      booleanCoefficient (fun s => y s a) t = 0 := integerBooleanSitesFromRows_coefficient_outside _ _ t ht
  have h := allocatedSupportedSlicedJointGrid_site_approximation B U b hR hσ S q r H step c hH hsubset hcell
    ig (fun a => rowSets (ig a).1) (allocatedGridIntegerAxis_injective B U b S)
    (allocatedGridIntegerAxis_grid B U b S) height e hC hδ hcap he x y hy
  have hmass := allocatedSupportedSlicedPhysicalGrid_joint_mass B U b hR hσ S q r H step c hH hsubset hcell
    ig (fun a => rowSets (ig a).1) x (allocatedGridIntegerAxis_injective B U b S)
    (allocatedGridIntegerAxis_grid B U b S) (fun a t => booleanCoefficient (fun s => y s a) t)
  have heq : (∏ a : gridAxes, (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
        (ig a).1 (ig a).2 (rowSets (ig a).1) x (fun t => booleanCoefficient (fun s => y s a) t)).toReal) =
      allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z := by
    apply Finset.prod_congr rfl
    intro a _
    congr 2
    funext t
    exact hc a t
  rw [hmass, heq, Complex.ofReal_mul] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

noncomputable def allocatedFullGridSelectedApproximation
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : (a : {_a : gridAxes // True}) → CoefficientJetAxisRow (rowTypes) a.val.val) : ℂ :=
  allocatedFullGridSiteApproximation B U b S rowSets e (fun a => z ⟨a, True.intro⟩)

variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

variable (x : G → IntegerScalarCubeBox α S.value)

theorem allocatedFullGridSelected_mass_eq
    (z : (a : {_a : gridAxes // True}) → CoefficientJetAxisRow (rowTypes) a.val.val) :
    (∏ a : {_a : gridAxes // True}, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell
      a.val (z a)).toReal) =
    ∏ a : gridAxes, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell
      a (z ⟨a, True.intro⟩)).toReal := by
  apply Fintype.prod_of_injective (fun a : {_a : gridAxes // True} => a.val) Subtype.val_injective
  · intro a ha
    exact False.elim (ha ⟨⟨a, True.intro⟩, rfl⟩)
  · intro a
    rfl

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{uα,uα} (Finset α))

theorem allocatedFullGridSelected_error {ε : ℝ}
    (he : ∀ z : AllocatedFrozenJetRows B U b S (rowTypes),
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
        ((∏ a, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell a (z a)).toReal : ℝ) : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ ε)
    (z : (a : {_a : gridAxes // True}) → CoefficientJetAxisRow (rowTypes) a.val.val) :
    ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
      ((∏ a, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell a.val (z a)).toReal : ℝ) : ℂ) -
      allocatedFullGridSelectedApproximation B U b S rowSets e z‖ ≤ ε := by
  rw [allocatedFullGridSelected_mass_eq]
  exact he (fun a => z ⟨a, True.intro⟩)

theorem allocatedFullGridSelected_zero {D : ℝ}
    (hd : AllocatedComparisonDimensions (G := G) B α (fun j : Fin m => (rowSets j : Type uα)) D)
    (hσ1 : ∀ a : gridAxes, σ (ig a).1 ≤ 1)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (he : ∀ a i s r v, Real.exp (allocatedInactiveSupportLog D) ≤ |v| → (e a).factor i s r v = 0)
    (z : (a : {_a : gridAxes // True}) → CoefficientJetAxisRow (rowTypes) a.val.val)
    (hz : ∃ a, z a ∉ allocatedFullGridSiteWindow B U b S rowSets D a.val) :
    (∏ a, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q r hcell a.val (z a)).toReal) = 0 ∧
      allocatedFullGridSelectedApproximation B U b S rowSets e z = 0 := by
  rw [allocatedFullGridSelected_mass_eq]
  apply allocatedFullGridSiteWindow_zero B U b hR hσ S rowSets hd q r hcell hσ1 hrows e he x
  obtain ⟨a, ha⟩ := hz
  exact ⟨a.val, ha⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

noncomputable def allocatedFullGridPointTolerance (D δ : ℝ) : ℝ :=
  δ / Real.exp (allocatedFullGridWindowLog D)

theorem allocatedFullGridPointTolerance_pos {D δ : ℝ} (hδ : 0 < δ) :
    0 < allocatedFullGridPointTolerance D δ := div_pos hδ (Real.exp_pos _)

theorem allocatedFullGridPointTolerance_inv {D δ E : ℝ} (hδE : δ⁻¹ ≤ Real.exp E) :
    (allocatedFullGridPointTolerance D δ)⁻¹ ≤ Real.exp (E + allocatedFullGridWindowLog D) := by
  rw [allocatedFullGridPointTolerance, inv_div, div_eq_mul_inv]
  calc
    _ ≤ Real.exp (allocatedFullGridWindowLog D) * Real.exp E :=
      mul_le_mul_of_nonneg_left hδE (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, add_comm]

theorem allocatedFullGridWindowLog_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedFullGridWindowLog D := by
  have h := allocatedFullGridCoefficientLog_nonneg hD
  unfold allocatedFullGridWindowLog
  positivity

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [DecidableEq α] in
include hR in
theorem allocatedFullGridSiteWindow_error_budget {D δ : ℝ}
    (hd : AllocatedComparisonDimensions (G := G) B α (fun j : Fin m => (rowSets j : Type uα)) D)
    (hδ : 0 < δ) :
    (allocatedFullGridPointTolerance D δ / allocatedFullGridNaturalVolume B U b S rowSets) *
      (∏ a : gridAxes, ((allocatedFullGridSiteWindow B U b S rowSets D a).card : ℝ)) ≤ δ := by
  have hN := allocatedFullGridNaturalVolume_pos B U b hR S rowSets
  have he := allocatedFullGridPointTolerance_pos (D := D) hδ
  calc
    _ ≤ (allocatedFullGridPointTolerance D δ / allocatedFullGridNaturalVolume B U b S rowSets) *
        (Real.exp (allocatedFullGridWindowLog D) * allocatedFullGridNaturalVolume B U b S rowSets) :=
      mul_le_mul_of_nonneg_left (allocatedFullGridSiteWindow_volume B U b hR S rowSets hd)
        (div_nonneg he.le hN.le)
    _ = δ := by
      unfold allocatedFullGridPointTolerance
      field_simp [ne_of_gt hN]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (q : ℕ)

local notation "selected" => (fun _ : {a // allocatedGridAxis (I := I) U b S.value a} => True)
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))

noncomputable def allocatedFullGridSiteProfile
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
      {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (e : {a // allocatedGridAxis (I := I) U b S.value a} →
      ScalarSiteExpansion.{uα,uα} (Finset α)) (z : EuclideanJetLayers U O) : ℂ :=
  allocatedComplexGridMultiplier B U b S O hb o bW d
    (allocatedSelectedGridExtension B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell selected
      (allocatedFullGridSelectedApproximation B U b S rowSets e)
      (allocatedFullGridNaturalVolume B U b S rowSets)) z *
    (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f z : ℂ)

variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (e : {a // allocatedGridAxis (I := I) U b S.value a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))

theorem allocatedFullGridSiteProfile_measurable (hf : Measurable f) :
    Measurable (allocatedFullGridSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e) := by
  unfold allocatedFullGridSiteProfile
  apply Measurable.mul
  · apply allocatedComplexGridMultiplier_measurable
    exact allocatedSelectedGridExtension_measurable B U b hR hσ S x rows q
      (principalResidueLabel q y₀) hcell selected _ _
  · exact (allocatedWholeMaskedGridlessProfile_measurable B U b S x y₀ rows hb o bW d q f hf).complex_ofReal

theorem allocatedFullGridSiteProfile_error :
    (fun z => ((FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean
        (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
      allocatedFullGridSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e z) =
    allocatedSelectedConditionalError B U b hR hσ S x rows hb o bW d q y₀ hcell selected f
      (allocatedFullGridSelectedApproximation B U b S rowSets e)
      (allocatedFullGridNaturalVolume B U b S rowSets) := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridAxes" => {a // grid a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "volumeN" => allocatedFullGridNaturalVolume B U b S rowSets

noncomputable def allocatedFullGridRowsOfMixed
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (a : gridAxes) : CoefficientJetAxisRow O a.val := (split z).1 a

omit [Fintype α] [DecidableEq α] in
theorem allocatedFullGridRowsOfMixed_integer
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) (a : gridAxes) :
    allocatedGridIntegerValues B U b S rowSets a
        (allocatedFullGridRowsOfMixed B U b S rowSets z a) = (z (ig a).1).2 (ig a).2 := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · rfl

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ)

omit [∀ j, Fintype (E j)] in
theorem allocatedFullGridSiteValues_mixed (z : MixedCoveredJetSource I O E n d)
    (s : Finset α) (a : gridAxes) :
    allocatedFullGridSiteValues B U b S rowSets
        (allocatedFullGridRowsOfMixed B U b S rowSets z.1) s a =
      ((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a).1).2 (ig a).2 () := by
  rw [mixedCoveredRowsSiteValue_integer]
  unfold allocatedFullGridSiteValues
  rw [allocatedFullGridRowsOfMixed_integer]

omit [∀ j, Fintype (E j)] in
theorem allocatedFullGridSiteApproximation_mixed
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I O E n d) :
    allocatedFullGridSiteApproximation B U b S rowSets e
        (allocatedFullGridRowsOfMixed B U b S rowSets z.1) =
      siteFamilyEval e
        (fun s a => ((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a).1).2 (ig a).2 ())
        (fun s a => (((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a).1).2 (ig a).2 () : ℝ) /
          allocatedGridNaturalScale B U b S a) := by
  have hy : allocatedFullGridSiteValues B U b S rowSets
      (allocatedFullGridRowsOfMixed B U b S rowSets z.1) =
      fun s a => ((mixedCoveredRowsSiteValue rowSets d z s).1 (ig a).1).2 (ig a).2 () := by
    funext s a
    exact allocatedFullGridSiteValues_mixed B U b S rowSets d z s a
  unfold allocatedFullGridSiteApproximation
  rw [hy]

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable [NeZero d] (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell

noncomputable def allocatedFullGridSiteChartPrefactor (z : MixedCoveredJetSource I O E n d) : ℂ :=
  1 / (volumeN : ℂ) *
    (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) : ℂ)

theorem allocatedFullGridSiteProfile_mixed
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I O E n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d
      (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))) :
    allocatedFullGridSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e (chart z) =
      allocatedFullGridSiteChartPrefactor B U b S rowSets d x hb o bW q y₀ f z *
        allocatedFullGridSiteApproximation B U b S rowSets e
          (allocatedFullGridRowsOfMixed B U b S rowSets z.1) := by
  rw [allocatedFullGridSiteProfile, allocatedComplexGridMultiplier_apply B U b S O hb o bW d _ z hz]
  have hprod : (∏ a : {a : gridAxes // ¬True},
      (laws a.val ((split z.1).1 a.val)).toReal) = 1 := by
    apply Finset.prod_eq_one
    intro a _
    exact False.elim (a.property True.intro)
  unfold allocatedSelectedGridExtension selectedProductExtension allocatedFullGridSiteChartPrefactor
    allocatedFullGridRowsOfMixed allocatedFullGridSelectedApproximation
  rw [hprod]
  simp only [Complex.ofReal_one, mul_one]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridAxes" => {a // grid a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "split" => coefficientJetAxisSplit O I n grid

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (T : Fin m → ℝ)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "mask" => allocatedPhysicalGridMask B U b S O T hb o bW d

noncomputable def allocatedClippedFullGridSiteProfile
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) (y : EuclideanJetLayers U O) : ℂ :=
  mask y * allocatedFullGridSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e y

noncomputable def allocatedClippedFullGridPrefactor (z : MixedCoveredJetSource I O E n d) : ℂ :=
  mask (chart z) * allocatedFullGridSiteChartPrefactor B U b S rowSets d x hb o bW q y₀ f z

theorem allocatedClippedFullGridSiteProfile_mixed
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (z : MixedCoveredJetSource I O E n d) (hz : z ∈ region) :
    allocatedClippedFullGridSiteProfile B U b S rowSets d T hR hσ x hb o bW q y₀ hcell f e (chart z) =
      allocatedClippedFullGridPrefactor B U b S rowSets d T x hb o bW q y₀ f z *
        allocatedFullGridSiteApproximation B U b S rowSets e
          (allocatedFullGridRowsOfMixed B U b S rowSets z.1) := by
  rw [allocatedClippedFullGridSiteProfile, allocatedFullGridSiteProfile_mixed
    B U b S rowSets d hR hσ x hb o bW q y₀ hcell f e z hz]
  exact (mul_assoc _ _ _).symm

theorem allocatedClippedFullGridSiteProfile_measurable
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α)) (hf : Measurable f) :
    Measurable (allocatedClippedFullGridSiteProfile B U b S rowSets d T hR hσ x hb o bW q y₀ hcell f e) :=
  (allocatedPhysicalGridMask_measurable B U b S O T hb o bW d).mul
    (allocatedFullGridSiteProfile_measurable B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e hf)

omit [Fintype α] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedClippedFullGridPrefactor_support
    (z : MixedCoveredJetSource I O E n d) (hz : z ∈ region)
    (hne : allocatedClippedFullGridPrefactor B U b S rowSets d T x hb o bW q y₀ f z ≠ 0) :
    allocatedPhysicalGridCondition B U b S O T ((split z.1).1) ∧
      f (allocatedLongJetRealCoordinates B U b S ((split z.1).2)) ≠ 0 := by
  have hm : mask (chart z) ≠ 0 := (mul_ne_zero_iff.mp hne).1
  have hp : allocatedFullGridSiteChartPrefactor B U b S rowSets d x hb o bW q y₀ f z ≠ 0 :=
    (mul_ne_zero_iff.mp hne).2
  constructor
  · by_contra hc
    exact hm (by rw [allocatedPhysicalGridMask_apply B U b S O T hb o bW d z hz, ite_eq_right hc])
  · intro hf
    have hprofile : allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f (chart z) = 0 := by
      have hinj := mixedCoveredJetChart_injOn U o b hb bW d
        (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
        (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
      unfold allocatedWholeMaskedGridlessProfile allocatedGridlessCoveredProfile
      rw [restrictedChartDensity_apply _ _ _ _ hinj hz]
      simp only [allocatedLongProfileDensity, hf, mul_zero, zero_div]
    apply hp
    simp only [allocatedFullGridSiteChartPrefactor, hprofile, Complex.ofReal_zero, mul_zero]

theorem allocatedClippedFullGridSiteProfile_zero
    (e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α))
    (y : EuclideanJetLayers U O) (hy : y ∉ chart '' region) :
    allocatedClippedFullGridSiteProfile B U b S rowSets d T hR hσ x hb o bW q y₀ hcell f e y = 0 := by
  rw [allocatedClippedFullGridSiteProfile, allocatedPhysicalGridMask_zero B U b S O T hb o bW d y hy,
    zero_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "gridAxes" => {a // grid a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "split" => coefficientJetAxisSplit O I n grid

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (d : ℕ) [NeZero d] (T : Fin m → ℝ)
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d
  (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "mask" => allocatedPhysicalGridMask B U b S O T hb o bW d

noncomputable def allocatedClippedFullGridGlobalPrefactor (y : EuclideanJetLayers U O) : ℂ :=
  mask y * (1 / (allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
    (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f y : ℂ))

omit [Fintype α] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedClippedFullGridGlobalPrefactor_apply (z : MixedCoveredJetSource I O E n d) :
    allocatedClippedFullGridGlobalPrefactor B U b S rowSets d T x hb o bW q y₀ f (chart z) =
      allocatedClippedFullGridPrefactor B U b S rowSets d T x hb o bW q y₀ f z := rfl

omit [Fintype α] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedClippedFullGridGlobalPrefactor_zero (y : EuclideanJetLayers U O)
    (hy : y ∉ chart '' region) :
    allocatedClippedFullGridGlobalPrefactor B U b S rowSets d T x hb o bW q y₀ f y = 0 := by
  rw [allocatedClippedFullGridGlobalPrefactor, allocatedPhysicalGridMask_zero B U b S O T hb o bW d y hy,
    zero_mul]

omit [Fintype α] [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedClippedFullGridGlobalPrefactor_measurable (hf : Measurable f) :
    Measurable (allocatedClippedFullGridGlobalPrefactor B U b S rowSets d T x hb o bW q y₀ f) := by
  exact (allocatedPhysicalGridMask_measurable B U b S O T hb o bW d).mul
    (((allocatedWholeMaskedGridlessProfile_measurable B U b S x y₀ rows hb o bW d q f hf).complex_ofReal).const_mul _)

end Erdos3.VectorPolynomial

end

end OAI
