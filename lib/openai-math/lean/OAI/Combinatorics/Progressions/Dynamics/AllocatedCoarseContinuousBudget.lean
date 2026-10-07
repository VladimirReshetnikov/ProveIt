import OAI.Combinatorics.Progressions.Estimates.AllocatedCoarseGenuineSource
import OAI.Combinatorics.Progressions.Estimates.AllocatedGenuineNativePartner

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

noncomputable def allocatedConstructedContinuousLog {A : Type*} [Semiring A]
    (m dim : ℕ) (D pI p0 E0 O Pτ c : A) : A :=
  (D + 1) + p0 + (3 * (coarseSpatialReciprocalLog (allocatedEarlyCoarseInput m dim (p0 + E0)) + 4) + 6) +
    (Pτ + 8) + (D + O + (D + 8) + allocatedFiniteIdealLipschitzLog D pI c + 1) + 1

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value) (N : X → ℕ) {τ : ℝ} (base : X → ℤ)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
variable (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d period : ℕ) [NeZero d] [NeZero period]
variable (hR : ∀ j, 0 < R j)
variable {M : ℕ} (selection : Fin dim ↪ G)
variable (F : AllocatedFiniteIdealData (Fin dim) I n)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin dim) // s ∈ rowSets j})
local notation "gridAxes" => {i // allocatedGridAxis (I := I) U b S.value i}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

theorem allocatedConstructedContinuousSiteFactor_pre_bounds
    {δ : ℝ≥0} {ε pI p0 E0 O Pτ D : ℝ}
    (hF : F.Bounds B U b S rowSets x (coverWitness r).representative
      (residueRefinedPeriod modulus q) d period hb o bW hR δ ε pI (layerKernelIndexBound m M))
    {T C A H : gridAxes → ℝ}
    (hgrid : ∀ i, ((coverWitness r).expansion i).Bounds (T i) (C i) (A i)
      ⟨Real.exp O, Real.exp_nonneg _⟩ (H i))
    (hpI : 0 ≤ pI) (hp0 : 0 ≤ p0) (hE0 : 0 ≤ E0) (hO : 0 ≤ O) (hPτ : 0 ≤ Pτ)
    (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hG : (Fintype.card G : ℝ) ≤ p0) (hX : (Fintype.card X : ℝ) ≤ p0)
    (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp p0) (hmod : modulus ≤ M ^ (m + 1))
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ) (hτexp : 1 / τ ≤ Real.exp Pτ) :
    let meshR := allocatedEarlyRecenteredMesh X selection M modulus p0 E0
    let mesh : ℝ≥0 := ⟨meshR, (allocatedEarlyRecenteredMesh_partition_budget m X selection
      hp0 hE0 hG hX hM hMP hmod).1.le⟩
    ∀ (spatial : X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
      (kg : ∀ i, ((coverWitness r).expansion i).Term) (i : F.Term) (s : Finset (Fin dim))
      (gridLabel : ∀ j, ZMod (((coverWitness r).expansion j).period (kg j))),
      (∀ v, ‖allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S X modulus q wholeReference
        coverWitness x N mesh base r a spatial kg (F.factor i s) s gridLabel v‖ ≤ 1) ∧
      LipschitzWith
        ⟨Real.exp (allocatedConstructedContinuousLog m dim D pI p0 E0 O Pτ (normalizedSiteCutoffBound : ℝ)),
          Real.exp_nonneg _⟩
        (allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S X modulus q wholeReference
          coverWitness x N mesh base r a spatial kg (F.factor i s) s gridLabel) := by
  intro meshR mesh spatial kg i s gridLabel
  rcases hgeom with ⟨hD, _, _, hcube, haxes, _, _, hout, _, hcoeff, hprofile⟩
  have hdim : (dim : ℝ) ≤ D := by simpa only [Fintype.card_fin] using hcube
  have hgridAxes : (Fintype.card gridAxes : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans haxes
  let Q : ℝ≥0 := ⟨8 * (D + 1), mul_nonneg (by norm_num) (by linarith only [hD])⟩
  have hQ (j : gridAxes) :
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B (ig j).1 (ig j).2) : ℝ) + 1) ≤ Q := by
    have hc : ((layerIntegerPrincipalSlots (G := G) B (ig j).1 (ig j).2).card : ℝ) ≤ D :=
      (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (hcoeff (ig j).1)
    change 8 * (_ + 1) ≤ 8 * (D + 1)
    linarith only [hc]
  have hQexp : (Q : ℝ) ≤ Real.exp (D + 8) := by
    change 8 * (D + 1) ≤ _
    calc
      _ ≤ 8 * Real.exp D := mul_le_mul_of_nonneg_left (Real.add_one_le_exp D) (by norm_num)
      _ ≤ Real.exp 8 * Real.exp D := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  let eI := allocatedFiniteIdealLipschitzLog D pI (normalizedSiteCutoffBound : ℝ)
  have heI : 0 ≤ eI := (allocatedFiniteIdeal_budget_nonneg m hD hpI normalizedSiteCutoffBound.coe_nonneg).2.2
  have hI : LipschitzWith ⟨Real.exp eI, Real.exp_nonneg _⟩
      (bufferedCoordinateProjection (allocatedGridAxis (I := I) U b S.value)
        radius positiveRadius (F.factor i s)) := by
    exact allocatedFiniteIdeal_buffered_lipschitz_budget B U b S rowSets x (coverWitness r).representative
      (residueRefinedPeriod modulus q) d period hb o bW hR F hF hpI hD hdim haxes
      (by simpa only [← Nat.card_eq_fintype_card] using hout) hprofile i s
  have hearly := allocatedEarlyRecenteredMesh_partition_budget m X selection hp0 hE0 hG hX hM hMP hmod
  have hinput := (allocatedEarlyCoarseInput_bounds m dim (add_nonneg hp0 hE0)).1
  have hreciprocal := (coarseSpatialLogs_nonneg hinput).1
  let Pmesh := coarseSpatialReciprocalLog (allocatedEarlyCoarseInput m dim (p0 + E0)) + 4
  have hPmesh : 0 ≤ Pmesh := by dsimp [Pmesh]; linarith only [hreciprocal]
  have hbox : (4 : ℝ) ≤ Real.exp Pmesh := by
    apply (show (4 : ℝ) ≤ Real.exp 4 by linarith [Real.add_one_le_exp (4 : ℝ)]).trans
    exact Real.exp_le_exp.mpr (by dsimp [Pmesh]; linarith only [hreciprocal])
  have hmeshValue : (mesh : ℝ) = meshR := rfl
  have hinv : 1 / (mesh : ℝ) ≤ Real.exp Pmesh := by
    rw [hmeshValue, one_div]
    apply hearly.2.2.1.trans
    exact Real.exp_le_exp.mpr (by dsimp [Pmesh]; linarith)
  have hXexp : (Fintype.card X : ℝ) ≤ Real.exp p0 :=
    hX.trans (by linarith [Real.add_one_le_exp p0])
  have hSexp : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ Real.exp (D + 1) := by
    have hc : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ D + 1 := by
      simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
      linarith only [hdim]
    exact hc.trans (by linarith [Real.add_one_le_exp (D + 1)])
  have hresult := allocatedRecenteredContinuousSiteFactor_pre_bounds (τ := τ)
    B U b S X modulus q wholeReference coverWitness x N mesh base r a spatial kg (F.factor i s) s gridLabel
    hR hgrid Q hQ (hF.2.2.2.1 i s) hI hearly.1 hq hN hτ
    hD hO (by linarith only [hD] : 0 ≤ D + 8) heI hPmesh hp0
    (by linarith only [hD] : 0 ≤ D + 1) hPτ hgridAxes (le_refl (Real.exp O)) hQexp
    (le_refl (Real.exp eI)) hbox hinv hXexp hSexp hτexp
  simpa only [allocatedConstructedContinuousLog, eI, Pmesh] using hresult

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq fullBooleanRowSetFintype

noncomputable def allocatedCoarseContinuousLog {A : Type*} [Semiring A]
    (m dim : ℕ) (D pI p0 pAccuracy w v E0 O Pτ c : A) : A :=
  (D + 1) + p0 + (3 * (coarseSpatialReciprocalLog (allocatedProductCoarseInput m dim p0 pAccuracy w v E0) + 4) + 6) +
    (Pτ + 8) + (D + O + (D + 8) + allocatedFiniteIdealLipschitzLog D pI c + 1) + 1

variable {m dim : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X] (modulus : ℕ) (q : X → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (residueRefinedPeriod modulus q)) →
  PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (coverWitness : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus q) r.val)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value) (N : X → ℕ) {τ : ℝ} (base : X → ℤ)
variable (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus q))
variable (a : ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
variable (bW : ∀ j, Basis (Kcov j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d period : ℕ) [NeZero d] [NeZero period]
variable (hR : ∀ j, 0 < R j)
variable {M : ℕ} (selection : Fin dim ↪ G)
variable (F : AllocatedFiniteIdealData (Fin dim) I n)

local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => {s : Finset (Fin dim) // s ∈ rowSets j})
local notation "gridAxes" => {i // allocatedGridAxis (I := I) U b S.value i}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "radius" => allocatedProductIdealSiteRadius (G := G) B rowSets
local notation "positiveRadius" => allocatedProductIdealSiteRadius_pos (G := G) B rowSets

theorem allocatedCoarseContinuousSiteFactor_bounds
    {δ : ℝ≥0} {ε pI p0 pAccuracy w v E0 O Pτ D : ℝ}
    (hF : F.Bounds B U b S rowSets x (coverWitness r).representative
      (residueRefinedPeriod modulus q) d period hb o bW hR δ ε pI (layerKernelIndexBound m M))
    {T C A H : gridAxes → ℝ}
    (hgrid : ∀ i, ((coverWitness r).expansion i).Bounds (T i) (C i) (A i)
      ⟨Real.exp O, Real.exp_nonneg _⟩ (H i))
    (hpI : 0 ≤ pI) (hp0 : 0 ≤ p0) (hpAccuracy : 0 ≤ pAccuracy)
    (hw : 0 ≤ w) (hv : 0 ≤ v) (hE0 : 0 ≤ E0) (hO : 0 ≤ O) (hPτ : 0 ≤ Pτ)
    (hgeom : AllocatedComparisonDimensions (G := G) B (Fin dim) rowTypes D)
    (hG : (Fintype.card G : ℝ) ≤ p0) (hX : (Fintype.card X : ℝ) ≤ p0)
    (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp p0) (hmod : modulus ≤ M ^ (m + 1))
    (hq : ∀ z, 0 < q z) (hN : ∀ z, 0 < N z) (hτ : 0 < τ) (hτexp : 1 / τ ≤ Real.exp Pτ) :
    let meshR := allocatedProductCoarseMesh m X selection M modulus p0 pAccuracy w v E0
    let mesh : ℝ≥0 := ⟨meshR, (allocatedProductCoarseMesh_partition_budget m X selection
      hp0 hpAccuracy hw hv hE0 hG hX hM hMP hmod).1.le⟩
    ∀ (spatial : X → SpatialSiteLabel (Fin dim) modulus 4 mesh)
      (kg : ∀ i, ((coverWitness r).expansion i).Term) (i : F.Term) (s : Finset (Fin dim))
      (gridLabel : ∀ j, ZMod (((coverWitness r).expansion j).period (kg j))),
      (∀ v, ‖allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S X modulus q wholeReference
        coverWitness x N mesh base r a spatial kg (F.factor i s) s gridLabel v‖ ≤ 1) ∧
      LipschitzWith
        ⟨Real.exp (allocatedCoarseContinuousLog m dim D pI p0 pAccuracy w v E0 O Pτ (normalizedSiteCutoffBound : ℝ)),
          Real.exp_nonneg _⟩
        (allocatedRecenteredContinuousSiteFactor (τ := τ) B U b S X modulus q wholeReference
          coverWitness x N mesh base r a spatial kg (F.factor i s) s gridLabel) := by
  intro meshR mesh spatial kg i s gridLabel
  rcases hgeom with ⟨hD, _, _, hcube, haxes, _, _, hout, _, hcoeff, hprofile⟩
  have hdim : (dim : ℝ) ≤ D := by simpa only [Fintype.card_fin] using hcube
  have hgridAxes : (Fintype.card gridAxes : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans haxes
  let Q : ℝ≥0 := ⟨8 * (D + 1), mul_nonneg (by norm_num) (by linarith only [hD])⟩
  have hQ (j : gridAxes) :
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B (ig j).1 (ig j).2) : ℝ) + 1) ≤ Q := by
    have hc : ((layerIntegerPrincipalSlots (G := G) B (ig j).1 (ig j).2).card : ℝ) ≤ D :=
      (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (hcoeff (ig j).1)
    change 8 * (_ + 1) ≤ 8 * (D + 1)
    linarith only [hc]
  have hQexp : (Q : ℝ) ≤ Real.exp (D + 8) := by
    change 8 * (D + 1) ≤ _
    calc
      _ ≤ 8 * Real.exp D := mul_le_mul_of_nonneg_left (Real.add_one_le_exp D) (by norm_num)
      _ ≤ Real.exp 8 * Real.exp D := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  let eI := allocatedFiniteIdealLipschitzLog D pI (normalizedSiteCutoffBound : ℝ)
  have heI : 0 ≤ eI := (allocatedFiniteIdeal_budget_nonneg m hD hpI normalizedSiteCutoffBound.coe_nonneg).2.2
  have hI : LipschitzWith ⟨Real.exp eI, Real.exp_nonneg _⟩
      (bufferedCoordinateProjection (allocatedGridAxis (I := I) U b S.value)
        radius positiveRadius (F.factor i s)) := by
    exact allocatedFiniteIdeal_buffered_lipschitz_budget B U b S rowSets x (coverWitness r).representative
      (residueRefinedPeriod modulus q) d period hb o bW hR F hF hpI hD hdim haxes
      (by simpa only [← Nat.card_eq_fintype_card] using hout) hprofile i s
  have hearly := allocatedProductCoarseMesh_partition_budget m X selection hp0 hpAccuracy hw hv hE0 hG hX hM hMP hmod
  have hinput := allocatedProductCoarseInput_nonneg m dim hp0 hpAccuracy hw hv hE0
  have hreciprocal := (coarseSpatialLogs_nonneg hinput).1
  let Pmesh := coarseSpatialReciprocalLog (allocatedProductCoarseInput m dim p0 pAccuracy w v E0) + 4
  have hPmesh : 0 ≤ Pmesh := by dsimp [Pmesh]; linarith only [hreciprocal]
  have hbox : (4 : ℝ) ≤ Real.exp Pmesh := by
    apply (show (4 : ℝ) ≤ Real.exp 4 by linarith [Real.add_one_le_exp (4 : ℝ)]).trans
    exact Real.exp_le_exp.mpr (by dsimp [Pmesh]; linarith only [hreciprocal])
  have hmeshValue : (mesh : ℝ) = meshR := rfl
  have hinv : 1 / (mesh : ℝ) ≤ Real.exp Pmesh := by
    rw [hmeshValue, one_div]
    apply hearly.2.2.1.trans
    exact Real.exp_le_exp.mpr (by dsimp [Pmesh]; linarith)
  have hXexp : (Fintype.card X : ℝ) ≤ Real.exp p0 :=
    hX.trans (by linarith [Real.add_one_le_exp p0])
  have hSexp : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ Real.exp (D + 1) := by
    have hc : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ D + 1 := by
      simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
      linarith only [hdim]
    exact hc.trans (by linarith [Real.add_one_le_exp (D + 1)])
  have hresult := allocatedRecenteredContinuousSiteFactor_pre_bounds (τ := τ)
    B U b S X modulus q wholeReference coverWitness x N mesh base r a spatial kg (F.factor i s) s gridLabel
    hR hgrid Q hQ (hF.2.2.2.1 i s) hI hearly.1 hq hN hτ
    hD hO (by linarith only [hD] : 0 ≤ D + 8) heI hPmesh hp0
    (by linarith only [hD] : 0 ≤ D + 1) hPτ hgridAxes (le_refl (Real.exp O)) hQexp
    (le_refl (Real.exp eI)) hbox hinv hXexp hSexp hτexp
  simpa only [allocatedCoarseContinuousLog, eI, Pmesh] using hresult

end Erdos3.VectorPolynomial

end

end OAI
