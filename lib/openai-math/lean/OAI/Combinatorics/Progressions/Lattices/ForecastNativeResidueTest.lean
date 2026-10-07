import OAI.Combinatorics.Progressions.Fourier.ForecastSpatialCharacterSplit
import OAI.Combinatorics.Progressions.Sampling.ForecastNativePullbackBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical Matrix

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

def forecastNativeSpatialResidue (hm : 0 < m) {R : Type*}
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → R) : X → R :=
  fun x => out ⟨⟨0, hm⟩, .inl ⟨x, rfl⟩⟩

theorem forecastNativeSpatialResidue_output (hm : 0 < m) {R : Type*}
    (u : X → R) (label : ∀ j, Fin (n j) ⊕ E j → R) :
    forecastNativeSpatialResidue inactive hm (forecastCongruenceOutput inactive u label) = u := rfl

theorem forecastNativeSpatialResidue_reduction (hm : 0 < m) {q d : ℕ} (hd : d ∣ q)
    (u : X → ℤ) (label : ∀ j, Fin (n j) ⊕ E j → ℤ) :
    zmodPiReduction hd (forecastNativeSpatialResidue inactive hm
      (fun a => (forecastCongruenceOutput (R := ℤ) inactive u label a : ZMod q))) =
      fun x => (u x : ZMod d) := by
  funext x
  exact map_intCast (ZMod.castHom hd (ZMod d)) (u x)

noncomputable def forecastNativeSheetResidue (q : ℕ)
    (frozen : ∀ j, {i : Fin (n j) // inactive ⟨j, .inr i⟩} → ℤ)
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod q)
    (j : Fin m) (i : Fin (n j)) : ZMod q :=
  if hi : inactive ⟨j, .inr i⟩ then (frozen j ⟨i, hi⟩ : ZMod q)
  else out ⟨j, .inr (.inr ⟨i, hi⟩)⟩

def forecastNativeFreeDeckResidue {R : Type*}
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → R)
    (j : Fin m) (e : E j) : R := out ⟨j, .inr (.inl e)⟩

noncomputable def forecastNativeCoordinateResidue (q : ℕ)
    (frozen : ∀ j, {i : Fin (n j) // inactive ⟨j, .inr i⟩} → ℤ)
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod q)
    (j : Fin m) : Fin (n j) ⊕ E j → ZMod q :=
  Sum.elim (forecastNativeSheetResidue inactive q frozen out j)
    (forecastNativeFreeDeckResidue inactive out j)

theorem forecastNativeCoordinateResidue_output (q : ℕ) (u : X → ℤ)
    (label : ∀ j, Fin (n j) ⊕ E j → ℤ) :
    forecastNativeCoordinateResidue inactive q (fun j i => label j (.inl i.val))
      (fun a => (forecastCongruenceOutput (R := ℤ) inactive u label a : ZMod q)) =
      fun j i => (label j i : ZMod q) := by
  funext j i
  cases i with
  | inl i =>
    simp only [forecastNativeCoordinateResidue, Sum.elim_inl, forecastNativeSheetResidue]
    split <;> rfl
  | inr e => rfl

variable {J : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

noncomputable def forecastNativeDeckResidueMatrix (q : ℕ) [NeZero q] (j : Fin m) :
    Matrix (J j) (Fin (n j) ⊕ E j) ℤ :=
  Classical.choose (exists_bounded_integerMap_residue_matrix
    (standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)).symm.toLinearMap q)

theorem forecastNativeDeckResidueMatrix_bounds (q : ℕ) [NeZero q] (j : Fin m)
    (a : J j) (i : Fin (n j) ⊕ E j) :
    0 ≤ forecastNativeDeckResidueMatrix U b hb bW q j a i ∧
      forecastNativeDeckResidueMatrix U b hb bW q j a i < q :=
  (Classical.choose_spec (exists_bounded_integerMap_residue_matrix
    (standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)).symm.toLinearMap q)).1 a i

theorem forecastNativeDeckResidueMatrix_apply (q : ℕ) [NeZero q] (j : Fin m)
    (label : Fin (n j) ⊕ E j → ℤ) :
    integerResidueMatrix (forecastNativeDeckResidueMatrix U b hb bW q j) q *ᵥ
        integerResidueMap _ q label =
      integerResidueMap _ q
        ((standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)).symm label) :=
  ((Classical.choose_spec (exists_bounded_integerMap_residue_matrix
    (standardLatticeCoordinates (euclideanSubspace (U j)) (bW j) (b j) (hb j)).symm.toLinearMap q)).2 label).symm

noncomputable def forecastNativeAmbientDeckResidue (q : ℕ) [NeZero q]
    (frozen : ∀ j, {i : Fin (n j) // inactive ⟨j, .inr i⟩} → ℤ)
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → ZMod q) :
    (Σ j, J j) → ZMod q := fun a =>
  (integerResidueMatrix (forecastNativeDeckResidueMatrix U b hb bW q a.1) q *ᵥ
    forecastNativeCoordinateResidue inactive q frozen out a.1) a.2

theorem forecastNativeAmbientDeckResidue_output (q : ℕ) [NeZero q]
    (u : X → ℤ) (sheet : ∀ j, Fin (n j) → ℤ) (deck : ∀ j, E j → ℤ) :
    forecastNativeAmbientDeckResidue inactive U b hb bW q (fun j i => sheet j i.val)
      (fun a => (forecastCongruenceOutput (R := ℤ) inactive u (fun j => Sum.elim (sheet j) (deck j)) a : ZMod q)) =
      fun a : Σ j, J j =>
        (latticeDeckInteger (euclideanSubspace (U a.1)) (bW a.1) (b a.1) (hb a.1)
          (sheet a.1) (deck a.1) a.2 : ZMod q) := by
  unfold forecastNativeAmbientDeckResidue
  have hcoord := forecastNativeCoordinateResidue_output inactive q u
    (fun j => Sum.elim (sheet j) (deck j))
  simp only [Sum.elim_inl] at hcoord
  simp only [hcoord]
  funext a
  exact congrFun (forecastNativeDeckResidueMatrix_apply U b hb bW q a.1
    (Sum.elim (sheet a.1) (deck a.1))) a.2

theorem forecastNativeAmbientDeckResidue_reduction (q : ℕ) [NeZero q]
    {d : ℕ} (hd : d ∣ q) (u : X → ℤ)
    (sheet : ∀ j, Fin (n j) → ℤ) (deck : ∀ j, E j → ℤ) :
    zmodPiReduction hd
      (forecastNativeAmbientDeckResidue inactive U b hb bW q (fun j i => sheet j i.val)
        (fun a => (forecastCongruenceOutput (R := ℤ) inactive u
          (fun j => Sum.elim (sheet j) (deck j)) a : ZMod q))) =
      fun a : Σ j, J j =>
        (latticeDeckInteger (euclideanSubspace (U a.1)) (bW a.1) (b a.1) (hb a.1)
          (sheet a.1) (deck a.1) a.2 : ZMod d) := by
  rw [forecastNativeAmbientDeckResidue_output]
  funext a
  exact map_intCast (ZMod.castHom hd (ZMod d)) _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module
open scoped Classical NNReal
variable {m : ℕ} {X : Type*} [Fintype X]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (R : Fin m → ℝ) (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X E P)
local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit)
local notation "Domain" => (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (Output → ℝ))

namespace NormalizedPolynomialTwist
variable {periodCap coverCap : ℝ} {L : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)

noncomputable def forecastResidueTest (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (sheet : ∀ j, {i : Fin (n j) // P ⟨j, .inr i⟩} → ℤ)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (center : X → ℝ) (τ : ℝ) (out : Out → ZMod q) : Domain → ℂ :=
  W.forecastPullback U b o R P
    (zmodPiReduction hperiod (forecastNativeSpatialResidue P hm out))
    (zmodPiReduction hcover (forecastNativeAmbientDeckResidue P U b hb bW q sheet out))
    center τ frozen

theorem forecastResidueTest_bounds (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (sheet : ∀ j, {i : Fin (n j) // P ⟨j, .inr i⟩} → ℤ)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (center : X → ℝ) (τ : ℝ) (out : Out → ZMod q) :
    (∀ y, ‖W.forecastResidueTest U b hb o bW R P q hm hperiod hcover sheet frozen center τ out y‖ ≤ 1) ∧
      LipschitzWith (L * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
        (W.forecastResidueTest U b hb o bW R P q hm hperiod hcover sheet frozen center τ out) :=
  ⟨W.forecastPullback_norm_le U b o R P _ _ center τ frozen,
    W.forecastPullback_lipschitz U b o R P _ _ center τ frozen⟩

theorem forecastResidueTest_eq_eval (q : ℕ) [NeZero q] (hm : 0 < m)
    (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
    (hR : ∀ j, R j ≠ 0) (base u : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ : ℝ} (hτ : τ ≠ 0)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, E j → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hmem : ∀ j a, coefficients (poly j) a ∈ U j)
    (hchart : let _ : NeZero W.cover := ⟨W.cover_pos.ne'⟩
      ∀ j, BooleanCubeKernel.physicalSingleSiteValue U W.cover poly hmem (fun x => (u x : ℝ)) j () =
        normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) W.cover
          (orthonormalMixedChart (o j) (w j), integerResidueMap (E j) W.cover (deck j))) :
    W.forecastResidueTest U b hb o bW R P q hm hperiod hcover
      (fun j i => (w j).2 i.val)
      (fun a => allocatedFullMixedSiteValue (R := R) U b w a.val)
      (fun x => (base x : ℝ) / N x) τ
      (fun a => (forecastCongruenceOutput (R := ℤ) P u
        (fun j => Sum.elim (w j).2 (deck j)) a : ZMod q))
      ((fun a => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)),
        fun a : Output => allocatedFullMixedSiteValue (R := R) U b w a.1.val) =
      W.eval N poly u := by
  unfold forecastResidueTest
  rw [forecastNativeSpatialResidue_reduction, forecastNativeAmbientDeckResidue_reduction]
  exact W.forecastPullback_eval_of_chart U b o R P hR base u N hN hτ hb bW w deck poly hmem hchart

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

end OAI
