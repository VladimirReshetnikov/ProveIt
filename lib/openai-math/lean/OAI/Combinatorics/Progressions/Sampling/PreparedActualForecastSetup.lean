/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalLocalGoodForecastPath

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped Classical

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem enlargedPreparedCommonSamplerBlock_single_uniform (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    uniformSpectrumBlockCount a.1.val 1 (a.1.val + 1) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  have hrows : 1 ≤ (boundedBooleanJetRows (Fin 1) (a.1.val + 1)).card := by
    apply Nat.succ_le_of_lt
    apply Finset.card_pos.mpr
    refine ⟨∅, ?_⟩
    simp only [mem_boundedBooleanJetRows, Finset.card_empty, Nat.zero_le]
  apply le_trans _ (enlargedPreparedCommonSamplerBlock_uniform L Jalloc 0
    (Nat.zero_le m) a)
  unfold uniformSpectrumBlockCount majorArcSpectrumExponent majorArcCoverExponent
  gcongr
  simpa only [mul_one] using Nat.mul_le_mul_left (a.1.val + 1) hrows

theorem enlargedPreparedCommonSamplerBlock_four (Jalloc : ℕ)
    (a : LayerSamplerAxis (PreparedSamplerContinuous L) (preparedSamplerTransverse L)) :
    4 ≤ Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a) := by
  apply le_trans _ (enlargedPreparedCommonSamplerBlock_single_uniform L Jalloc a)
  unfold uniformSpectrumBlockCount majorArcSpectrumExponent majorArcCoverExponent
    majorArcErrorExponent
  simp only [mul_one]
  omega

theorem enlargedPreparedCommonSamplerBlock_transverse_uniform (Jalloc : ℕ)
    (j : Fin m) (i : Fin (preparedSamplerTransverse L j)) :
    uniformSpectrumBlockCount j.val 1 (j.val + 1) ≤
      Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc ⟨j, Sum.inr i⟩) :=
  enlargedPreparedCommonSamplerBlock_single_uniform L Jalloc ⟨j, Sum.inr i⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators

theorem principalTupleIndex_block_sum_le_card {D : Type*} [Fintype D]
    (B : D → Type*) [∀ d, Fintype (B d)] (degree : D → ℕ)
    (hdegree : ∀ d, 1 ≤ degree d) :
    (∑ d, Fintype.card (B d)) ≤ Fintype.card (PrincipalTupleIndex B degree) := by
  simp only [PrincipalTupleIndex, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  apply Finset.sum_le_sum
  intro d _
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (Fintype.card (B d)) (hdegree d)

namespace VectorPolynomial

theorem layerSampler_block_sum_le_principal_card {m : ℕ}
    (I : Fin m → Type*) [∀ j, Fintype (I j)] (n : Fin m → ℕ)
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] :
    (∑ a, Fintype.card (B a)) ≤
      Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) :=
  principalTupleIndex_block_sum_le_card B (layerSamplerDegree I n)
    (fun _ => Nat.succ_le_succ (Nat.zero_le _))

theorem enlargedPreparedCommonSampler_block_sum_le_principal_card
    {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m) (Jalloc : ℕ) :
    (∑ a, Fintype.card (EnlargedPreparedCommonSamplerBlock L Jalloc a)) ≤
      Fintype.card (PrincipalTupleIndex (EnlargedPreparedCommonSamplerBlock L Jalloc)
        (layerSamplerDegree (PreparedSamplerContinuous L) (preparedSamplerTransverse L))) :=
  layerSampler_block_sum_le_principal_card (PreparedSamplerContinuous L)
    (preparedSamplerTransverse L) (EnlargedPreparedCommonSamplerBlock L Jalloc)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

section Generic

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

abbrev PreparedActualForecastShortIndex := AllocatedShortIntegerAxis U b S.value

def preparedActualForecastShortSelection :
    PreparedActualForecastShortIndex B U b S → Σ j : Fin m, Fin (n j) :=
  Subtype.val

theorem preparedActualForecastShortSelection_injective :
    Function.Injective (preparedActualForecastShortSelection B U b S) :=
  Subtype.val_injective

theorem preparedActualForecastShortSelection_small
    (a : PreparedActualForecastShortIndex B U b S) :
    basisAxisScale (b (preparedActualForecastShortSelection B U b S a).1)
      (preparedActualForecastShortSelection B U b S a).2 ≤
      S.value ^ ((preparedActualForecastShortSelection B U b S a).1.val + 1) :=
  a.property

theorem preparedActualForecastShortSelection_exhaustive
    (a : LayerSamplerAxis I n) (ha : allocatedShortAxis U b S.value a) :
    ∃ i : PreparedActualForecastShortIndex B U b S,
      (⟨(preparedActualForecastShortSelection B U b S i).1,
        Sum.inr (preparedActualForecastShortSelection B U b S i).2⟩ :
          LayerSamplerAxis I n) = a := by
  rcases a with ⟨j, a⟩
  cases a with
  | inl a => exact False.elim ha
  | inr a => exact ⟨⟨⟨j, a⟩, ha⟩, rfl⟩

def preparedActualForecastShortAxisEmbedding :
    PreparedActualForecastShortIndex B U b S ↪ LayerSamplerAxis I n where
  toFun a := ⟨a.val.1, Sum.inr a.val.2⟩
  inj' := by
    intro a c h
    apply (allocatedShortIntegerAxisEquiv (I := I) U b S.value).injective
    exact Subtype.ext h

theorem preparedActualForecastShortIndex_card_le_axes :
    Fintype.card (PreparedActualForecastShortIndex B U b S) ≤
      Fintype.card (LayerSamplerAxis I n) :=
  Fintype.card_le_of_injective _ (preparedActualForecastShortAxisEmbedding B U b S).injective

theorem preparedActualForecastShortIndex_card_le_sum :
    Fintype.card (PreparedActualForecastShortIndex B U b S) ≤ ∑ j : Fin m, n j :=
  allocatedShortIntegerAxis_card U b S.value

theorem preparedActualForecastShortIndex_card_le {D : ℝ}
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D) :
    (Fintype.card (PreparedActualForecastShortIndex B U b S) : ℝ) ≤ D :=
  (Nat.cast_le.mpr (preparedActualForecastShortIndex_card_le_axes B U b S)).trans haxes

theorem preparedActualForecastShortSelection_inverse_bound {P : ℝ}
    (hR : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (a : PreparedActualForecastShortIndex B U b S) :
    (R (preparedActualForecastShortSelection B U b S a).1)⁻¹ ≤ Real.exp P :=
  hR _

end Generic

section Prepared

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m) (Jalloc : ℕ)
variable {G : Type*} [Fintype G]
variable {Jout : Fin m → Type*} [∀ j, Fintype (Jout j)]
variable (U : ∀ j, Submodule ℝ (Jout j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
  (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := G) (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)

theorem enlargedPreparedActualForecastShortSelection_nonempty
    (a : PreparedActualForecastShortIndex (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S) :
    Nonempty (EnlargedPreparedCommonSamplerBlock L Jalloc
      ⟨(preparedActualForecastShortSelection (EnlargedPreparedCommonSamplerBlock L Jalloc)
        U b S a).1,
        Sum.inr (preparedActualForecastShortSelection
          (EnlargedPreparedCommonSamplerBlock L Jalloc) U b S a).2⟩) :=
  Fintype.card_pos_iff.mp (enlargedPreparedCommonSamplerBlock_positive L Jalloc _)

end Prepared

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical BigOperators

section Grid

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def preparedActualForecastGridVolume : ℝ :=
  ∏ a : PreparedActualForecastShortIndex B U b S,
    (basisAxisScale (b (preparedActualForecastShortSelection B U b S a).1)
      (preparedActualForecastShortSelection B U b S a).2 : ℝ)

theorem preparedActualForecastGridVolume_one_le :
    1 ≤ preparedActualForecastGridVolume B U b S := by
  unfold preparedActualForecastGridVolume
  apply Finset.one_le_prod₀
  intro a _
  exact_mod_cast basisAxisScale_pos
    (b (preparedActualForecastShortSelection B U b S a).1)
    (preparedActualForecastShortSelection B U b S a).2

theorem preparedActualForecastGridVolume_pos :
    0 < preparedActualForecastGridVolume B U b S :=
  lt_of_lt_of_le zero_lt_one (preparedActualForecastGridVolume_one_le B U b S)

end Grid

theorem preparedActualForecastJacobian_budget
    {m M nX : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    {G : Type*} [Fintype G]
    (B : LayerSamplerAxis (PreparedSamplerContinuous prep)
      (preparedSamplerTransverse prep) → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ
      (euclideanSubspace (U j))ᗮ)
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    {pRadius gainLog Pchart : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog) (hChart : 0 ≤ Pchart)
    (hR : ∀ j, 0 < R j) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hcovol : ∀ j, ZLattice.covolume
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))) ≤ Real.exp Pchart) :
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let Pκ := ((nX + m + m * M : ℕ) : ℝ) *
      (pRadius + gainLog + nX + Pchart + 11)
    let κ := forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous prep)
      U b R S.value (preparedActualForecastGridVolume B U b S) τ
    0 < κ ∧ 0 ≤ Pκ ∧ κ ≤ Real.exp Pκ :=
  preparedForecastJacobian_budget prep U b hCoord hpRadius hGain hChart hR hRinv
    hcovol S.value (preparedActualForecastGridVolume_one_le B U b S)

section EnlargedPrepared

variable {m : ℕ} {X₀ J₀ : Type}
variable (prep : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
variable (U : ∀ j, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ
  (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock prep Jalloc) U b R σ)

noncomputable abbrev preparedForecastGridVolume : ℝ :=
  preparedActualForecastGridVolume (EnlargedPreparedCommonSamplerBlock prep Jalloc) U b S

theorem preparedForecastGridVolume_one_le :
    1 ≤ preparedForecastGridVolume prep Jalloc U b S :=
  preparedActualForecastGridVolume_one_le
    (EnlargedPreparedCommonSamplerBlock prep Jalloc) U b S

theorem preparedForecastGridVolume_pos :
    0 < preparedForecastGridVolume prep Jalloc U b S :=
  preparedActualForecastGridVolume_pos
    (EnlargedPreparedCommonSamplerBlock prep Jalloc) U b S

variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]

theorem preparedForecastGridJacobian_budget {M nX : ℕ} {pRadius gainLog Pchart : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog) (hChart : 0 ≤ Pchart)
    (hR : ∀ j, 0 < R j) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hcovol : ∀ j, ZLattice.covolume
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j)))
        (euclideanSubspace (U j))) ≤ Real.exp Pchart) :
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let Pκ := ((nX + m + m * M : ℕ) : ℝ) *
      (pRadius + gainLog + nX + Pchart + 11)
    let κ := forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous prep)
      U b R S.value (preparedForecastGridVolume prep Jalloc U b S) τ
    0 < κ ∧ 0 ≤ Pκ ∧ κ ≤ Real.exp Pκ :=
  preparedActualForecastJacobian_budget prep
    (EnlargedPreparedCommonSamplerBlock prep Jalloc) U b S hCoord
    hpRadius hGain hChart hR hRinv hcovol

end EnlargedPrepared

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedActualForecastGridVolume_mul_active_heights :
    preparedActualForecastGridVolume B U b S *
      (∏ a : AllocatedActiveIntegerAxis U b S.value,
        (basisAxisScale (b a.val.1) a.val.2 : ℝ)) =
      ∏ j : Fin m, ∏ i : Fin (n j), (basisAxisScale (b j) i : ℝ) := by
  let p : (Σ j : Fin m, Fin (n j)) → Prop :=
    fun a => basisAxisScale (b a.1) a.2 ≤ S.value ^ (a.1.val + 1)
  let activeEquiv : {a // ¬p a} ≃ AllocatedActiveIntegerAxis U b S.value :=
    { toFun := fun a => ⟨a.val, Nat.lt_of_not_ge a.property⟩
      invFun := fun a => ⟨a.val, Nat.not_le.mpr a.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hactive : (∏ a : {a // ¬p a}, (basisAxisScale (b a.val.1) a.val.2 : ℝ)) =
      ∏ a : AllocatedActiveIntegerAxis U b S.value,
        (basisAxisScale (b a.val.1) a.val.2 : ℝ) :=
    Fintype.prod_equiv activeEquiv _ _ (fun _ => rfl)
  have h := Fintype.prod_subtype_mul_prod_subtype p
    (fun a : Σ j : Fin m, Fin (n j) => (basisAxisScale (b a.1) a.2 : ℝ))
  rw [hactive, Fintype.prod_sigma] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedActualForecastGridVolume_eq_allocated_product :
    preparedActualForecastGridVolume B U b S =
      ∏ a : AllocatedShortIntegerAxis U b S.value,
        (basisAxisScale (b (allocatedShortIntegerSelection U b S.value a).1)
          (allocatedShortIntegerSelection U b S.value a).2 : ℝ) := by
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped Classical BigOperators

section Generic
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {X : Type*} [Fintype X]

theorem preparedActualForecastJacobian_eq_ratio (τ : ℝ) :
    forecastGeometricJacobian (X := X) (I := I) U b R S.value
      (preparedActualForecastGridVolume B U b S) τ =
    (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)) *
      ((τ / 8) ^ Fintype.card X)⁻¹ *
      (∏ a : Σ j, I j, R a.1)⁻¹ *
      (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1)⁻¹ := by
  have hcombined : coveredJetArrayScale (O := fun _ : Fin m => Unit) U *
      preparedActualForecastGridVolume B U b S *
        (∏ a : AllocatedActiveIntegerAxis U b S.value,
          (basisAxisScale (b a.val.1) a.val.2 : ℝ)) =
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j))⁻¹ := by
    rw [mul_assoc, preparedActualForecastGridVolume_mul_active_heights]
    simp only [coveredJetArrayScale, Fintype.card_unit, pow_one,
      mixedDensityCovolumeRatio, div_eq_mul_inv, Finset.prod_mul_distrib,
      Finset.prod_inv_distrib, mul_inv_rev, inv_inv]
    ring
  have hactive : (∏ a, allocatedActiveIntegerGridScale U b R S.value a) =
      (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1) *
        (∏ a : AllocatedActiveIntegerAxis U b S.value,
          (basisAxisScale (b a.val.1) a.val.2 : ℝ)) := by
    simp only [allocatedActiveIntegerGridScale, Finset.prod_mul_distrib]
  have hden : coveredJetArrayScale (O := fun _ : Fin m => Unit) U *
      preparedActualForecastGridVolume B U b S * (τ / 8) ^ Fintype.card X *
        (∏ a : Σ j, I j, R a.1) * (∏ a, allocatedActiveIntegerGridScale U b R S.value a) =
      (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j))⁻¹ *
        (τ / 8) ^ Fintype.card X * (∏ a : Σ j, I j, R a.1) *
        (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1) := by
    rw [hactive]
    calc
      _ = (coveredJetArrayScale (O := fun _ : Fin m => Unit) U *
          preparedActualForecastGridVolume B U b S *
            (∏ a : AllocatedActiveIntegerAxis U b S.value,
              (basisAxisScale (b a.val.1) a.val.2 : ℝ))) *
          (τ / 8) ^ Fintype.card X * (∏ a : Σ j, I j, R a.1) *
          (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1) := by ring
      _ = _ := by rw [hcombined]
  rw [forecastGeometricJacobian, hden]
  simp only [mul_inv_rev, inv_inv]
  ring

variable [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

private theorem ratioJacobian_product_le_exp {A : Type*} [Fintype A] {P : ℝ}
    (f : A → ℝ) (hf : ∀ a, 0 ≤ f a) (hb : ∀ a, f a ≤ Real.exp P) :
    (∏ a, f a) ≤ Real.exp ((Fintype.card A : ℝ) * P) := by
  calc
    _ ≤ ∏ _a : A, Real.exp P := Finset.prod_le_prod₀ (fun a _ => hf a) (fun a _ => hb a)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]

theorem preparedActualForecastJacobian_ratio_le_exp
    (hR : ∀ j, 0 < R j) {τ P : ℝ} (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp P) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P) :
    forecastGeometricJacobian (X := X) (I := I) U b R S.value
      (preparedActualForecastGridVolume B U b S) τ ≤
    Real.exp ((m : ℝ) * P + (Fintype.card X : ℝ) * (P + 3) +
      (Fintype.card (Σ j, I j) : ℝ) * P +
      (Fintype.card (AllocatedActiveIntegerAxis U b S.value) : ℝ) * P) := by
  have hchart : (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j)) ≤
      Real.exp ((m : ℝ) * P) := by
    simpa only [Fintype.card_fin] using ratioJacobian_product_le_exp
      (fun j => mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j))
      (fun j => (mixedDensityCovolumeRatio_pos (euclideanSubspace (U j)) (b j)).le) hratio
  have h8 : (8 : ℝ) ≤ Real.exp 3 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp (1 : ℝ) using 1
      norm_num
    calc
      _ = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hsp : ((τ / 8) ^ Fintype.card X)⁻¹ ≤
      Real.exp ((Fintype.card X : ℝ) * (P + 3)) := by
    rw [← inv_pow]
    have hi : (τ / 8)⁻¹ ≤ Real.exp (P + 3) := by
      calc
        _ = 8 * τ⁻¹ := by rw [inv_div, div_eq_mul_inv]
        _ ≤ Real.exp 3 * Real.exp P :=
          mul_le_mul h8 hτinv (inv_nonneg.mpr hτ.le) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    exact (pow_le_pow_left₀ (inv_nonneg.mpr (div_pos hτ (by norm_num)).le) hi _).trans_eq
      (Real.exp_nat_mul _ _).symm
  have hcontinuous : (∏ a : Σ j, I j, R a.1)⁻¹ ≤
      Real.exp ((Fintype.card (Σ j, I j) : ℝ) * P) := by
    simpa only [← Finset.prod_inv_distrib] using ratioJacobian_product_le_exp
      (fun a : Σ j, I j => (R a.1)⁻¹)
      (fun a => inv_nonneg.mpr (hR a.1).le) (fun a => hRinv a.1)
  have hactive : (∏ a : AllocatedActiveIntegerAxis U b S.value, R a.val.1)⁻¹ ≤
      Real.exp ((Fintype.card (AllocatedActiveIntegerAxis U b S.value) : ℝ) * P) := by
    simpa only [← Finset.prod_inv_distrib] using ratioJacobian_product_le_exp
      (fun a : AllocatedActiveIntegerAxis U b S.value => (R a.val.1)⁻¹)
      (fun a => inv_nonneg.mpr (hR a.val.1).le) (fun a => hRinv a.val.1)
  have hcs := mul_le_mul hchart hsp
    (inv_nonneg.mpr (pow_nonneg (div_pos hτ (by norm_num)).le _)) (Real.exp_nonneg _)
  have hcsc := mul_le_mul hcs hcontinuous
    (inv_nonneg.mpr (Finset.prod_nonneg (fun a _ => (hR a.1).le))) (by positivity)
  have hfull := mul_le_mul hcsc hactive
    (inv_nonneg.mpr (Finset.prod_nonneg (fun a _ => (hR a.val.1).le))) (by positivity)
  rw [preparedActualForecastJacobian_eq_ratio]
  simpa only [← Real.exp_add] using hfull

theorem preparedActualForecastJacobian_ratio_uniform_le_exp
    (hR : ∀ j, 0 < R j) {τ P : ℝ} (hP : 0 ≤ P) (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ Real.exp P) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hratio : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P) :
    forecastGeometricJacobian (X := X) (I := I) U b R S.value
      (preparedActualForecastGridVolume B U b S) τ ≤
    Real.exp (((m : ℝ) + Fintype.card X + Fintype.card (Σ j, I j) +
      Fintype.card (Σ j : Fin m, Fin (n j))) * (P + 3)) := by
  apply (preparedActualForecastJacobian_ratio_le_exp B U b S hR hτ hτinv hRinv hratio).trans
  apply Real.exp_le_exp.mpr
  have hcard : (Fintype.card (AllocatedActiveIntegerAxis U b S.value) : ℝ) ≤
      Fintype.card (Σ j : Fin m, Fin (n j)) := by
    exact_mod_cast (Fintype.card_subtype_le
      (fun a : Σ j : Fin m, Fin (n j) =>
        S.value ^ (a.1.val + 1) < basisAxisScale (b a.1) a.2))
  have hmul := mul_le_mul_of_nonneg_right hcard hP
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hi0 : (0 : ℝ) ≤ Fintype.card (Σ j, I j) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ Fintype.card (Σ j : Fin m, Fin (n j)) := Nat.cast_nonneg _
  nlinarith

end Generic

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical BigOperators

theorem preparedActualForecastJacobian_ratio_budget
    {m M nX : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    {G : Type*} [Fintype G]
    (B : LayerSamplerAxis (PreparedSamplerContinuous prep)
      (preparedSamplerTransverse prep) → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    [∀ j, IsZLattice ℝ (latticeSection
      (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j)))]
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    {pRadius gainLog Pchart : ℝ}
    (hCoord : ∀ j, Fintype.card (prep j).Coord ≤ M)
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog) (hChart : 0 ≤ Pchart)
    (hR : ∀ j, 0 < R j) (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius)
    (hratio : ∀ j, mixedDensityCovolumeRatio
      (euclideanSubspace (U j)) (b j) ≤ Real.exp Pchart) :
    let τ := Real.exp (-(gainLog + (nX : ℝ) + 8))
    let Pκ := ((nX + m + m * M : ℕ) : ℝ) *
      (pRadius + gainLog + nX + Pchart + 11)
    0 < forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous prep)
      U b R S.value (preparedActualForecastGridVolume B U b S) τ ∧
    0 ≤ Pκ ∧
    forecastGeometricJacobian (X := Fin nX) (I := PreparedSamplerContinuous prep)
      U b R S.value (preparedActualForecastGridVolume B U b S) τ ≤ Real.exp Pκ := by
  intro τ Pκ
  let P := pRadius + gainLog + nX + Pchart + 8
  have hn : (0 : ℝ) ≤ nX := Nat.cast_nonneg _
  have hP : 0 ≤ P := by dsimp only [P]; linarith
  have hrP : pRadius ≤ P := by dsimp only [P]; linarith
  have hcP : Pchart ≤ P := by dsimp only [P]; linarith
  have htP : gainLog + nX + 8 ≤ P := by dsimp only [P]; linarith
  have hτ : 0 < τ := Real.exp_pos _
  have hτinv : τ⁻¹ ≤ Real.exp P := by
    change (Real.exp (-(gainLog + (nX : ℝ) + 8)))⁻¹ ≤ Real.exp P
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr htP
  have hdim : Fintype.card (Σ j, PreparedSamplerContinuous prep j) +
      Fintype.card (Σ j : Fin m, Fin (preparedSamplerTransverse prep j)) ≤ m * M := by
    simp only [Fintype.card_sigma, Fintype.card_fin, ← Finset.sum_add_distrib]
    calc
      _ = ∑ j : Fin m, Fintype.card (prep j).Coord := by
        apply Finset.sum_congr rfl
        intro j _
        simpa only [PreparedSamplerContinuous, Fintype.card_fin] using preparedSampler_axis_card prep j
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => hCoord j)
      _ = m * M := by simp
  have hdimR := Nat.cast_le (α := ℝ).mpr hdim
  simp only [Nat.cast_add, Nat.cast_mul] at hdimR
  have hκ := preparedActualForecastJacobian_ratio_uniform_le_exp
    (X := Fin nX) B U b S hR hP hτ hτinv
    (fun j => (hRinv j).trans (Real.exp_le_exp.mpr hrP))
    (fun j => (hratio j).trans (Real.exp_le_exp.mpr hcP))
  refine ⟨forecastGeometricJacobian_pos U b hR S.value
    (preparedActualForecastGridVolume_pos B U b S) hτ, ?_, ?_⟩
  · dsimp only [Pκ]
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  · apply hκ.trans (Real.exp_le_exp.mpr ?_)
    have hmult := mul_le_mul_of_nonneg_right
      (show (m : ℝ) + Fintype.card (Fin nX) +
        Fintype.card (Σ j, PreparedSamplerContinuous prep j) +
        Fintype.card (Σ j : Fin m, Fin (preparedSamplerTransverse prep j)) ≤
        ((nX + m + m * M : ℕ) : ℝ) by
          simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul]
          linarith) (show 0 ≤ P + 3 by linarith)
    apply hmult.trans_eq
    dsimp only [Pκ, P]
    ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal

private theorem forecastRows_one_le (j : ℕ) :
    1 ≤ (boundedBooleanJetRows (Fin 1) (j + 1)).card := by
  apply Finset.one_le_card.mpr
  exact ⟨∅, by simp only [mem_boundedBooleanJetRows, Finset.card_empty, Nat.zero_le]⟩

theorem preparedActualForecast_radius_bounds
    {m : ℕ} (hm : 0 < m) {Vars : Type} [Fintype Vars]
    (T : Fin m → ℝ) (radius : ℝ≥0)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent Vars (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ)) :
    (3 : ℝ) ≤ radius ∧
      ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent Vars (j.val + 1)) : ℝ) ≤ radius := by
  have hcount (j : Fin m) :
      (1 : ℝ) ≤ Fintype.card (BoundedCoefficientExponent Vars (j.val + 1)) := by
    have : Nonempty (BoundedCoefficientExponent Vars (j.val + 1)) := ⟨⟨0, by simp⟩⟩
    exact_mod_cast Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr this)
  have hT0 (j : Fin m) : 0 ≤ T j :=
    (mul_nonneg (Nat.cast_nonneg _) (by positivity)).trans (hT j)
  have hTradius (j : Fin m) : T j ≤ (radius : ℝ) :=
    (le_mul_of_one_le_left (hT0 j) (by exact_mod_cast forecastRows_one_le j.val)).trans (hradius j)
  constructor
  · let j : Fin m := ⟨0, hm⟩
    have hj := (hT j).trans (hTradius j)
    have hc := hcount j
    norm_num only [j, Nat.zero_add, pow_one] at hj
    linarith
  · intro j
    have hf : (1 : ℝ) ≤ 2 * 2 ^ (j.val + 1) := by
      have := (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) : (1 : ℝ) ≤ 2 ^ (j.val + 1))
      linarith
    exact (le_mul_of_one_le_right (Nat.cast_nonneg _) hf).trans ((hT j).trans (hTradius j))

variable {X₀ J₀ : Type} {m : ℕ} (L : RankPreparationFamily X₀ J₀ m) (Jalloc : ℕ)
local notation "G" => EnlargedPreparedCommonKernel m Jalloc
local notation "I" => PreparedSamplerContinuous L
local notation "n" => preparedSamplerTransverse L
local notation "B" => EnlargedPreparedCommonSamplerBlock L Jalloc
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale («G» := EnlargedPreparedCommonKernel m Jalloc)
  (EnlargedPreparedCommonSamplerBlock L Jalloc) U b R σ)
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (bW : ∀ j, Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

noncomputable def preparedActualForecastSetup {M nX : ℕ}
    (hm : 0 < m) (hCoord : ∀ j, Fintype.card (L j).Coord ≤ M)
    {pRadius gainLog Pbad Ppres PF Pκ κ : ℝ}
    (hpRadius : 0 ≤ pRadius) (hGain : 0 ≤ gainLog)
    (hPbad : 0 ≤ Pbad) (hPpres : 0 ≤ Ppres) (hPF : 0 ≤ PF) (hPκ : 0 ≤ Pκ)
    (hκ : 0 ≤ κ) (hκcap : κ ≤ Real.exp Pκ)
    (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hRinv : ∀ j, (R j)⁻¹ ≤ Real.exp pRadius) (hσone : ∀ j, σ j ≤ 1)
    (forward : Fin m → ℝ≥0)
    (hforward : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ forward j * ‖w‖)
    (hforwardBound : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (radius : ℝ≥0) (T : Fin m → ℝ)
    (hT : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      (2 * 2 ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j : Fin m, (boundedBooleanJetRows (Fin 1) (j.val + 1)).card * T j ≤ (radius : ℝ))
    (inverse : Fin m → ℝ) (hinverse : ∀ j, 0 ≤ inverse j)
    (hchart : ∀ j (w : euclideanSubspace (U j) × (Fin (preparedSamplerTransverse L j) → ℝ)), ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm w‖ ≤ inverse j * ‖w‖)
    (hsourceBudget : ∀ j : Fin m,
      ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
        (Fintype.card (Finset (Fin 1)) : ℝ) *
        (inverse j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (radius : ℝ) * R j))) ≤ 1 / 4) :
    ActualFixedSpatialForecastSetup (X := Fin nX) (Eout := Eout)
      («G» := G) («I» := I) («n» := n) (A := PreparedActualForecastShortIndex («G» := G) B U b S)
      B U b S (nX + m * M) (preparedActualForecastShortSelection («G» := G) B U b S)
      (Real.exp (-(gainLog + (nX : ℝ) + 8))) (1 / 2) := by
  let pnum : ℝ := enlargedPreparedCommonSamplerDimension m M Jalloc
  let D : ℝ := allocatedComparisonDimension m pnum
  let P : ℝ := D + nX + 8
  obtain ⟨hvars, hI, hn⟩ := enlargedPreparedCommonSampler_dimensions L Jalloc hCoord
  have hd : AllocatedComparisonDimensions («G» := G) B Empty
      (fun _ : Fin m => ((Finset.univ : Finset (Finset Empty)) : Type)) D :=
    allocatedComparisonDimensions_of_primitive B (fun _ => Subtype.val)
      (by simp) (fun _ => Subtype.val_injective) (Nat.cast_nonneg _)
      (Nat.cast_le.mpr hvars) (fun j => Nat.cast_le.mpr (hI j)) (fun j => Nat.cast_le.mpr (hn j))
  have hP : 1 ≤ P := by dsimp only [P]; have := hd.nonneg; have := Nat.cast_nonneg (α := ℝ) nX; linarith
  have hDP : D ≤ P := by dsimp only [P]; have := Nat.cast_nonneg (α := ℝ) nX; linarith
  have hdimEq : (∑ j, Fintype.card (J j) : ℕ) = Fintype.card (LayerSamplerAxis I n) := by
    simp only [LayerSamplerAxis, Fintype.card_sigma, Fintype.card_sum, Fintype.card_fin]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [PreparedSamplerContinuous, Fintype.card_fin] using
      (allocatedAmbientDimension_eq U b o j).symm
  have hDmod : Fintype.card (Fin nX) + ∑ j : Fin m, (Fintype.card (Eout j) + n j) ≤ nX + m * M := by
    simp only [Fintype.card_fin]
    apply Nat.add_le_add_left
    calc
      _ = ∑ j : Fin m, Fintype.card (L j).Coord := by
        apply Finset.sum_congr rfl
        intro j _
        rw [allocatedLatticeDimension_eq U b o hb bW j]
        exact preparedSampler_axis_card L j
      _ ≤ ∑ _j : Fin m, M := Finset.sum_le_sum (fun j _ => hCoord j)
      _ = m * M := by simp
  have hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P := by
    have hh := Nat.cast_le (α := ℝ).mpr (enlargedPreparedCommonSampler_block_sum_le_principal_card L Jalloc)
    rw [Nat.cast_sum] at hh
    exact hh.trans (hd.tuples.trans hDP)
  have hscale : 0 ≤ D + pRadius + 1 := by linarith only [hd.nonneg, hpRadius]
  have hscaleRadius : pRadius ≤ D + pRadius + 1 := by linarith only [hd.nonneg]
  obtain ⟨hr3, hrcoeff⟩ := preparedActualForecast_radius_bounds hm T radius hT hradius
  obtain ⟨hτlog, hτ, _, _, hτinv, _⟩ := preparedEarlySpatialWidth nX hGain
  let transition := scalarSourceTransitionBound
  let Pcap := max 1 (scalarCubePrimitiveEnvelope Empty transition 1 0 1)
  have hPcap : 1 ≤ Pcap := le_max_left _ _
  refine {
    hm := hm
    hDmod := hDmod
    hselected := preparedActualForecastShortSelection_injective («G» := G) B U b S
    selectedNonempty := enlargedPreparedActualForecastShortSelection_nonempty L Jalloc U b S
    D := D, P := P, Pcap := Pcap, pcap := Pcap
    Pscale := D + pRadius + 1, Pbad := Pbad, Ppres := Ppres
    Pτ := gainLog + nX + 8, PK := pRadius, PF := PF, Pκ := Pκ, κ := κ
    hD := hd, hP := hP, hDP := hDP, haxes := hd.axes
    hdim := by rw [hdimEq]; exact hd.axes
    hX := by simp only [Fintype.card_fin]; dsimp only [P]; linarith only [hd.nonneg]
    hblocks := hblocks
    hPcap := hPcap, hpcap := zero_le_one.trans hPcap
    hPcapp := by linarith only [Real.add_one_le_exp Pcap]
    hPscale := hscale, hPbad := hPbad, hPpres := hPpres, hPτ := hτlog
    hPK := hpRadius, hPF := hPF, hPκ := hPκ, hκ := hκ, hκcap := hκcap
    hτ := hτ, hτinv := hτinv.le
    hδslice := by norm_num
    hδsliceInv := by norm_num; linarith only [Real.add_one_le_exp P, hP]
    hR1 := fun a => hRone _, hσ1 := fun a => hσone _
    hsmall := preparedActualForecastShortSelection_small («G» := G) B U b S
    L := transition, hL := scalarSourceTransitionBound_spec.2
    hprimitiveCap := le_max_right _ _
    hB := fun a => enlargedPreparedCommonSamplerBlock_transverse_uniform L Jalloc _ _
    hRinv := fun a => (hRinv _).trans (Real.exp_le_exp.mpr hscaleRadius)
    hslots := ?_
    hBactive := fun a => enlargedPreparedCommonSamplerBlock_four L Jalloc a.val
    forward := forward, hforward := hforward, hforwardBound := hforwardBound
    K := ⟨Real.exp pRadius, Real.exp_nonneg _⟩, hK := hRinv, hKBound := le_rfl
    radius := radius, hr3 := hr3, hradius := hrcoeff
    inverse := inverse, hinverse := hinverse, hchart := hchart
    hbudget := ?_
    hexhaustive := preparedActualForecastShortSelection_exhaustive («G» := G) B U b S }
  · intro a
    have hh := (Nat.cast_le (α := ℝ).mpr (Finset.card_le_univ
      (layerIntegerPrincipalSlots («G» := G) B a.val.1 a.val.2))).trans (hd.coefficients a.val.1)
    exact hh.trans (by linarith only [hpRadius])
  · intro j
    have hinner : 0 ≤ inverse j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (radius : ℝ) * R j)) :=
      mul_nonneg (hinverse j) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hR j).le))
    have hrows : (0 : ℝ) ≤ (boundedBooleanJetRows (Fin 1) (j.val + 1)).card := Nat.cast_nonneg _
    have hfactor : (1 : ℝ) ≤
        ((boundedBooleanJetRows (Fin 1) (j.val + 1)).card + 1 : ℝ) *
          (Fintype.card (Finset (Fin 1)) : ℝ) := by
      norm_num only [Fintype.card_finset, Fintype.card_fin, Nat.cast_ofNat, pow_one]
      linarith only [hrows]
    exact (le_mul_of_one_le_left hinner hfactor).trans (hsourceBudget j)

end Erdos3.VectorPolynomial

end

end OAI
