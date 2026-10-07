import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankBadProduct
import OAI.Combinatorics.Progressions.Polynomial.ConditionPolynomialMapDegree

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {N L : ℕ}

noncomputable def allocatedCongruenceIntegerPolynomial
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ) :
    AllocatedCongruenceRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) ℤ
  | .inl x => conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v
      (C (base x.val) + spatialRankPolynomial (fun d => noise (d, x.val)))
  | .inr (.inl i) => conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v
      (modularBoundedCoefficientPolynomial (j.val + 1) (fun q => r j q i))
  | .inr (.inr a) => conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v
      (modularBoundedCoefficientPolynomial (j.val + 1)
        (projection (allocatedCongruenceIntegerEmbedding inactive j a)))

theorem allocatedCongruenceIntegerPolynomial_degree
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o).totalDegree ≤
      j.val + 1 := by
  rcases o with x | i | a
  · apply (conditionPolynomial_totalDegree_le _ _ _ _).trans
    apply (totalDegree_add _ _).trans
    apply max_le
    · rw [totalDegree_C]
      exact Nat.zero_le _
    · exact (spatialRankPolynomial_degree _).trans (by omega)
  · exact (conditionPolynomial_totalDegree_le _ _ _ _).trans
      (modularBoundedCoefficientPolynomial_degree _ _)
  · exact (conditionPolynomial_totalDegree_le _ _ _ _).trans
      (modularBoundedCoefficientPolynomial_degree _ _)

theorem allocatedCongruenceIntegerPolynomial_top_reduce
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (homogeneousComponent (j.val + 1)
      (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o)).map
        (Int.castRingHom (ZMod N)) =
      allocatedOriginalTaggedTop inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
        (fun k => (v k : ZMod N)) (allocatedCongruenceOutputEmbedding inactive j o) := by
  rw [← homogeneousComponent_map_ringHom]
  rcases o with x | i | a
  · have hx : j.val + 1 = 1 := by simp only [x.property, zero_add]
    simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_spatial, allocatedOriginalTaggedTop, hx,
      map_add, map_C, Int.coe_castRingHom]
    have hs : (spatialRankPolynomial (fun d => noise (d, x.val))).map
        (Int.castRingHom (ZMod N)) =
        spatialRankPolynomial (fun d => (noise (d, x.val) : ZMod N)) := by
      simp only [spatialRankPolynomial, map_sum, MvPolynomial.map_monomial,
        Int.coe_castRingHom]
    rw [hs]
    simp only [conditionPolynomial, map_add, polynomialTranslate_C, killCompl_C]
    have hc : homogeneousComponent 1 (C (base x.val : ZMod N) :
        MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N)) = 0 :=
      homogeneousComponent_eq_zero _ _ (by rw [totalDegree_C]; exact zero_lt_one)
    rw [hc, zero_add]
  · simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_deck, allocatedOriginalTaggedTop,
      modularDeckPolynomial, ← modularBoundedCoefficientPolynomial_map,
      Int.coe_castRingHom]
  · simp only [allocatedCongruenceIntegerPolynomial, conditionPolynomial_map,
      allocatedCongruenceOutputEmbedding_integer, allocatedOriginalTaggedTop,
      ← modularBoundedCoefficientPolynomial_map, Int.coe_castRingHom,
      allocatedCongruenceIntegerEmbedding]
    rfl

theorem allocatedCongruenceIntegerPolynomial_top_eq_actual_rank
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ℤ)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    (homogeneousComponent (j.val + 1)
      (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v o)).map
        (Int.castRingHom (ZMod N)) =
      allocatedCongruenceRankPolynomial inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
        spatial kernel block
        (fun z => allocatedSelectedRankCoefficients inactive j (fun q => (noise q : ZMod N))
          (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
          spatial kernel block (allocatedCongruenceOutputEmbedding inactive j z))
        (fun k => (v k : ZMod N)) o := by
  rw [allocatedCongruenceRankPolynomial_original]
  exact allocatedCongruenceIntegerPolynomial_top_reduce N inactive j base noise r projection v o

theorem allocatedCongruenceIntegerPolynomial_spatial_eval
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (base : X → ℤ)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ)
    (y : LayerSamplerLongVariables inactive G B → ℤ) (x : SpatialDegreeOutput X j) :
    MvPolynomial.eval y
      (allocatedCongruenceIntegerPolynomial inactive j base noise r projection v (.inl x)) =
      BooleanCubeKernel.jointIntegerPhysicalSite
        (Function.extend (allocatedLongEmbedding inactive) y v) (base, noise) x.val := by
  rw [allocatedCongruenceIntegerPolynomial, eval_conditionPolynomial]
  exact spatialRankPolynomial_actual_eval base noise x.val _

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)

noncomputable def allocatedCongruenceIntegerSelectedCoefficients :
    AllocatedCongruenceScalarIndex X E inactive L → ℤ
  | ⟨_j, .inl x, l⟩ => noise (spatialKernelRankSlot spatial l, x.val)
  | ⟨j, .inr (.inl i), l⟩ => r j (kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j) l) i
  | ⟨j, .inr (.inr a), l⟩ => projection j (allocatedCongruenceIntegerEmbedding inactive j a)
      (canonicalPrincipalSubblockSlot (layerSamplerDegree I n)
        ⟨j, Sum.inr a.val⟩ (block j (allocatedCongruenceIntegerEmbedding inactive j a)) l)

local notation "selected" => allocatedCongruenceIntegerSelectedCoefficients
  inactive noise r projection spatial kernel block

omit [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ a, Fintype (B a)] in

theorem allocatedCongruenceIntegerSelectedCoefficients_reduce (N : ℕ)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j) (l : Fin L) :
    (selected ⟨j, (o,l)⟩ : ZMod N) =
      allocatedSelectedRankCoefficients inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N)) (fun a q => (projection j a q : ZMod N))
        spatial (kernel j) (block j) (allocatedCongruenceOutputEmbedding inactive j o) l := by
  rcases o with x | i | a <;> rfl

theorem allocatedCongruenceIntegerPolynomial_rank_probability
    (p a : ℕ) [NeZero p] (base : X → ℤ)
    (v : LayerSamplerVariables G I n B → ℤ) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p ^ a)) :
    integerPolynomialRankProbability p a j.val
      (allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v) w =
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod (p ^ a)))
      (fun j q i => (r j q i : ZMod (p ^ a)))
      (fun b q => (projection j b q : ZMod (p ^ a))) spatial (kernel j) (block j)
      (fun o l => (selected ⟨j,(o,l)⟩ : ZMod (p ^ a))) (fun k => (v k : ZMod (p ^ a))) w := by
  unfold integerPolynomialRankProbability allocatedCongruenceRankFailureProbability
  simp only [allocatedCongruenceIntegerSelectedCoefficients_reduce,
    allocatedCongruenceIntegerPolynomial_top_eq_actual_rank
      (p ^ a) inactive j base noise r (projection j) spatial (kernel j) (block j)]
  simp only [polynomialCharacterRow, smul_eq_C_mul]

theorem allocatedCongruenceIntegerPolynomial_rank_of_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p : P) (a : ℕ)
    (hgood : ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a selected)
    (base : X → ℤ) (v : LayerSamplerVariables G I n B → ℤ) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p.val ^ a))
    (hw : ∃ o, IsUnit (w o)) :
    integerPolynomialRankProbability p.val a j.val
      (allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v) w ≤
      (p.val : ℝ) ^ (-C * a) := by
  rw [allocatedCongruenceIntegerPolynomial_rank_probability inactive noise r projection spatial kernel block]
  have h := allocatedCongruenceRankBad_good inactive noise r projection spatial kernel block
    P C p a selected hgood (fun k => (v k : ZMod (p.val ^ a))) j w hw
  calc
    _ ≤ ((p.val ^ a : ℕ) : ℝ) ^ (-C) := h
    _ = (p.val : ℝ) ^ (-C * a) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p.val)]
      congr 1
      ring

theorem allocatedCongruence_crt_characteristic_decay
    (hm : 0 < m) (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (A b e : ℕ → ℕ) (hp : ∀ p ∈ P, p.Prime) (C : ℝ) (hC : 0 ≤ C)
    (hgood : ∀ (p : P) (a : ℕ), b p.val < a → a ≤ A p.val →
      ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
        P C p.val a selected)
    (base : X → ℤ) (v : LayerSamplerVariables G I n B → ℤ)
    (origin : ∀ p : P, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (χ : AddChar (∀ j, AllocatedCongruenceRankOutput X E inactive j →
      ZMod (∏ p : P, p.val ^ A p.val)) ℂ) :
    letI : DecidableEq P := Classical.decEq _
    ‖finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := LayerSamplerLongVariables inactive G B)
        (fun p : P => p.val) (fun p : P => A p.val))
      (crtPrimePowerPolynomialMap (fun p : P => p.val) (fun p : P => A p.val)
        (fun p : P => e p.val)
        (primePower_crt_coprime (fun p : P => p.val) (fun p : P => A p.val)
          (fun p => hp p.val p.property) Subtype.val_injective)
        (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v)
        origin) χ‖ ≤
      crtPolynomialCharge (fun p : P => p.val) (fun p : P => b p.val)
        (fun p : P => e p.val) m C * (orderOf χ : ℝ) ^ (-modularRankDecayExponent m C) := by
  let : DecidableEq P := Classical.decEq _
  apply crt_integer_polynomial_characteristic_decay hm
    (fun p : P => p.val) (fun p : P => A p.val) (fun p : P => b p.val)
    (fun p : P => e p.val) (fun p => hp p.val p.property) Subtype.val_injective C hC
  · exact fun j o => allocatedCongruenceIntegerPolynomial_degree inactive j base noise r (projection j) v o
  · intro p a ha hA j w hw
    exact allocatedCongruenceIntegerPolynomial_rank_of_good inactive noise r projection spatial kernel block
      P C p a (hgood p a ha hA) base v j w hw

theorem allocatedCongruence_largest_bad_depth_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ)
    (p : P) (a : ℕ)
    (ha : largestTestedBadDepth A
      (allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C)
      p.val selected < a) (hA : a ≤ A p.val) :
    ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a selected :=
  largestTestedBadDepth_not_bad A _ p.val selected ha hA

noncomputable def allocatedCongruenceBadDepth
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ) (C : ℝ) : ℕ → ℕ :=
  fun p => largestTestedBadDepth A
    (allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C) p selected

theorem allocatedCongruence_crt_decay_of_bad_product
    (hm : 0 < m) (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (A e : ℕ → ℕ) (hp : ∀ p ∈ P, p.Prime) (C : ℝ) (hC : 0 ≤ C) (R : ℕ)
    (hbad : (∏ p : P, p.val ^ allocatedCongruenceBadDepth
      inactive noise r projection spatial kernel block P A C p.val) ≤ R)
    (base : X → ℤ) (v : LayerSamplerVariables G I n B → ℤ)
    (origin : ∀ p : P, LayerSamplerLongVariables inactive G B → ZMod (p.val ^ A p.val))
    (χ : AddChar (∀ j, AllocatedCongruenceRankOutput X E inactive j →
      ZMod (∏ p : P, p.val ^ A p.val)) ℂ) :
    letI : DecidableEq P := Classical.decEq _
    ‖finiteImageCharacteristic (crtPrimePowerPolynomialLaw (V := LayerSamplerLongVariables inactive G B)
        (fun p : P => p.val) (fun p : P => A p.val))
      (crtPrimePowerPolynomialMap (fun p : P => p.val) (fun p : P => A p.val)
        (fun p : P => e p.val)
        (primePower_crt_coprime (fun p : P => p.val) (fun p : P => A p.val)
          (fun p => hp p.val p.property) Subtype.val_injective)
        (fun j => allocatedCongruenceIntegerPolynomial inactive j base noise r (projection j) v)
        origin) χ‖ ≤
      ((R * ∏ p : P, p.val ^ e p.val : ℕ) : ℝ) ^
        (modularRankDecayExponent m C * modularRankChargeFactor m) *
        (orderOf χ : ℝ) ^ (-modularRankDecayExponent m C) := by
  let : DecidableEq P := Classical.decEq _
  let b := allocatedCongruenceBadDepth inactive noise r projection spatial kernel block P A C
  have h := allocatedCongruence_crt_characteristic_decay inactive noise r projection spatial kernel block
    hm P A b e hp C hC (fun p a ha hA =>
      allocatedCongruence_largest_bad_depth_good inactive noise r projection spatial kernel block
        P A C p a ha hA) base v origin χ
  exact h.trans (mul_le_mul_of_nonneg_right
    (crtPolynomialCharge_le_of_bad_product (fun p : P => p.val) (fun p : P => b p.val)
      (fun p : P => e p.val) m hC hbad) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end Erdos3.VectorPolynomial

end

end OAI
