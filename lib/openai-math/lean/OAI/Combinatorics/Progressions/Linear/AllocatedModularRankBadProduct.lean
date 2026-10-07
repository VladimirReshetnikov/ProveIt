import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankActualRead
import OAI.Combinatorics.Progressions.Linear.SmoothCoefficientRankBadProduct

namespace OAI

section

namespace Erdos3

open MvPolynomial VectorPolynomial
open scoped BigOperators Classical

section RingMap

variable {K L A R S : Type*} [CommRing R] [CommRing S]

theorem homogeneousComponent_map_ringHom (f : R →+* S) (h : ℕ) (P : MvPolynomial K R) :
    homogeneousComponent h (P.map f) = (homogeneousComponent h P).map f := by
  ext a
  simp only [coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp only [map_zero]

theorem modularBoundedCoefficientPolynomial_map [Fintype K]
    (f : R →+* S) (h : ℕ) (c : BoundedCoefficientExponent K h → R) :
    modularBoundedCoefficientPolynomial h (fun e => f (c e)) =
      (modularBoundedCoefficientPolynomial h c).map f := by
  simp only [modularBoundedCoefficientPolynomial, map_sum, MvPolynomial.map_monomial]

theorem modularUnselectedCoefficientPolynomial_map [Fintype K] [Fintype A]
    (f : R →+* S) (h : ℕ) (slot : A → BoundedCoefficientExponent K h)
    (fixed : BoundedCoefficientExponent K h → R) :
    modularUnselectedCoefficientPolynomial h slot (fun e => f (fixed e)) =
      (modularUnselectedCoefficientPolynomial h slot fixed).map f := by
  simp only [modularUnselectedCoefficientPolynomial, map_sum, MvPolynomial.map_monomial]

theorem restrictedUnselectedTop_map [Fintype K] [Fintype A]
    (f : R →+* S) (retained : L → K) (hinj : Function.Injective retained)
    (h : ℕ) (slot : A → BoundedCoefficientExponent K h)
    (fixed : BoundedCoefficientExponent K h → R) :
    killCompl hinj (homogeneousComponent h
      (modularUnselectedCoefficientPolynomial h slot (fun e => f (fixed e)))) =
        (killCompl hinj (homogeneousComponent h
          (modularUnselectedCoefficientPolynomial h slot fixed))).map f := by
  rw [modularUnselectedCoefficientPolynomial_map, homogeneousComponent_map_ringHom,
    killCompl_map]

theorem restrictedMonomialSumTop_map {V : Type*}
    (f : R →+* S) (retained : L → K) (hinj : Function.Injective retained)
    (h : ℕ) (slots : Finset V) (exponent : V → K →₀ ℕ) (fixed : V → R) :
    killCompl hinj (homogeneousComponent h
      (∑ e ∈ slots, monomial (exponent e) (f (fixed e)))) =
        (killCompl hinj (homogeneousComponent h
          (∑ e ∈ slots, monomial (exponent e) (fixed e)))).map f := by
  have hs : (∑ e ∈ slots, monomial (exponent e) (f (fixed e))) =
      (∑ e ∈ slots, monomial (exponent e) (fixed e)).map f := by
    simp only [map_sum, MvPolynomial.map_monomial]
  rw [hs, homogeneousComponent_map_ringHom, killCompl_map]

end RingMap

section ActualResidual

variable {D G R S : Type*} {B : D → Type*} [Fintype D] [Fintype G]
    [∀ d, Fintype (B d)] [CommRing R] [CommRing S]

theorem canonicalSelectedTopResidual_map (f : R →+* S) (h : D → ℕ) (d : D)
    {J : ℕ} (block : Fin J ↪ B d)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d) → R) :
    canonicalSelectedTopResidual h d block (fun e => f (fixed e)) =
      (canonicalSelectedTopResidual h d block fixed).map f := by
  unfold canonicalSelectedTopResidual
  rw [modularUnselectedCoefficientPolynomial_map, homogeneousComponent_map_ringHom]

theorem canonicalSelectedLongTopResidual_map (f : R →+* S)
    (inactive : D → Prop) (h : D → ℕ) (d : {d // ¬ inactive d})
    {J : ℕ} (block : Fin J ↪ B d.val)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d.val) → R) :
    canonicalSelectedLongTopResidual inactive h d block (fun e => f (fixed e)) =
      (canonicalSelectedLongTopResidual inactive h d block fixed).map f := by
  unfold canonicalSelectedLongTopResidual
  rw [canonicalSelectedTopResidual_map, killCompl_map]

theorem canonicalSelectedLongTopResidual_integer_reduce (N : ℕ)
    (inactive : D → Prop) (h : D → ℕ) (d : {d // ¬ inactive d})
    {J : ℕ} (block : Fin J ↪ B d.val)
    (fixed : BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d.val) → ℤ) :
    canonicalSelectedLongTopResidual inactive h d block (fun e => (fixed e : ZMod N)) =
      (canonicalSelectedLongTopResidual inactive h d block fixed).map
        (Int.castRingHom (ZMod N)) :=
  canonicalSelectedLongTopResidual_map (Int.castRingHom (ZMod N)) inactive h d block fixed

end ActualResidual
end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]
    {L : ℕ}

noncomputable def allocatedTaggedRankIntegerResidual
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩) :
    AllocatedTaggedRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) ℤ
  | .inl x => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent 1
        (∑ d ∈ Finset.univ.filter (fun d => d ∉ Set.range
          (spatialKernelRankSlot (P := PrincipalTupleIndex B (layerSamplerDegree I n)) spatial)),
          MvPolynomial.monomial (spatialRankExponent d) (noise (d,x.val))))
  | .inr (.inl i) => killCompl (allocatedLongEmbedding inactive).injective
      (homogeneousComponent (j.val + 1)
        (modularUnselectedCoefficientPolynomial (j.val + 1)
          (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel) (fun q => r j q i)))
  | .inr (.inr a) => canonicalSelectedLongTopResidual inactive (layerSamplerDegree I n)
      (allocatedDegreeLongAxis inactive j a) (block a) (projection a)

theorem allocatedTaggedRankIntegerResidual_reduce
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    (allocatedTaggedRankIntegerResidual inactive j noise r projection spatial kernel block o).map
        (Int.castRingHom (ZMod N)) =
      allocatedTaggedRankResidual inactive j (fun q => (noise q : ZMod N))
        (fun j q i => (r j q i : ZMod N))
        (fun a q => (projection a q : ZMod N)) spatial kernel block o := by
  cases o with
  | inl x =>
    exact (restrictedMonomialSumTop_map (Int.castRingHom (ZMod N))
      (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective 1
      (Finset.univ.filter (fun d => d ∉ Set.range
        (spatialKernelRankSlot (P := PrincipalTupleIndex B (layerSamplerDegree I n)) spatial)))
      spatialRankExponent (fun d => noise (d,x.val))).symm
  | inr o =>
    cases o with
    | inl i =>
      exact (restrictedUnselectedTop_map (Int.castRingHom (ZMod N))
        (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective
        (j.val + 1) (kernelRankCoefficientSlot (layerSamplerDegree I n) kernel)
        (fun q => r j q i)).symm
    | inr a =>
      exact (canonicalSelectedLongTopResidual_integer_reduce N inactive (layerSamplerDegree I n)
        (allocatedDegreeLongAxis inactive j a) (block a) (projection a)).symm

theorem allocatedTaggedRankPolynomial_eq_integer_designated
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedTaggedRankOutput X E inactive j) :
    allocatedTaggedRankPolynomial inactive j (fun q => (noise q : ZMod N))
      (fun j q i => (r j q i : ZMod N)) (fun a q => (projection a q : ZMod N))
      spatial kernel block c v o =
        designatedVectorComponent (allocatedTaggedRankBlock inactive j spatial kernel block)
          (fun o => (allocatedTaggedRankIntegerResidual inactive j noise r projection
            spatial kernel block o).map (Int.castRingHom (ZMod N))) c o := by
  simp only [allocatedTaggedRankIntegerResidual_reduce,
    allocatedTaggedRankPolynomial_eq_designated]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable def allocatedTaggedRankFailureProbability {N L : ℕ} [NeZero N]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (w : AllocatedTaggedRankOutput X E inactive j → ZMod N) : ℝ :=
  𝔼 u : Fin j.val → LayerSamplerLongVariables inactive G B → ZMod N,
    if polynomialLinearRow (polynomialIterDifference j.val
      (∑ o, w o • allocatedTaggedRankPolynomial inactive j noise r projection
        spatial kernel block c v o) u) = 0 then 1 else 0

theorem allocatedTaggedRankFailureProbability_eq_designated {N L : ℕ} [NeZero N]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (c : AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (w : AllocatedTaggedRankOutput X E inactive j → ZMod N) :
    allocatedTaggedRankFailureProbability inactive j noise r projection spatial kernel block c v w =
      vectorDesignatedRankFailureProbability N j.val
        (allocatedTaggedRankBlock inactive j spatial kernel block)
        (allocatedTaggedRankResidual inactive j noise r projection spatial kernel block) w c := by
  unfold allocatedTaggedRankFailureProbability vectorDesignatedRankFailureProbability
  simp only [allocatedTaggedRankPolynomial_eq_designated]

theorem allocatedTaggedRank_exceptional_probability {p a L D : ℕ} [NeZero p]
    (hm : 0 < m) (hp : p.Prime) (ha : 0 < a)
    (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod (p ^ a))
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E (p ^ a))
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod (p ^ a))
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (v : LayerSamplerVariables G I n B → ZMod (p ^ a))
    (hD : Fintype.card X + ∑ j : Fin m,
      (Fintype.card (E j) + Fintype.card (I j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hq : max 2 ((m : ℝ) ^ (4 / modularRankSmallBallExponent m)) ≤ (p : ℝ) ^ a)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L) :
    (FiniteProbabilityWeights.uniform
      (∀ j : Fin m, AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod (p ^ a))).eventProbability
      (fun c => ∃ j : Fin m, ∃ w : AllocatedTaggedRankOutput X E inactive j → ZMod (p ^ a),
        (∃ o, IsUnit (w o)) ∧ ((p : ℝ) ^ a) ^ (-C) <
          allocatedTaggedRankFailureProbability inactive j noise r (projection j)
            spatial (kernel j) (block j) (c j) v w) ≤
        ((p : ℝ) ^ a) ^ (-(10 : ℝ)) := by
  have hcount (j : Fin m) : Fintype.card (AllocatedTaggedRankOutput X E inactive j) ≤ D :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      ((allocatedTaggedRankOutput_sum_card_le (X := X) (E := E) hm inactive).trans hD)
  have h := taggedVectorDesignatedRank_exceptional_probability
    (T := Fin m) (A := Fin L) (I := LayerSamplerLongVariables inactive G B)
    (B := AllocatedTaggedRankOutput X E inactive) (s := m) (m := D) hp ha
    (fun j => j.val) (fun j => Nat.succ_le_of_lt j.isLt) (by simp only [Fintype.card_fin, le_refl]) hcount
    (fun j => allocatedTaggedRankBlock inactive j spatial (kernel j) (block j))
    (fun j => allocatedTaggedRankResidual inactive j noise r (projection j)
      spatial (kernel j) (block j))
    (fun j => allocatedTaggedRankBlock_card inactive j spatial (kernel j) (block j))
    (fun j => allocatedTaggedRankBlock_disjoint inactive j spatial (kernel j) (block j))
    hC hq (by simpa only [Fintype.card_fin] using hL)
  simpa only [allocatedTaggedRankFailureProbability_eq_designated] using h

theorem allocatedTaggedRank_exceptional_probability_uniform {p a L D : ℕ} [NeZero p]
    (hm : 0 < m) (hp : p.Prime) (ha : 0 < a)
    (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod (p ^ a))
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E (p ^ a))
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod (p ^ a))
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (hD : Fintype.card X + ∑ j : Fin m,
      (Fintype.card (E j) + Fintype.card (I j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hq : max 2 ((m : ℝ) ^ (4 / modularRankSmallBallExponent m)) ≤ (p : ℝ) ^ a)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L) :
    (FiniteProbabilityWeights.uniform
      (∀ j : Fin m, AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod (p ^ a))).eventProbability
      (fun c => ∃ v : LayerSamplerVariables G I n B → ZMod (p ^ a),
        ∃ j : Fin m, ∃ w : AllocatedTaggedRankOutput X E inactive j → ZMod (p ^ a),
        (∃ o, IsUnit (w o)) ∧ ((p : ℝ) ^ a) ^ (-C) <
          allocatedTaggedRankFailureProbability inactive j noise r (projection j)
            spatial (kernel j) (block j) (c j) v w) ≤
        ((p : ℝ) ^ a) ^ (-(10 : ℝ)) := by
  have h := allocatedTaggedRank_exceptional_probability hm hp ha inactive noise r projection
    spatial kernel block (fun _ => 0) hD hC hq hL
  apply le_trans ?_ h
  apply FiniteProbabilityWeights.eventProbability_mono
  intro c hc
  obtain ⟨v, j, w, hw, hbad⟩ := hc
  refine ⟨j, w, hw, ?_⟩
  simpa only [allocatedTaggedRankFailureProbability_eq_designated] using hbad

noncomputable def allocatedCongruenceRankPolynomial {N L : ℕ}
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (c : AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    MvPolynomial (LayerSamplerLongVariables inactive G B) (ZMod N) :=
  allocatedTaggedRankPolynomial inactive j noise r projection spatial kernel block
    (Function.extend (allocatedCongruenceOutputEmbedding inactive j) c (fun _ _ => 0)) v
    (allocatedCongruenceOutputEmbedding inactive j o)

omit [Fintype X] [∀ j, Fintype (E j)] in

theorem allocatedCongruenceRankPolynomial_eq_actual {N L : ℕ}
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (c : AllocatedTaggedRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    allocatedCongruenceRankPolynomial inactive j noise r projection spatial kernel block
      (fun o => c (allocatedCongruenceOutputEmbedding inactive j o)) v o =
      allocatedTaggedRankPolynomial inactive j noise r projection spatial kernel block c v
        (allocatedCongruenceOutputEmbedding inactive j o) := by
  unfold allocatedCongruenceRankPolynomial
  simp only [allocatedTaggedRankPolynomial_eq_designated, designatedVectorComponent,
    (allocatedCongruenceOutputEmbedding (X := X) (E := E) inactive j).injective.extend_apply]

noncomputable def allocatedCongruenceRankFailureProbability {N L : ℕ} [NeZero N]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (c : AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) : ℝ :=
  𝔼 u : Fin j.val → LayerSamplerLongVariables inactive G B → ZMod N,
    if polynomialLinearRow (polynomialIterDifference j.val
      (∑ o, w o • allocatedCongruenceRankPolynomial inactive j noise r projection
        spatial kernel block c v o) u) = 0 then 1 else 0

theorem allocatedCongruenceRankFailureProbability_eq_designated {N L : ℕ} [NeZero N]
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (c : AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) :
    allocatedCongruenceRankFailureProbability inactive j noise r projection spatial kernel block c v w =
      vectorDesignatedRankFailureProbability N j.val
        (fun o => allocatedTaggedRankBlock inactive j spatial kernel block
          (allocatedCongruenceOutputEmbedding inactive j o))
        (fun o => allocatedTaggedRankResidual inactive j noise r projection spatial kernel block
          (allocatedCongruenceOutputEmbedding inactive j o)) w c := by
  unfold allocatedCongruenceRankFailureProbability vectorDesignatedRankFailureProbability
    allocatedCongruenceRankPolynomial
  simp only [allocatedTaggedRankPolynomial_eq_designated, designatedVectorComponent,
    (allocatedCongruenceOutputEmbedding (X := X) (E := E) inactive j).injective.extend_apply]

theorem allocatedCongruenceRank_exceptional_probability {p a L D : ℕ} [NeZero p]
    (hm : 0 < m) (hp : p.Prime) (ha : 0 < a)
    (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod (p ^ a))
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E (p ^ a))
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod (p ^ a))
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (v : LayerSamplerVariables G I n B → ZMod (p ^ a))
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hq : max 2 ((m : ℝ) ^ (4 / modularRankSmallBallExponent m)) ≤ (p : ℝ) ^ a)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L) :
    (FiniteProbabilityWeights.uniform
      (∀ j : Fin m, AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod (p ^ a))).eventProbability
      (fun c => ∃ j : Fin m, ∃ w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p ^ a),
        (∃ o, IsUnit (w o)) ∧ ((p : ℝ) ^ a) ^ (-C) <
          allocatedCongruenceRankFailureProbability inactive j noise r (projection j)
            spatial (kernel j) (block j) (c j) v w) ≤
        ((p : ℝ) ^ a) ^ (-(10 : ℝ)) := by
  have hcount (j : Fin m) : Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤ D :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      ((allocatedCongruenceRankOutput_sum_card_le (X := X) (E := E) hm inactive).trans hD)
  have h := taggedVectorDesignatedRank_exceptional_probability
    (T := Fin m) (A := Fin L) (I := LayerSamplerLongVariables inactive G B)
    (B := AllocatedCongruenceRankOutput X E inactive) (s := m) (m := D) hp ha
    (fun j => j.val) (fun j => Nat.succ_le_of_lt j.isLt)
    (by simp only [Fintype.card_fin, le_refl]) hcount
    (fun j o => allocatedTaggedRankBlock inactive j spatial (kernel j) (block j)
      (allocatedCongruenceOutputEmbedding inactive j o))
    (fun j o => allocatedTaggedRankResidual inactive j noise r (projection j)
      spatial (kernel j) (block j) (allocatedCongruenceOutputEmbedding inactive j o))
    (fun j o => allocatedTaggedRankBlock_card inactive j spatial (kernel j) (block j)
      (allocatedCongruenceOutputEmbedding inactive j o))
    (fun j o => allocatedTaggedRankBlock_disjoint inactive j spatial (kernel j) (block j)
      (allocatedCongruenceOutputEmbedding inactive j o))
    hC hq (by simpa only [Fintype.card_fin] using hL)
  simpa only [allocatedCongruenceRankFailureProbability_eq_designated] using h

theorem allocatedCongruenceRank_exceptional_probability_uniform {p a L D : ℕ} [NeZero p]
    (hm : 0 < m) (hp : p.Prime) (ha : 0 < a)
    (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod (p ^ a))
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E (p ^ a))
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod (p ^ a))
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hq : max 2 ((m : ℝ) ^ (4 / modularRankSmallBallExponent m)) ≤ (p : ℝ) ^ a)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L) :
    (FiniteProbabilityWeights.uniform
      (∀ j : Fin m, AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod (p ^ a))).eventProbability
      (fun c => ∃ v : LayerSamplerVariables G I n B → ZMod (p ^ a),
        ∃ j : Fin m, ∃ w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p ^ a),
        (∃ o, IsUnit (w o)) ∧ ((p : ℝ) ^ a) ^ (-C) <
          allocatedCongruenceRankFailureProbability inactive j noise r (projection j)
            spatial (kernel j) (block j) (c j) v w) ≤
        ((p : ℝ) ^ a) ^ (-(10 : ℝ)) := by
  have h := allocatedCongruenceRank_exceptional_probability hm hp ha inactive noise r projection
    spatial kernel block (fun _ => 0) hD hC hq hL
  apply le_trans ?_ h
  apply FiniteProbabilityWeights.eventProbability_mono
  intro c hc
  obtain ⟨v, j, w, hw, hbad⟩ := hc
  refine ⟨j, w, hw, ?_⟩
  simpa only [allocatedCongruenceRankFailureProbability_eq_designated] using hbad

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

abbrev AllocatedCongruenceScalarIndex (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, AllocatedCongruenceRankOutput X E inactive j × Fin L

def allocatedCongruenceRankBlockFamily (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩) :
    ∀ j, AllocatedCongruenceRankOutput X E inactive j → Fin L →
      Finset (LayerSamplerLongVariables inactive G B) :=
  fun j o => allocatedTaggedRankBlock inactive j spatial (kernel j) (block j)
    (allocatedCongruenceOutputEmbedding inactive j o)

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable def allocatedCongruenceRankIntegerResidualFamily
    (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩) :
    ∀ j, AllocatedCongruenceRankOutput X E inactive j →
      MvPolynomial (LayerSamplerLongVariables inactive G B) ℤ :=
  fun j o => allocatedTaggedRankIntegerResidual inactive j noise r (projection j)
    spatial (kernel j) (block j) (allocatedCongruenceOutputEmbedding inactive j o)

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

local notation "rankS" => allocatedCongruenceRankBlockFamily (X := X) (E := E) inactive spatial kernel block
local notation "rankQ" => allocatedCongruenceRankIntegerResidualFamily inactive noise r projection spatial kernel block

theorem allocatedCongruenceRankFailureProbability_eq_integer_model
    (N : ℕ) [NeZero N] (x : AllocatedCongruenceScalarIndex X E inactive L → ZMod N)
    (v : LayerSamplerVariables G I n B → ZMod N) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) :
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod N))
      (fun j q i => (r j q i : ZMod N)) (fun b q => (projection j b q : ZMod N))
      spatial (kernel j) (block j) (fun o l => x ⟨j, (o,l)⟩) v w =
      vectorDesignatedRankFailureProbability N j.val (rankS j)
        (fun o => (rankQ j o).map (Int.castRingHom (ZMod N))) w
        (fun o l => x ⟨j, (o,l)⟩) := by
  rw [allocatedCongruenceRankFailureProbability_eq_designated]
  simp only [allocatedCongruenceRankIntegerResidualFamily,
    allocatedTaggedRankIntegerResidual_reduce]
  rfl

def allocatedCongruenceModulusBad (C : ℝ) (N : ℕ) [NeZero N]
    (x : AllocatedCongruenceScalarIndex X E inactive L → ZMod N) : Prop :=
  ∃ v : LayerSamplerVariables G I n B → ZMod N, ∃ j : Fin m,
    ∃ w : AllocatedCongruenceRankOutput X E inactive j → ZMod N,
      (∃ o, IsUnit (w o)) ∧ (N : ℝ) ^ (-C) <
        allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod N))
          (fun j q i => (r j q i : ZMod N)) (fun b q => (projection j b q : ZMod N))
          spatial (kernel j) (block j) (fun o l => x ⟨j,(o,l)⟩) v w

theorem allocatedCongruenceModulusBad_iff_scalarCoefficientBad
    (C : ℝ) (N : ℕ) [NeZero N]
    (x : AllocatedCongruenceScalarIndex X E inactive L → ZMod N) :
    allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C N x ↔
      scalarCoefficientBad (fun j : Fin m => j.val) rankS rankQ C N x := by
  unfold allocatedCongruenceModulusBad scalarCoefficientBad
  simp only [allocatedCongruenceRankFailureProbability_eq_integer_model]
  constructor
  · rintro ⟨v, j, w, hw, hbad⟩
    exact ⟨j, w, hw, hbad⟩
  · rintro ⟨j, w, hw, hbad⟩
    exact ⟨fun _ => 0, j, w, hw, hbad⟩

def allocatedCongruenceRankBad (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) :
    ℕ → ℕ → (AllocatedCongruenceScalarIndex X E inactive L → ℤ) → Prop :=
  smoothResiduePrimeBad P (fun p a =>
    allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C (p.val ^ a))

theorem allocatedCongruenceRankBad_eq_smoothCoefficientRankBad
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) :
    allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C =
      smoothCoefficientRankBad P (fun j : Fin m => j.val) rankS rankQ C := by
  funext p a x
  apply propext
  unfold allocatedCongruenceRankBad smoothCoefficientRankBad smoothResiduePrimeBad
  apply exists_congr
  intro hp
  let : NeZero p := inferInstanceAs (NeZero (⟨p, hp⟩ : P).val)
  exact allocatedCongruenceModulusBad_iff_scalarCoefficientBad
    inactive noise r projection spatial kernel block C (p ^ a) _

theorem allocatedCongruenceModulusBad_good (C : ℝ) (N : ℕ) [NeZero N]
    (x : AllocatedCongruenceScalarIndex X E inactive L → ZMod N)
    (hgood : ¬ allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C N x)
    (v : LayerSamplerVariables G I n B → ZMod N) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) (hw : ∃ o, IsUnit (w o)) :
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod N))
      (fun j q i => (r j q i : ZMod N)) (fun b q => (projection j b q : ZMod N))
      spatial (kernel j) (block j) (fun o l => x ⟨j,(o,l)⟩) v w ≤ (N : ℝ) ^ (-C) :=
  le_of_not_gt (fun hbad => hgood ⟨v, j, w, hw, hbad⟩)

theorem allocatedCongruenceRankBad_good
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ)
    (p : P) (a : ℕ) (x : AllocatedCongruenceScalarIndex X E inactive L → ℤ)
    (hgood : ¬ allocatedCongruenceRankBad inactive noise r projection spatial kernel block
      P C p.val a x)
    (v : LayerSamplerVariables G I n B → ZMod (p.val ^ a)) (j : Fin m)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod (p.val ^ a))
    (hw : ∃ o, IsUnit (w o)) :
    allocatedCongruenceRankFailureProbability inactive j (fun q => (noise q : ZMod (p.val ^ a)))
      (fun j q i => (r j q i : ZMod (p.val ^ a)))
      (fun b q => (projection j b q : ZMod (p.val ^ a)))
      spatial (kernel j) (block j) (fun o l => (x ⟨j,(o,l)⟩ : ZMod (p.val ^ a))) v w ≤
        ((p.val ^ a : ℕ) : ℝ) ^ (-C) := by
  have hmod : ¬ allocatedCongruenceModulusBad inactive noise r projection spatial kernel block
      C (p.val ^ a) (fun i => (x i : ZMod (p.val ^ a))) :=
    fun hbad => hgood ⟨p.property, hbad⟩
  exact allocatedCongruenceModulusBad_good inactive noise r projection spatial kernel block C
    (p.val ^ a) (fun i => (x i : ZMod (p.val ^ a))) hmod v j w hw

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}
    [Fintype G] [∀ j, Fintype (I j)]
    [∀ a, Fintype (B a)] {N L : ℕ}

theorem allocatedCongruenceRankPolynomial_original
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (noise : Option (LayerSamplerVariables G I n B) × X → ZMod N)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E N)
    (projection : AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ZMod N)
    (spatial : Fin L ↪ G) (kernel : Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, a.val⟩)
    (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    allocatedCongruenceRankPolynomial inactive j noise r projection spatial kernel block
      (fun z => allocatedSelectedRankCoefficients inactive j noise r projection spatial kernel block
        (allocatedCongruenceOutputEmbedding inactive j z)) v o =
      allocatedOriginalTaggedTop inactive j noise r projection v
        (allocatedCongruenceOutputEmbedding inactive j o) := by
  rw [allocatedCongruenceRankPolynomial, allocatedTaggedRankPolynomial_eq_designated,
    allocatedOriginalTaggedTop_eq_designated inactive j noise r projection spatial kernel block]
  simp only [designatedVectorComponent,
    (allocatedCongruenceOutputEmbedding (X := X) (E := E) inactive j).injective.extend_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

private theorem uniform_eventProbability_le_instances (Y : Type*) (f g : Fintype Y)
    [Nonempty Y] (A : Y → Prop) (r : ℝ)
    (h : @FiniteProbabilityWeights.eventProbability Y f
      (@FiniteProbabilityWeights.uniform Y f _) A ≤ r) :
    @FiniteProbabilityWeights.eventProbability Y g
      (@FiniteProbabilityWeights.uniform Y g _) A ≤ r := by
  cases Subsingleton.elim f g
  exact h

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance congruenceScalarFintype
    (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedCongruenceScalarIndex X E inactive L) := inferInstance

noncomputable local instance congruenceScalarDecidableEq
    (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedCongruenceScalarIndex X E inactive L) := Classical.decEq _

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

local notation "rankS" => allocatedCongruenceRankBlockFamily (X := X) (E := E) inactive spatial kernel block
local notation "rankQ" => allocatedCongruenceRankIntegerResidualFamily inactive noise r projection spatial kernel block

theorem allocatedCongruenceModulusBad_probability {p a D : ℕ} [NeZero p]
    (hm : 0 < m) (hp : p.Prime) (ha : 0 < a)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hlarge : modularCoefficientPrimeThreshold m ≤ p ^ a)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L) :
    (FiniteProbabilityWeights.uniform
      (AllocatedCongruenceScalarIndex (I := I) (n := n) X E inactive L → ZMod (p ^ a))).eventProbability
      (allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C (p ^ a)) ≤
        1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  have hcount (j : Fin m) : Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤ D :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      ((allocatedCongruenceRankOutput_sum_card_le (X := X) (E := E) hm inactive).trans hD)
  have h := scalarCoefficientBad_probability
    (T := Fin m) (D := Fin L) (I := LayerSamplerLongVariables inactive G B)
    (B := AllocatedCongruenceRankOutput X E inactive) (s := m) (m := D) hp ha
    (fun j => j.val) (fun j => Nat.succ_le_of_lt j.isLt)
    (by simp only [Fintype.card_fin, le_refl]) hcount rankS rankQ
    (fun j o => allocatedTaggedRankBlock_card inactive j spatial (kernel j) (block j)
      (allocatedCongruenceOutputEmbedding inactive j o))
    (fun j o => allocatedTaggedRankBlock_disjoint inactive j spatial (kernel j) (block j)
      (allocatedCongruenceOutputEmbedding inactive j o))
    hC hlarge (by simpa only [Fintype.card_fin] using hL)
  have heq : allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C (p ^ a) =
      scalarCoefficientBad (fun j : Fin m => j.val) rankS rankQ C (p ^ a) := by
    funext x
    exact propext (allocatedCongruenceModulusBad_iff_scalarCoefficientBad
      inactive noise r projection spatial kernel block C (p ^ a) x)
  rw [heq]
  exact uniform_eventProbability_le_instances _ _ _ _ _ h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

private theorem mixed_uniform_eventProbability_le_instances (Y : Type*) (f g : Fintype Y)
    [Nonempty Y] (F : Y → Prop) (r : ℝ)
    (h : @eventProbability Y f (@uniform Y f _) F ≤ r) :
    @eventProbability Y g (@uniform Y g _) F ≤ r := by
  cases Subsingleton.elim f g
  exact h

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance badProductSmoothIndexFintype (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedSmoothRankCoefficientIndex X inactive L) := inferInstance
noncomputable local instance badProductDeckIndexFintype :
    Fintype (AllocatedDeckRankCoefficientIndex E L) := inferInstance
noncomputable local instance badProductDeckIndexDecidableEq :
    DecidableEq (AllocatedDeckRankCoefficientIndex E L) := Classical.decEq _
noncomputable local instance badProductCongruenceIndexFintype (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedCongruenceCoefficientIndex X E inactive L) := inferInstance
noncomputable local instance badProductCongruenceIndexDecidableEq (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedCongruenceCoefficientIndex X E inactive L) := Classical.decEq _

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

def allocatedMixedModulusBad (C : ℝ) (M : ℕ) [NeZero M]
    (x : (AllocatedSmoothRankCoefficientIndex X inactive L ⊕
      AllocatedDeckRankCoefficientIndex E L) → ZMod M) : Prop :=
  allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C M
    (allocatedMixedCoefficientEquiv inactive L (ZMod M) x)

theorem allocatedMixedModulusBad_probability {p a D : ℕ} [NeZero p]
    (hm : 0 < m) (hp : p.Prime) (ha : 0 < a)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hlarge : modularCoefficientPrimeThreshold m ≤ p ^ a)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L) :
    (uniform ((AllocatedSmoothRankCoefficientIndex X inactive L ⊕
      AllocatedDeckRankCoefficientIndex E L) → ZMod (p ^ a))).eventProbability
        (allocatedMixedModulusBad inactive noise r projection spatial kernel block C (p ^ a)) ≤
      1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  have he := allocatedMixedCoefficient_uniform_event (X := X) (E := E) inactive L (p ^ a)
    (allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C (p ^ a))
  have hs := allocatedCongruenceModulusBad_probability inactive noise r projection spatial kernel block
    hm hp ha hD hC hlarge hL
  have hb := he.le.trans (mixed_uniform_eventProbability_le_instances _ _ _ _ _ hs)
  exact mixed_uniform_eventProbability_le_instances _ _ _ _ _ hb

theorem allocatedMixedRankBad_eq {N : ℕ} [NeZero N]
    (P : Finset ℕ) [∀ p : P, NeZero p.val] (C : ℝ) (p a : ℕ)
    (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    mixedSmoothUniformResiduePrimeBad P
      (fun p a => allocatedMixedModulusBad inactive noise r projection spatial kernel block C (p.val ^ a))
      p a (x,deck) =
    allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C p a
      (allocatedMixedSelectedValues inactive x deck) := by
  unfold mixedSmoothUniformResiduePrimeBad allocatedCongruenceRankBad smoothResiduePrimeBad
  simp only [allocatedMixedModulusBad, allocatedMixedCoefficientEquiv_cast]

theorem allocatedMixedRank_primePower_event {N D : ℕ} [NeZero N]
    (hm : 0 < m)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width j) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
      (fun x => ∀ p : P, allocatedCongruenceModulusBad inactive noise r projection spatial kernel block
        C (p.val ^ A p.val) (fun j =>
          (allocatedMixedSelectedValues inactive x.1.val x.2 j : ZMod (p.val ^ A p.val)))) ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
          (∏ p : P, p.val ^ A p.val) / width j := by
  have h := mixedSmoothUniform_primePower_event (N := N) center width hwidth hZ P A
    hprime hcover
    (fun p => allocatedMixedModulusBad inactive noise r projection spatial kernel block C (p.val ^ A p.val))
    (fun p => by
      have ht := allocatedMixedModulusBad_probability inactive noise r projection spatial kernel block
        hm (hprime p p.property) (hpositive p p.property) hD hC (hthreshold p p.property) hL
      exact mixed_uniform_eventProbability_le_instances _ _ _ _ _ ht)
    hlarge
  simpa only [allocatedMixedModulusBad, allocatedMixedCoefficientEquiv_cast] using h

theorem allocatedMixedRank_bad_product_probability {N D Q R : ℕ} [NeZero N]
    (hm : 0 < m)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hQ : 1 ≤ Q) (hR : 0 < R) (hdepth : ∀ p ∈ P, p ^ A p ≤ Q)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (max Q (R ^ 2) : ℕ) ≤ width j)
    {η : ℝ} (hη : 0 ≤ η)
    (herror : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
      (max Q (R ^ 2) : ℕ) / width j) ≤ η) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
      (fun x => smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * R <
        ∏ p ∈ P, p ^ largestTestedBadDepth A
          (fun p a x => allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C
            p a (allocatedMixedSelectedValues inactive x.1.val x.2)) p x) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Q : ℝ) + (R : ℝ) ^ 2) * η := by
  have h := mixedSmoothUniform_badPrimeProduct_probability (N := N)
    center width hwidth hZ P A
    (fun p a => allocatedMixedModulusBad inactive noise r projection spatial kernel block C (p.val ^ a))
    hprime hcover (modularCoefficientPrimeThreshold_two_le m) hQ hR hdepth
    (fun p a ha _had hlarge => by
      have ht := allocatedMixedModulusBad_probability
        inactive noise r projection spatial kernel block hm (hprime p p.property) ha hD hC hlarge hL
      exact mixed_uniform_eventProbability_le_instances _ _ _ _ _ ht)
    hlarge hη herror
  simpa only [allocatedMixedRankBad_eq] using h

theorem exists_early_allocatedMixedRank_bad_product_cutoff {D : ℕ}
    (hm : 0 < m)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ (Q N : ℕ) [NeZero N]
      (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
      (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
      (r : ∀ j : Fin m,
        BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
      (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
        BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
      (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
      (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width),
      1 ≤ Q → (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ^ A p ∣ N) →
      (∀ p ∈ P, p ^ A p ≤ Q) →
      (∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (max Q (R ^ 2) : ℕ) ≤ width j) →
      (∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (max Q (R ^ 2) : ℕ) / width j) ≤
        δ / (2 * ((Q : ℝ) + (R : ℝ) ^ 2)) →
      ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
        (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
        (fun x => smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * R <
          ∏ p ∈ P, p ^ largestTestedBadDepth A
            (fun p a x => allocatedCongruenceRankBad inactive noise r projection spatial kernel block P C
              p a (allocatedMixedSelectedValues inactive x.1.val x.2)) p x) ≤ δ := by
  obtain ⟨R, hR, hradius⟩ := exists_early_badPrime_radius hδ
  refine ⟨R, hR, ?_⟩
  intro Q N _ P A _ noise r projection center width hwidth hZ hQ hprime hcover hdepth hlarge herror
  exact (allocatedMixedRank_bad_product_probability inactive noise r projection spatial kernel block
    hm center width hwidth hZ P A hprime hcover hQ hR hdepth hD hC hL hlarge
    (hradius Q hQ).1.le herror).trans (hradius Q hQ).2

end Erdos3.VectorPolynomial

end

end OAI
