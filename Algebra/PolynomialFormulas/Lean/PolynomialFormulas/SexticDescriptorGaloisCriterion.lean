import PolynomialFormulas.SexticScalarGaloisBridge
import PolynomialFormulas.SexticSeparatingInvariants

/-!
# Collision-free descriptor criterion for irreducible sextics

For an irreducible rational sextic, the Galois group is solvable exactly when
one pair- or triple-partition descriptor has all coefficients in the rational
base field.  Unlike a single specialized scalar invariant, the descriptor
cannot acquire accidental collisions because the six roots are distinct.
-/

open scoped Polynomial
open Polynomial

namespace LeanProofs.PolynomialFormulas.SexticDescriptorGaloisCriterion

open Fin6BlockSystems
open SexticScalarGaloisBridge
open SexticSeparatingInvariants

/-- Every coefficient of a splitting-field polynomial belongs to the rational
base field. -/
def CoefficientsRational (p : ℚ[X])
    (d : Polynomial (Polynomial p.SplittingField)) : Prop :=
  ∀ m n, (d.coeff m).coeff n ∈
    Set.range (algebraMap ℚ p.SplittingField)

theorem coefficientsRational_iff_gal_fixed
    (p : ℚ[X]) (hp : Irreducible p)
    (d : Polynomial (Polynomial p.SplittingField)) :
    CoefficientsRational p d ↔
      ∀ σ : p.Gal, d.map (Polynomial.mapRingHom σ.toRingHom) = d := by
  constructor
  · intro h σ
    ext m n
    simp only [Polynomial.coeff_map]
    rw [show (Polynomial.mapRingHom σ.toRingHom) (d.coeff m) =
      (d.coeff m).map σ.toRingHom by rfl, Polynomial.coeff_map]
    obtain ⟨q, hq⟩ := h m n
    rw [← hq]
    exact σ.commutes q
  · intro h m n
    rw [mem_range_algebraMap_iff_gal_fixed p hp]
    intro σ
    have hm := congrArg
      (fun d : Polynomial (Polynomial p.SplittingField) ↦ d.coeff m) (h σ)
    simp only [Polynomial.coeff_map] at hm
    rw [show (Polynomial.mapRingHom σ.toRingHom) (d.coeff m) =
      (d.coeff m).map σ.toRingHom by rfl] at hm
    have hn := congrArg (fun d : Polynomial p.SplittingField ↦ d.coeff n) hm
    simp only [Polynomial.coeff_map] at hn
    change σ.toRingEquiv.toRingHom ((d.coeff m).coeff n) =
      (d.coeff m).coeff n
    exact hn

theorem gal_map_pairDescriptor
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6)
    (σ : p.Gal) (b : PairPartition) :
    (pairDescriptor (rootTuple p hp hdeg) b).map
        (Polynomial.mapRingHom σ.toRingHom) =
      pairDescriptor
        (fun i ↦ rootTuple p hp hdeg
          (rootPermutationHom p hp hdeg σ i)) b := by
  rw [pairDescriptor, descriptor_map]
  congr 2
  funext i
  exact gal_maps_rootTuple p hp hdeg σ i

theorem gal_map_tripleDescriptor
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6)
    (σ : p.Gal) (b : TriplePartition) :
    (tripleDescriptor (rootTuple p hp hdeg) b).map
        (Polynomial.mapRingHom σ.toRingHom) =
      tripleDescriptor
        (fun i ↦ rootTuple p hp hdeg
          (rootPermutationHom p hp hdeg σ i)) b := by
  rw [tripleDescriptor, descriptor_map]
  congr 2
  funext i
  exact gal_maps_rootTuple p hp hdeg σ i

theorem pairDescriptor_coefficientsRational_iff_le_stabilizer
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6)
    (b : PairPartition) :
    CoefficientsRational p (pairDescriptor (rootTuple p hp hdeg) b) ↔
      rootPermutationGroup p hp hdeg ≤ pairStabilizer b := by
  rw [coefficientsRational_iff_gal_fixed p hp]
  constructor
  · intro h g hg
    rcases hg with ⟨σ, rfl⟩
    change Preserves (pairLabel b) (rootPermutationHom p hp hdeg σ)
    apply (pairDescriptor_permute_eq_self_iff
      (rootTuple p hp hdeg) (rootTuple_injective p hp hdeg) b _).1
    rw [← gal_map_pairDescriptor p hp hdeg σ b]
    exact h σ
  · intro h σ
    rw [gal_map_pairDescriptor p hp hdeg σ b]
    apply (pairDescriptor_permute_eq_self_iff
      (rootTuple p hp hdeg) (rootTuple_injective p hp hdeg) b _).2
    exact h ⟨σ, rfl⟩

theorem tripleDescriptor_coefficientsRational_iff_le_stabilizer
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6)
    (b : TriplePartition) :
    CoefficientsRational p (tripleDescriptor (rootTuple p hp hdeg) b) ↔
      rootPermutationGroup p hp hdeg ≤ tripleStabilizer b := by
  rw [coefficientsRational_iff_gal_fixed p hp]
  constructor
  · intro h g hg
    rcases hg with ⟨σ, rfl⟩
    change Preserves (tripleLabel b) (rootPermutationHom p hp hdeg σ)
    apply (tripleDescriptor_permute_eq_self_iff
      (rootTuple p hp hdeg) (rootTuple_injective p hp hdeg) b _).1
    rw [← gal_map_tripleDescriptor p hp hdeg σ b]
    exact h σ
  · intro h σ
    rw [gal_map_tripleDescriptor p hp hdeg σ b]
    apply (tripleDescriptor_permute_eq_self_iff
      (rootTuple p hp hdeg) (rootTuple_injective p hp hdeg) b _).2
    exact h ⟨σ, rfl⟩

/-- Collision-free semantic criterion in the exact disjunctive form needed by
the eventual recursive coefficient test. -/
theorem gal_isSolvable_iff_exists_rational_descriptor
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6) :
    IsSolvable p.Gal ↔
      (∃ b : PairPartition,
        CoefficientsRational p (pairDescriptor (rootTuple p hp hdeg) b)) ∨
      (∃ b : TriplePartition,
        CoefficientsRational p (tripleDescriptor (rootTuple p hp hdeg) b)) := by
  rw [gal_isSolvable_iff_le_pair_or_triple p hp hdeg]
  constructor
  · rintro (⟨b, hb⟩ | ⟨b, hb⟩)
    · exact Or.inl ⟨b,
        (pairDescriptor_coefficientsRational_iff_le_stabilizer p hp hdeg b).2 hb⟩
    · exact Or.inr ⟨b,
        (tripleDescriptor_coefficientsRational_iff_le_stabilizer p hp hdeg b).2 hb⟩
  · rintro (⟨b, hb⟩ | ⟨b, hb⟩)
    · exact Or.inl ⟨b,
        (pairDescriptor_coefficientsRational_iff_le_stabilizer p hp hdeg b).1 hb⟩
    · exact Or.inr ⟨b,
        (tripleDescriptor_coefficientsRational_iff_le_stabilizer p hp hdeg b).1 hb⟩

/-! ## Separating scalar specializations -/

theorem gal_map_pairDescriptorValue
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6)
    (x : Fin 2 → ℕ) (σ : p.Gal) (b : PairPartition) :
    σ.toRingHom (pairDescriptorValue x (rootTuple p hp hdeg) b) =
      pairDescriptorValue x
        (fun i ↦ rootTuple p hp hdeg
          (rootPermutationHom p hp hdeg σ i)) b := by
  rw [map_pairDescriptorValue]
  congr 2
  funext i
  exact gal_maps_rootTuple p hp hdeg σ i

theorem gal_map_tripleDescriptorValue
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6)
    (x : Fin 2 → ℕ) (σ : p.Gal) (b : TriplePartition) :
    σ.toRingHom (tripleDescriptorValue x (rootTuple p hp hdeg) b) =
      tripleDescriptorValue x
        (fun i ↦ rootTuple p hp hdeg
          (rootPermutationHom p hp hdeg σ i)) b := by
  rw [map_tripleDescriptorValue]
  congr 2
  funext i
  exact gal_maps_rootTuple p hp hdeg σ i

theorem pairDescriptorValue_mem_range_iff_le_stabilizer
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6)
    (x : Fin 2 → ℕ)
    (hx : Function.Injective
      (pairDescriptorValue x (rootTuple p hp hdeg)))
    (b : PairPartition) :
    pairDescriptorValue x (rootTuple p hp hdeg) b ∈
        Set.range (algebraMap ℚ p.SplittingField) ↔
      rootPermutationGroup p hp hdeg ≤ pairStabilizer b := by
  rw [mem_range_algebraMap_iff_gal_fixed p hp]
  constructor
  · intro h g hg
    rcases hg with ⟨σ, rfl⟩
    change Preserves (pairLabel b) (rootPermutationHom p hp hdeg σ)
    apply (pairDescriptorValue_permute_fixed_iff
      x (rootTuple p hp hdeg) (rootTuple_injective p hp hdeg) hx b _).1
    rw [← gal_map_pairDescriptorValue p hp hdeg x σ b]
    exact h σ
  · intro h σ
    change σ.toRingHom (pairDescriptorValue x (rootTuple p hp hdeg) b) = _
    rw [gal_map_pairDescriptorValue p hp hdeg x σ b]
    apply (pairDescriptorValue_permute_fixed_iff
      x (rootTuple p hp hdeg) (rootTuple_injective p hp hdeg) hx b _).2
    exact h ⟨σ, rfl⟩

theorem tripleDescriptorValue_mem_range_iff_le_stabilizer
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6)
    (x : Fin 2 → ℕ)
    (hx : Function.Injective
      (tripleDescriptorValue x (rootTuple p hp hdeg)))
    (b : TriplePartition) :
    tripleDescriptorValue x (rootTuple p hp hdeg) b ∈
        Set.range (algebraMap ℚ p.SplittingField) ↔
      rootPermutationGroup p hp hdeg ≤ tripleStabilizer b := by
  rw [mem_range_algebraMap_iff_gal_fixed p hp]
  constructor
  · intro h g hg
    rcases hg with ⟨σ, rfl⟩
    change Preserves (tripleLabel b) (rootPermutationHom p hp hdeg σ)
    apply (tripleDescriptorValue_permute_fixed_iff
      x (rootTuple p hp hdeg) (rootTuple_injective p hp hdeg) hx b _).1
    rw [← gal_map_tripleDescriptorValue p hp hdeg x σ b]
    exact h σ
  · intro h σ
    change σ.toRingHom (tripleDescriptorValue x (rootTuple p hp hdeg) b) = _
    rw [gal_map_tripleDescriptorValue p hp hdeg x σ b]
    apply (tripleDescriptorValue_permute_fixed_iff
      x (rootTuple p hp hdeg) (rootTuple_injective p hp hdeg) hx b _).2
    exact h ⟨σ, rfl⟩

theorem pairEvaluatedResolvent_has_rational_root_iff_exists_le_stabilizer
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6)
    (x : Fin 2 → ℕ)
    (hx : Function.Injective
      (pairDescriptorValue x (rootTuple p hp hdeg))) :
    (∃ q : ℚ, (pairEvaluatedResolvent x (rootTuple p hp hdeg)).IsRoot
      (algebraMap ℚ p.SplittingField q)) ↔
      ∃ b : PairPartition,
        rootPermutationGroup p hp hdeg ≤ pairStabilizer b := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨b, hb⟩ := (pairEvaluatedResolvent_isRoot_iff _ _ _).1 hq
    refine ⟨b, (pairDescriptorValue_mem_range_iff_le_stabilizer
      p hp hdeg x hx b).1 ?_⟩
    exact ⟨q, hb.symm⟩
  · rintro ⟨b, hb⟩
    obtain ⟨q, hq⟩ := (pairDescriptorValue_mem_range_iff_le_stabilizer
      p hp hdeg x hx b).2 hb
    refine ⟨q, (pairEvaluatedResolvent_isRoot_iff _ _ _).2 ?_⟩
    exact ⟨b, hq.symm⟩

theorem tripleEvaluatedResolvent_has_rational_root_iff_exists_le_stabilizer
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6)
    (x : Fin 2 → ℕ)
    (hx : Function.Injective
      (tripleDescriptorValue x (rootTuple p hp hdeg))) :
    (∃ q : ℚ, (tripleEvaluatedResolvent x (rootTuple p hp hdeg)).IsRoot
      (algebraMap ℚ p.SplittingField q)) ↔
      ∃ b : TriplePartition,
        rootPermutationGroup p hp hdeg ≤ tripleStabilizer b := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨b, hb⟩ := (tripleEvaluatedResolvent_isRoot_iff _ _ _).1 hq
    refine ⟨b, (tripleDescriptorValue_mem_range_iff_le_stabilizer
      p hp hdeg x hx b).1 ?_⟩
    exact ⟨q, hb.symm⟩
  · rintro ⟨b, hb⟩
    obtain ⟨q, hq⟩ := (tripleDescriptorValue_mem_range_iff_le_stabilizer
      p hp hdeg x hx b).2 hb
    refine ⟨q, (tripleEvaluatedResolvent_isRoot_iff _ _ _).2 ?_⟩
    exact ⟨b, hq.symm⟩

theorem gal_isSolvable_iff_separating_resolvents_have_rational_root
    (p : ℚ[X]) (hp : Irreducible p) (hdeg : p.natDegree = 6)
    (xp xt : Fin 2 → ℕ)
    (hxp : Function.Injective
      (pairDescriptorValue xp (rootTuple p hp hdeg)))
    (hxt : Function.Injective
      (tripleDescriptorValue xt (rootTuple p hp hdeg))) :
    IsSolvable p.Gal ↔
      (∃ q : ℚ, (pairEvaluatedResolvent xp (rootTuple p hp hdeg)).IsRoot
        (algebraMap ℚ p.SplittingField q)) ∨
      (∃ q : ℚ, (tripleEvaluatedResolvent xt (rootTuple p hp hdeg)).IsRoot
        (algebraMap ℚ p.SplittingField q)) := by
  rw [gal_isSolvable_iff_le_pair_or_triple p hp hdeg,
    pairEvaluatedResolvent_has_rational_root_iff_exists_le_stabilizer
      p hp hdeg xp hxp,
    tripleEvaluatedResolvent_has_rational_root_iff_exists_le_stabilizer
      p hp hdeg xt hxt]

end LeanProofs.PolynomialFormulas.SexticDescriptorGaloisCriterion
