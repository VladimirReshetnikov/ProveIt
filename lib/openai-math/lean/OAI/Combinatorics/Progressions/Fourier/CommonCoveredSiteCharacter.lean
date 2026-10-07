/- Modified for ProveIt: Use older set-comprehension and discrete-subgroup names; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
import OAI.Combinatorics.Progressions.Estimates.LinearQuotientCoverAverage
import OAI.Combinatorics.Progressions.Lattices.NormalizedLatticeSheet

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def subspaceArrayIntegerLattice (I : Type*) {J : Type*} (U : Submodule ℝ (J → ℝ)) :
    AddSubgroup (I → U) where
  carrier := {x | ∀ i a, ∃ n : ℤ, (x i).val a = n}
  zero_mem' i a := ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy i a
    obtain ⟨n, hn⟩ := hx i a
    obtain ⟨m, hm⟩ := hy i a
    refine ⟨n + m, ?_⟩
    change (x i).val a + (y i).val a = ((n + m : ℤ) : ℝ)
    rw [hn, hm, Int.cast_add]
  neg_mem' := by
    intro x hx i a
    obtain ⟨n, hn⟩ := hx i a
    refine ⟨-n, ?_⟩
    change -(x i).val a = ((-n : ℤ) : ℝ)
    rw [hn, Int.cast_neg]

abbrev SubspaceArrayTorus (I : Type*) {J : Type*} (U : Submodule ℝ (J → ℝ)) :=
  (I → U) ⧸ subspaceArrayIntegerLattice I U

theorem subspaceArrayFunctional_integral {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℤ)
    (x : I → U) (hx : x ∈ subspaceArrayIntegerLattice I U) :
    ∃ n : ℤ, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x = n := by
  change ∀ i a, ∃ n : ℤ, (x i).val a = n at hx
  choose z hz using hx
  refine ⟨∑ i, ∑ a, frequency i a * z i a, ?_⟩
  change (∑ i, ∑ a, (frequency i a : ℝ) * (x i).val a) = _
  simp only [hz, Int.cast_sum, Int.cast_mul]

noncomputable def subspaceArrayCharacter {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℤ) : SubspaceArrayTorus I U → ℂ :=
  quotientLinearCharacter (subspaceArrayIntegerLattice I U)
    (subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)))
    (subspaceArrayFunctional_integral U frequency)

theorem subspaceArrayCharacter_mk {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℤ) (x : I → U) :
    subspaceArrayCharacter U frequency (QuotientAddGroup.mk' (subspaceArrayIntegerLattice I U) x) =
      CircleFourier.character (subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x : CircleFourier.Circle) := rfl

theorem subspaceArrayCharacter_norm {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℤ) (x : SubspaceArrayTorus I U) :
    ‖subspaceArrayCharacter U frequency x‖ = 1 := quotientLinearCharacter_norm _ _ _ x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem subspaceArrayFunctional_mul_frequency {S J : Type*} [Fintype S] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (b : Matrix S J ℤ) (r : ℕ) (x : S → U) :
    subspaceArrayFunctional U (fun s a => (((r : ℤ) * b s a : ℤ) : ℝ)) x =
      (r : ℝ) * subspaceArrayFunctional U (fun s a => (b s a : ℝ)) x := by
  change (∑ s, ∑ a, (((r : ℤ) * b s a : ℤ) : ℝ) * (x s).val a) =
    (r : ℝ) * (∑ s, ∑ a, (b s a : ℝ) * (x s).val a)
  simp only [Int.cast_mul, Int.cast_natCast, Finset.mul_sum, mul_assoc]

theorem subspaceArrayCharacter_period_multiple {S J : Type*} [Fintype S] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (b : Matrix S J ℤ)
    (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (x : S → U) :
    subspaceArrayCharacter U (fun s a => (r : ℤ) * b s a)
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice S U) (((q * r : ℕ) : ℝ)⁻¹ • x)) =
    subspaceArrayCharacter U b
      (QuotientAddGroup.mk' (subspaceArrayIntegerLattice S U) ((q : ℝ)⁻¹ • x)) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  change CircleFourier.character
      (subspaceArrayFunctional U (fun s a => (((r : ℤ) * b s a : ℤ) : ℝ))
        (((q * r : ℕ) : ℝ)⁻¹ • x) : CircleFourier.Circle) =
    CircleFourier.character
      (subspaceArrayFunctional U (fun s a => (b s a : ℝ)) ((q : ℝ)⁻¹ • x) : CircleFourier.Circle)
  apply congrArg (fun y : ℝ => CircleFourier.character (y : CircleFourier.Circle))
  have he : (r : ℝ) * ((q * r : ℕ) : ℝ)⁻¹ = (q : ℝ)⁻¹ := by
    push_cast
    field_simp
  calc
    _ = (r : ℝ) * subspaceArrayFunctional U (fun s a => (b s a : ℝ)) (((q * r : ℕ) : ℝ)⁻¹ • x) :=
      subspaceArrayFunctional_mul_frequency U b r _
    _ = _ := by rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, he]

end Erdos3

end

section

namespace Erdos3

def arrayCoordinateLinear {I J : Type*} (U : Submodule ℝ (J → ℝ)) (i : I) :
    (I → U) →ₗ[ℝ] (Unit → U) where
  toFun x _ := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def arrayCoordinateTorus {I J : Type*} (U : Submodule ℝ (J → ℝ)) :
    SubspaceArrayTorus I U →+ (I → SubspaceArrayTorus Unit U) :=
  AddMonoidHom.pi (fun i => QuotientAddGroup.map (subspaceArrayIntegerLattice I U)
    (subspaceArrayIntegerLattice Unit U) (arrayCoordinateLinear U i).toAddMonoidHom
    (fun _x hx _ a => hx i a))

theorem arrayCoordinateTorus_mk {I J : Type*} (U : Submodule ℝ (J → ℝ)) (x : I → U) (i : I) :
    arrayCoordinateTorus U (QuotientAddGroup.mk' (subspaceArrayIntegerLattice I U) x) i =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U) (fun _ => x i) := rfl

theorem arrayCoordinateTorus_bijective {I J : Type*} (U : Submodule ℝ (J → ℝ)) :
    Function.Bijective (arrayCoordinateTorus (I := I) U) := by
  constructor
  · intro x y h
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
    obtain ⟨w, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) y
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    intro i a
    exact (QuotientAddGroup.eq_iff_sub_mem.mp (congrFun h i)) () a
  · intro y
    choose v hv using fun i => QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice Unit U) (y i)
    refine ⟨QuotientAddGroup.mk' (subspaceArrayIntegerLattice I U) (fun i => v i ()), ?_⟩
    funext i
    rw [arrayCoordinateTorus_mk]
    have he : (fun _ : Unit => v i ()) = v i := funext (fun u => by cases u; rfl)
    rw [he, hv i]

noncomputable def arrayCoordinateEquiv {I J : Type*} (U : Submodule ℝ (J → ℝ)) :
    SubspaceArrayTorus I U ≃+ (I → SubspaceArrayTorus Unit U) :=
  AddEquiv.ofBijective (arrayCoordinateTorus U) (arrayCoordinateTorus_bijective U)

theorem arrayCoordinateEquiv_continuous {I J : Type*} [Fintype I] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) : Continuous (arrayCoordinateEquiv (I := I) U) := by
  apply continuous_pi
  intro i
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice I U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (arrayCoordinateLinear U i).continuous_of_finiteDimensional

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem integerMatrix_preserves_array_lattice {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (x : I → U)
    (hx : x ∈ subspaceArrayIntegerLattice I U) :
    matrixModuleAction (fun s i => (E s i : ℝ)) x ∈ subspaceArrayIntegerLattice S U := by
  classical
  change ∀ i a, ∃ n : ℤ, (x i).val a = n at hx
  choose z hz using hx
  intro s a
  refine ⟨∑ i, E s i * z i a, ?_⟩
  change (∑ i, (E s i : ℝ) • x i).val a = _
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul, hz, Int.cast_sum, Int.cast_mul]

noncomputable def integerMatrixTorusMap {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) :
    SubspaceArrayTorus I U →+ SubspaceArrayTorus S U :=
  QuotientAddGroup.map (subspaceArrayIntegerLattice I U) (subspaceArrayIntegerLattice S U)
    (matrixModuleAction (fun s i => (E s i : ℝ))).toAddMonoidHom
    (fun x hx => integerMatrix_preserves_array_lattice U E x hx)

theorem integerMatrixTorusMap_mk {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (x : I → U) :
    integerMatrixTorusMap U E (QuotientAddGroup.mk' (subspaceArrayIntegerLattice I U) x) =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice S U)
        (matrixModuleAction (fun s i => (E s i : ℝ)) x) := rfl

end Erdos3

end

section

namespace Erdos3

def unitSubspaceCoordinate {J : Type*} (U : Submodule ℝ (J → ℝ)) (a : J) :
    (Unit → U) →ₗ[ℝ] ℝ where
  toFun x := (x ()).val a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def subspaceAmbientTorus {J : Type*} (U : Submodule ℝ (J → ℝ)) :
    SubspaceArrayTorus Unit U →+ (J → UnitAddCircle) :=
  AddMonoidHom.pi (fun a => quotientLinearPhase (subspaceArrayIntegerLattice Unit U)
    (unitSubspaceCoordinate U a) (fun _x hx => hx () a))

theorem subspaceAmbientTorus_mk {J : Type*} (U : Submodule ℝ (J → ℝ)) (x : Unit → U) (a : J) :
    subspaceAmbientTorus U (QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U) x) a =
      ((x ()).val a : UnitAddCircle) := rfl

theorem subspaceAmbientTorus_continuous {J : Type*} [Fintype J] (U : Submodule ℝ (J → ℝ)) :
    Continuous (subspaceAmbientTorus U) := by
  apply continuous_pi
  intro a
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice Unit U)).continuous_iff.mpr
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp
    (unitSubspaceCoordinate U a).continuous_of_finiteDimensional

end Erdos3

end

section

namespace Erdos3

theorem subspaceArrayCharacter_cover_factorization {I S J : Type*}
    [Fintype I] [Fintype S] [Fintype J]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (q : ℕ) (hq : 0 < q)
    (frequency : Matrix I J ℤ) (b : Matrix S J ℤ)
    (hfactor : ∀ x : I → U, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
      subspaceArrayFunctional U (fun s a => (b s a : ℝ))
        (matrixModuleAction (fun s i => (E s i : ℝ)) ((q : ℝ)⁻¹ • x)))
    (x : SubspaceArrayTorus I U) :
    subspaceArrayCharacter U frequency (quotientIntegerCover (subspaceArrayIntegerLattice I U) q x) =
      subspaceArrayCharacter U b (integerMatrixTorusMap U E x) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
  rw [quotientIntegerCover_mk, integerMatrixTorusMap_mk, subspaceArrayCharacter_mk, subspaceArrayCharacter_mk]
  have he := hfactor ((q : ℝ) • v)
  simp only [smul_smul, inv_mul_cancel₀ hq0, one_smul] at he
  rw [he]

end Erdos3

end

section

namespace Erdos3

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))

noncomputable def euclideanSubspace : Submodule ℝ (EuclideanSpace ℝ D) :=
  U.comap (PiLp.continuousLinearEquiv 2 ℝ (fun _ : D => ℝ)).toLinearMap

noncomputable def euclideanSubspaceArrayEquiv : euclideanSubspace U ≃L[ℝ] (Unit → U) where
  toFun x _ := ⟨WithLp.ofLp x.val, x.property⟩
  invFun x := ⟨WithLp.toLp 2 (x ()).val, (x ()).property⟩
  left_inv _ := rfl
  right_inv x := by funext u; cases u; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    apply continuous_pi
    intro u
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : D => ℝ)).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : D => ℝ)).symm.continuous.comp
      (continuous_subtype_val.comp (continuous_apply ()))).subtype_mk _

omit [Fintype D] in
theorem euclideanSubspaceArrayEquiv_apply (x : euclideanSubspace U) (u : Unit) (i : D) :
    (euclideanSubspaceArrayEquiv U x u).val i = x.val i := rfl

theorem euclideanSubspaceArrayEquiv_mem_lattice (x : euclideanSubspace U) :
    euclideanSubspaceArrayEquiv U x ∈ subspaceArrayIntegerLattice Unit U ↔
      x ∈ latticeSection (standardEuclideanLattice D) (euclideanSubspace U) := by
  change (∀ u i, ∃ n : ℤ, x.val i = n) ↔ x.val ∈ standardEuclideanLattice D
  rw [mem_standardEuclideanLattice]
  constructor
  · intro h i
    obtain ⟨n, hn⟩ := h () i
    exact ⟨n, hn.symm⟩
  · intro h u i
    obtain ⟨n, hn⟩ := h i
    exact ⟨n, hn.symm⟩

theorem euclideanSubspaceArrayEquiv_map_lattice :
    (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup.map
      (euclideanSubspaceArrayEquiv U).toLinearEquiv.toAddEquiv.toAddMonoidHom =
        subspaceArrayIntegerLattice Unit U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (euclideanSubspaceArrayEquiv_mem_lattice U x).mpr hx
  · intro hy
    refine ⟨(euclideanSubspaceArrayEquiv U).symm y, ?_,
      (euclideanSubspaceArrayEquiv U).apply_symm_apply y⟩
    exact (euclideanSubspaceArrayEquiv_mem_lattice U _).mp (by simpa using hy)

noncomputable def euclideanSubspaceTorusEquiv :
    (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) ≃+
        SubspaceArrayTorus Unit U :=
  QuotientAddGroup.congr _ _ (euclideanSubspaceArrayEquiv U).toLinearEquiv.toAddEquiv
    (euclideanSubspaceArrayEquiv_map_lattice U)

instance euclideanSubspaceLattice_discrete :
    DiscreteTopology (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup :=
  latticeSection_discrete (standardEuclideanLattice D) (euclideanSubspace U)

instance euclideanSubspaceLattice_closed :
    IsClosed ((latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup :
      Set (euclideanSubspace U)) := AddSubgroup.isClosed_of_discrete

theorem euclideanSubspaceTorusEquiv_mk (x : euclideanSubspace U) :
    euclideanSubspaceTorusEquiv U (QuotientAddGroup.mk' _ x) =
      QuotientAddGroup.mk' _ (euclideanSubspaceArrayEquiv U x) := rfl

theorem euclideanSubspaceTorusEquiv_continuous : Continuous (euclideanSubspaceTorusEquiv U) := by
  apply (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (euclideanSubspaceArrayEquiv U).continuous

theorem euclideanSubspaceTorusEquiv_symm_continuous :
    Continuous (euclideanSubspaceTorusEquiv U).symm := by
  apply (QuotientAddGroup.isQuotientMap_mk (subspaceArrayIntegerLattice Unit U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (euclideanSubspaceArrayEquiv U).symm.continuous

noncomputable def euclideanSubspaceTorusHomeomorph :
    (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) ≃ₜ
        SubspaceArrayTorus Unit U where
  toEquiv := (euclideanSubspaceTorusEquiv U).toEquiv
  continuous_toFun := euclideanSubspaceTorusEquiv_continuous U
  continuous_invFun := euclideanSubspaceTorusEquiv_symm_continuous U

end Erdos3

end

section

namespace Erdos3

theorem exists_common_covered_site_character :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I S : Type*}
    [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S]
    (E : Matrix S I ℤ) {H : ℕ} (_hH : 1 ≤ H)
    (_hE : ∀ s i, RationalHeightLE (E s i : ℚ) H)
    {P : ℝ} (_hP : 0 ≤ P) (_hI : (Fintype.card I : ℝ) ≤ P)
    (_hS : (Fintype.card S : ℝ) ≤ P) (_hHP : (H : ℝ) ≤ Real.exp P),
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {J : Type*} [Fintype J] (U : Submodule ℝ (J → ℝ)) (frequency : Matrix I J ℤ)
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (_hfrequency : ∀ i a, |(frequency i a : ℝ)| ≤ C)
    (M : (S → U) →ₗ[ℝ] ℝ)
    (_hfactor : ∀ x, subspaceArrayFunctional U (fun i a => (frequency i a : ℝ)) x =
      M (matrixModuleAction (fun s i => (E s i : ℝ)) x)),
    ∃ b : Matrix S J ℤ, (∀ s a, |(b s a : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ x : SubspaceArrayTorus I U,
        subspaceArrayCharacter U frequency (quotientIntegerCover (subspaceArrayIntegerLattice I U) q x) =
          subspaceArrayCharacter U b (integerMatrixTorusMap U E x) := by
  obtain ⟨A, hA, hdenominator⟩ := exists_common_site_denominator
  refine ⟨A, hA, ?_⟩
  intro I S _ _ _ _ E H hH hE P hP hI hS hHP
  obtain ⟨q, hq, hqP, hrows⟩ := hdenominator (fun s i => (E s i : ℚ)) hH hE hP hI hS hHP
  refine ⟨q, hq, hqP, ?_⟩
  intro J _ U frequency C hC hCP hfrequency M hfactor
  obtain ⟨b, hb, he⟩ := hrows U frequency hC hCP hfrequency M
    (fun x => by simpa only [Rat.cast_intCast] using hfactor x)
  refine ⟨b, hb, ?_⟩
  exact subspaceArrayCharacter_cover_factorization U E q hq frequency b
    (fun x => by simpa only [Rat.cast_intCast] using he x)

end Erdos3

end

end OAI
