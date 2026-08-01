import PolynomialFormulas.RadicalTower
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Order.Atoms.Finite

/-!
# Solvable finite Galois extensions lie in the radical closure

This module proves the converse to the finite-Galois obstruction used by
Abel--Ruffini, for extensions realized inside `ℂ`.  The group-theoretic
induction is separated from the initial adjunction of roots of unity: once a
large enough primitive root is present, a maximal normal subgroup with cyclic
quotient supplies one Kummer layer and strictly decreases the Galois group.
-/

open Polynomial IntermediateField
open scoped IsMulCommutative

namespace LeanProofs.PolynomialFormulas

universe u

/-- A Kummer step transported along an embedding into `ℂ`. -/
private theorem cyclic_galois_image_mem_solvableByRad
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (emb : E →+* ℂ)
    (hF : ∀ x : F, emb (algebraMap F E x) ∈ solvableByRad ℚ ℂ)
    [FiniteDimensional F E] [IsGalois F E] [IsCyclic Gal(E/F)]
    (hroots : (primitiveRoots (Module.finrank F E) F).Nonempty) :
    ∀ x : E, emb x ∈ solvableByRad ℚ ℂ := by
  obtain ⟨α, hαpow, hαtop⟩ :=
    exists_root_adjoin_eq_top_of_isCyclic F E hroots
  obtain ⟨a, ha⟩ := hαpow
  have hαpow' : emb α ^ Module.finrank F E ∈ solvableByRad ℚ ℂ := by
    rw [← map_pow, ← ha]
    exact hF a
  have hα : emb α ∈ solvableByRad ℚ ℂ :=
    solvableByRad.rad_mem Module.finrank_pos.ne' hαpow'
  intro x
  have hx : x ∈ adjoin F ({α} : Set E) := by
    rw [hαtop]
    exact trivial
  exact IntermediateField.adjoin_induction F (E := E) (s := ({α} : Set E))
    (p := fun z _ ↦ emb z ∈ solvableByRad ℚ ℂ)
    (by
      rintro z rfl
      exact hα)
    hF
    (fun _ _ _ _ hz hw ↦ by simpa using add_mem hz hw)
    (fun _ _ hz ↦ by simpa using inv_mem hz)
    (fun _ _ _ _ hz hw ↦ by simpa using mul_mem hz hw)
    hx

/-- Data for a proper normal subgroup with cyclic quotient. -/
private structure CyclicNormalStep (G : Type*) [Group G] where
  subgroup : Subgroup G
  normal : subgroup.Normal
  lt_top : subgroup < ⊤
  cyclic : letI := normal; IsCyclic (G ⧸ subgroup)

/-- A finite nontrivial solvable group has a proper normal subgroup with
cyclic quotient. -/
private noncomputable def cyclicNormalStep
    {G : Type*} [Group G] [Finite G] [Nontrivial G] [IsSolvable G] :
    CyclicNormalStep G := by
  classical
  have hcomm : commutator G < (⊤ : Subgroup G) :=
    IsSolvable.commutator_lt_top_of_nontrivial G
  let hex := (eq_top_or_exists_le_coatom (commutator G)).resolve_left hcomm.ne
  let N := hex.choose
  have hNcoatom : IsCoatom N := hex.choose_spec.1
  have hcommN : commutator G ≤ N := hex.choose_spec.2
  have hNnormal : N.Normal := Subgroup.Normal.of_commutator_le (G := G) hcommN
  letI : N.Normal := hNnormal
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N
  haveI : Nontrivial (G ⧸ N) := by
    obtain ⟨g, -, hg⟩ := SetLike.exists_of_lt hNcoatom.lt_top
    refine ⟨⟨q g, 1, ?_⟩⟩
    intro heq
    apply hg
    exact (QuotientGroup.eq_one_iff g).mp heq
  letI : IsSimpleGroup (G ⧸ N) := by
    refine { eq_bot_or_eq_top_of_normal := ?_ }
    intro Q _
    have hle : N ≤ Q.comap q := by
      intro n hn
      change q n ∈ Q
      have hnone : q n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [hnone]
      exact Q.one_mem
    rcases hNcoatom.le_iff.mp hle with htop | hN
    · right
      apply Subgroup.comap_injective hq
      simp only [Subgroup.comap_top, htop]
    · left
      apply Subgroup.comap_injective hq
      simpa only [MonoidHom.comap_bot, q, QuotientGroup.ker_mk'] using hN
  letI : IsMulCommutative (G ⧸ N) :=
    IsMulCommutative.of_comm
      (IsSimpleGroup.comm_iff_isSolvable.mpr (inferInstance : IsSolvable (G ⧸ N)))
  exact ⟨N, hNnormal, hNcoatom.lt_top, inferInstance⟩

/-- Solvable Galois induction after enough roots of unity have been placed in
the base field. -/
private theorem solvable_galois_image_mem_solvableByRad
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (emb : E →+* ℂ)
    (hF : ∀ x : F, emb (algebraMap F E x) ∈ solvableByRad ℚ ℂ)
    [FiniteDimensional F E] [IsGalois F E] [IsSolvable Gal(E/F)]
    (bound : ℕ) (hdegree : Module.finrank F E ∣ bound)
    (hroots : ∀ d : ℕ, d ∣ bound → ∃ ζ : F, IsPrimitiveRoot ζ d) :
    ∀ x : E, emb x ∈ solvableByRad ℚ ℂ := by
  classical
  by_cases hnontrivial : Nontrivial Gal(E/F)
  · letI : Nontrivial Gal(E/F) := hnontrivial
    let step : CyclicNormalStep Gal(E/F) := cyclicNormalStep
    let N : Subgroup Gal(E/F) := step.subgroup
    letI : N.Normal := step.normal
    letI : IsCyclic (Gal(E/F) ⧸ N) := step.cyclic
    let F' : IntermediateField F E := IntermediateField.fixedField N
    letI : FiniteDimensional F F' := IntermediateField.finiteDimensional_left F'
    letI : IsGalois F F' := by
      dsimp only [F']
      infer_instance
    let quotientEquiv : Gal(E/F) ⧸ N ≃* Gal(F'/F) :=
      IsGalois.normalAutEquivQuotient N
    letI : IsCyclic Gal(F'/F) :=
      isCyclic_of_surjective quotientEquiv.toMonoidHom quotientEquiv.surjective
    have hleftDegree : Module.finrank F F' ∣ Module.finrank F E :=
      Dvd.intro (Module.finrank F' E) (Module.finrank_mul_finrank F F' E)
    obtain ⟨ζ, hζ⟩ := hroots (Module.finrank F F') (hleftDegree.trans hdegree)
    have hprimitive : (primitiveRoots (Module.finrank F F') F).Nonempty :=
      ⟨ζ, (mem_primitiveRoots Module.finrank_pos).mpr hζ⟩
    have hF' : ∀ x : F', emb x ∈ solvableByRad ℚ ℂ := by
      apply cyclic_galois_image_mem_solvableByRad
        (emb.comp F'.val.toRingHom) (F := F)
      · intro x
        change emb (algebraMap F E x) ∈ solvableByRad ℚ ℂ
        exact hF x
      · exact hprimitive
    letI : FiniteDimensional F' E := IntermediateField.finiteDimensional_right F'
    let subgroupEquiv : N ≃* Gal(E/F') := IntermediateField.subgroupEquivAlgEquiv N
    letI : IsSolvable Gal(E/F') :=
      solvable_of_surjective (f := subgroupEquiv.toMonoidHom) subgroupEquiv.surjective
    have hrightDegree : Module.finrank F' E ∣ Module.finrank F E :=
      Dvd.intro_left (Module.finrank F F') (Module.finrank_mul_finrank F F' E)
    have hroots' : ∀ d : ℕ, d ∣ bound → ∃ ζ : F', IsPrimitiveRoot ζ d := by
      intro d hd
      obtain ⟨ζ, hζ⟩ := hroots d hd
      exact ⟨algebraMap F F' ζ, hζ.map_of_injective (algebraMap F F').injective⟩
    have hcard : Nat.card Gal(E/F') < Nat.card Gal(E/F) := by
      rw [← Nat.card_congr subgroupEquiv.toEquiv]
      apply lt_of_le_of_ne (Subgroup.card_le_card_group N)
      intro heq
      apply step.lt_top.ne
      exact N.eq_top_of_card_eq heq
    exact solvable_galois_image_mem_solvableByRad
      (F := F') (E := E) emb hF' bound (hrightDegree.trans hdegree) hroots'
  · letI : Subsingleton Gal(E/F) := not_nontrivial_iff_subsingleton.mp hnontrivial
    intro x
    have hx : x ∈ Set.range (algebraMap F E) := by
      rw [IsGalois.mem_range_algebraMap_iff_fixed]
      intro σ
      rw [Subsingleton.elim σ 1]
      rfl
    obtain ⟨a, rfl⟩ := hx
    exact hF a
termination_by Nat.card Gal(E/F)
decreasing_by exact hcard

set_option maxHeartbeats 1000000 in
/-- Base-change a solvable Galois extension embedded in `ℂ` into the radical
closure. -/
private theorem solvable_galois_intermediateField_mem_solvableByRad
    {F : Type} [Field F] [Algebra F ℂ]
    (A : IntermediateField F ℂ)
    (hF : ∀ x : F, algebraMap F ℂ x ∈ solvableByRad ℚ ℂ)
    [FiniteDimensional F A] [IsGalois F A] [IsSolvable Gal(A/F)] :
    ∀ x : A, (x : ℂ) ∈ solvableByRad ℚ ℂ := by
  let N := Module.finrank F A
  let m := N.factorial
  have hmpos : 0 < m := Nat.factorial_pos N
  letI : NeZero (m : ℂ) := ⟨by exact_mod_cast hmpos.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ m
  have hζrad : ζ ∈ solvableByRad ℚ ℂ := by
    apply solvableByRad.rad_mem hmpos.ne'
    rw [hζ.pow_eq_one]
    exact one_mem _
  let Z : IntermediateField F ℂ := F⟮ζ⟯
  have hZrad (z : Z) : (z : ℂ) ∈ solvableByRad ℚ ℂ := by
    exact IntermediateField.adjoin_induction F (E := ℂ) (s := ({ζ} : Set ℂ))
      (p := fun z _ ↦ z ∈ solvableByRad ℚ ℂ)
      (by
        rintro z rfl
        exact hζrad)
      hF
      (fun _ _ _ _ hz hw ↦ add_mem hz hw)
      (fun _ _ hz ↦ inv_mem hz)
      (fun _ _ _ _ hz hw ↦ mul_mem hz hw)
      z.property
  have hζint : IsIntegral F ζ := (hζ.isIntegral hmpos).tower_top
  letI : FiniteDimensional F Z := IntermediateField.adjoin.finiteDimensional hζint
  let M : IntermediateField F ℂ := A ⊔ Z
  letI : FiniteDimensional F M := IntermediateField.finiteDimensional_sup A Z
  let A' : IntermediateField F M := A.restrict le_sup_left
  let Z' : IntermediateField F M := Z.restrict le_sup_right
  have hsup : A' ⊔ Z' = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top,
      IntermediateField.lift_sup, IntermediateField.lift_restrict,
      IntermediateField.lift_restrict]
  letI : FiniteDimensional F A' := IntermediateField.finiteDimensional_left A'
  letI : IsGalois F A' :=
    IsGalois.of_algEquiv (IntermediateField.restrict_algEquiv le_sup_left)
  let Aequiv : Gal(A/F) ≃* Gal(A'/F) :=
    AlgEquiv.autCongr
      (IntermediateField.restrict_algEquiv (show A ≤ M from le_sup_left))
  letI : IsSolvable Gal(A'/F) :=
    solvable_of_solvable_injective
      (f := Aequiv.symm.toMonoidHom) Aequiv.symm.injective
  letI : FiniteDimensional Z' M := IntermediateField.finiteDimensional_right Z'
  letI : IsGalois Z' M := IsGalois.sup_right A' Z' hsup
  let ρ : Gal(M/Z') →* Gal(A'/F) :=
    IntermediateField.restrictRestrictAlgEquivMapHom F A' Z' M
  have hρinj : Function.Injective ρ :=
    IntermediateField.restrictRestrictAlgEquivMapHom_injective A' Z' hsup
  letI : IsSolvable Gal(M/Z') :=
    solvable_of_solvable_injective (f := ρ) hρinj
  let d := Module.finrank Z' M
  have hdpos : 0 < d := Module.finrank_pos
  have hdle' : d ≤ Module.finrank F A' := by
    change Module.finrank Z' M ≤ Module.finrank F A'
    rw [← IsGalois.card_aut_eq_finrank Z' M,
      ← IsGalois.card_aut_eq_finrank F A']
    exact Nat.card_le_card_of_injective ρ hρinj
  have hAA' : Module.finrank F A = Module.finrank F A' :=
    (IntermediateField.restrict_algEquiv
      (show A ≤ M from le_sup_left)).toLinearEquiv.finrank_eq
  have hdle : d ≤ N := hdle'.trans_eq hAA'.symm
  have hdvd : d ∣ m := by
    change d ∣ N.factorial
    exact Nat.dvd_factorial hdpos hdle
  have hrootsZ' : ∀ r : ℕ, r ∣ m → ∃ η : Z', IsPrimitiveRoot η r := by
    intro r hr
    have hrpos : 0 < r := Nat.pos_of_ne_zero fun hrzero ↦ by
      subst r
      have hmzero : m = 0 := by simpa using hr
      exact hmpos.ne' hmzero
    obtain ⟨k, hk⟩ := hr
    have hηC : IsPrimitiveRoot (ζ ^ k) r :=
      hζ.pow hmpos (by rw [hk, Nat.mul_comm])
    let ηM : M :=
      ⟨ζ ^ k, (show Z ≤ M from le_sup_right)
        (pow_mem (IntermediateField.mem_adjoin_simple_self F ζ) k)⟩
    let η : Z' :=
      ⟨ηM, (IntermediateField.mem_restrict le_sup_right ηM).2
        (pow_mem (IntermediateField.mem_adjoin_simple_self F ζ) k)⟩
    refine ⟨η, ?_⟩
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff,
      ← IsPrimitiveRoot.coe_submonoidClass_iff]
    exact hηC
  have hZ'rad (z : Z') : ((z : M) : ℂ) ∈ solvableByRad ℚ ℂ := by
    let z' : Z :=
      ⟨((z : M) : ℂ),
        (IntermediateField.mem_restrict le_sup_right (z : M)).1 z.property⟩
    exact hZrad z'
  have hMrad : ∀ x : M, (x : ℂ) ∈ solvableByRad ℚ ℂ := by
    apply solvable_galois_image_mem_solvableByRad
      (F := Z') (E := M) M.val.toRingHom hZ'rad m hdvd hrootsZ'
  intro x
  let xM : M := ⟨x, (show A ≤ M from le_sup_left) x.property⟩
  exact hMrad xM

/-- A finite Galois extension inside `ℂ` with solvable Galois group is
contained in the radical closure whenever its base field is. -/
theorem solvable_galois_extension_le_solvableByRad
    {K L : IntermediateField ℚ ℂ} (hKL : K ≤ L)
    (hK : K ≤ solvableByRad ℚ ℂ)
    [FiniteDimensional K (IntermediateField.extendScalars hKL)]
    [IsGalois K (IntermediateField.extendScalars hKL)]
    [IsSolvable Gal((IntermediateField.extendScalars hKL)/K)] :
    L ≤ solvableByRad ℚ ℂ := by
  let A : IntermediateField K ℂ := IntermediateField.extendScalars hKL
  have hA : ∀ x : A, (x : ℂ) ∈ solvableByRad ℚ ℂ := by
    apply solvable_galois_intermediateField_mem_solvableByRad A
    intro x
    exact hK x.property
  intro x hx
  exact hA ⟨x, hx⟩

/-- A finite Galois extension of `ℚ` inside `ℂ` with solvable Galois group is
contained in the radical closure. -/
theorem solvable_galois_over_rat_le_solvableByRad
    (L : IntermediateField ℚ ℂ)
    [hfinite : FiniteDimensional ℚ L] [hgalois : IsGalois ℚ L]
    [hsolvable : IsSolvable Gal(L/ℚ)] :
    L ≤ solvableByRad ℚ ℂ := by
  have hL : ∀ x : L, (x : ℂ) ∈ solvableByRad ℚ ℂ := by
    exact @solvable_galois_intermediateField_mem_solvableByRad ℚ
      inferInstance inferInstance L
      (fun q ↦ IntermediateField.algebraMap_mem _ q)
      hfinite hgalois hsolvable
  intro x hx
  exact hL ⟨x, hx⟩

end LeanProofs.PolynomialFormulas
