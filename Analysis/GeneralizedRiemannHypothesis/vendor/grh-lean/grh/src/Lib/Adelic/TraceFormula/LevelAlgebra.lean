import Lib.Adelic.Hecke.Basic

/-!
# The elements of a group algebra that keep a level

For a representation `ρ` of a group `G` and a subgroup `K`, the elements of the group algebra
`ℂ[G]` that map `K`-fixed vectors to `K`-fixed vectors form an algebra, and it acts on the
`K`-fixed vectors.

Notions from other files:

* `levelSpace ρ K`: the subspace of the vectors that `ρ k` fixes for every `k ∈ K`.

## Relation to the literature

Known result: the elements of a group algebra that keep the vectors fixed by a subgroup, and their
action on these vectors. The related class sums are in `Lib.Adelic.Hecke.ClassSums`.
-/

noncomputable section

namespace New

open MonoidAlgebra

variable {G M : Type*} [Group G] [AddCommGroup M] [Module ℂ M]
  (ρ : Representation ℂ G M) (K : Subgroup G)

/-- Pushing an element of `H`'s group algebra forward along `f : H →* G` and letting it act by `ρ`
is letting it act by the restricted representation `ρ ∘ f`. -/
lemma asAlgebraHom_mapDomain {H : Type*} [Group H] (f : H →* G) (a : ℂ[H]) :
    ρ.asAlgebraHom (mapDomain f a) = Representation.asAlgebraHom (ρ.comp f) a := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simp [mapDomain_add, ha, hb]
  | single h c => simp

variable {ρ} in
/-- An operator that commutes with the group commutes with the group algebra. -/
lemma commute_asAlgebraHom {T : Module.End ℂ M} (hT : ∀ g : G, Commute T (ρ g)) (a : ℂ[G]) :
    Commute T (ρ.asAlgebraHom a) := by
  induction a using induction_linear with
  | zero => simp
  | add a b ha hb => simpa using ha.add_right hb
  | single g c => simpa using (hT g).smul_right c

/-- The elements of the group algebra that map `K`-fixed vectors of `ρ` to `K`-fixed vectors. -/
def levelAlgebra : Subalgebra ℂ ℂ[G] where
  carrier := {a : ℂ[G] | ∀ y ∈ levelSpace ρ K, ρ.asAlgebraHom a y ∈ levelSpace ρ K}
  mul_mem' {a b} ha hb y hy := by
    simpa using ha _ (hb y hy)
  add_mem' {a b} ha hb y hy := by
    simpa using add_mem (ha y hy) (hb y hy)
  algebraMap_mem' c y hy := by
    simpa using Submodule.smul_mem (levelSpace ρ K) c hy

variable {ρ K} in
lemma mem_levelAlgebra {a : ℂ[G]} :
    a ∈ levelAlgebra ρ K ↔ ∀ y ∈ levelSpace ρ K, ρ.asAlgebraHom a y ∈ levelSpace ρ K :=
  Iff.rfl

/-- The action of `levelAlgebra ρ K` on the `K`-fixed vectors. -/
def levelAction : levelAlgebra ρ K →ₐ[ℂ] Module.End ℂ (levelSpace ρ K) where
  toFun a := (ρ.asAlgebraHom a).restrict a.2
  map_one' := by simp [LinearMap.ext_iff, Subtype.ext_iff]
  map_mul' a b := by
    ext y
    exact LinearMap.congr_fun (map_mul ρ.asAlgebraHom a.1 b.1) y
  map_zero' := by simp [LinearMap.ext_iff, Subtype.ext_iff]
  map_add' a b := by
    ext y
    exact LinearMap.congr_fun (map_add ρ.asAlgebraHom a.1 b.1) y
  commutes' c := by
    ext y
    simp

variable {ρ K} in
/-- The operator `levelAction ρ K a` sends a `K`-fixed vector `y` to `ρ.asAlgebraHom a y`. -/
@[simp] lemma coe_levelAction_apply (a : levelAlgebra ρ K) (y : levelSpace ρ K) :
    (levelAction ρ K a y : M) = ρ.asAlgebraHom a y :=
  rfl

/-- The elements of the group algebra that keep the `K`-fixed vectors in every representation of
`G` on a complex vector space in `Type`. -/
def universalLevelAlgebra : Subalgebra ℂ ℂ[G] :=
  ⨅ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (ρ : Representation ℂ G M), levelAlgebra ρ K

variable {K} in
/-- An element of `ℂ[G]` lies in `universalLevelAlgebra K` iff, for every representation `ρ` of `G`
on a complex vector space in `Type`, it lies in `levelAlgebra ρ K`, i.e. keeps the `K`-fixed
vectors. -/
lemma mem_universalLevelAlgebra {a : ℂ[G]} :
    a ∈ universalLevelAlgebra K ↔ ∀ (M : Type) [AddCommGroup M] [Module ℂ M]
      (ρ : Representation ℂ G M), a ∈ levelAlgebra ρ K := by
  simp only [universalLevelAlgebra, Algebra.mem_iInf]

/-- For every representation `ρ` of `G` on a complex vector space in `Type`, the algebra
`universalLevelAlgebra K` is contained in `levelAlgebra ρ K`. -/
lemma universalLevelAlgebra_le {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) :
    universalLevelAlgebra K ≤ levelAlgebra ρ K :=
  fun _ ha ↦ mem_universalLevelAlgebra.mp ha M ρ

end New

end
