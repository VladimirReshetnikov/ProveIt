import Lib.Adelic.TraceFormula.LevelAlgebra
import New.UpperBound.Objects.Rows

/-!
# Spherical Hecke operators away from the level, and eigensystems

The level `M` is the product of the primes `D.levelPrime 0`, `D.levelPrime 1`, and `D.chosenPlace`
runs through the chosen places above it. The spherical Hecke operators away from `M` form an algebra
that acts at once on the forms `D.principalForms V` of principal level for all hermitian spaces `V`.
It commutes with the finite group `D.chosenGL`, so it acts on the good forms `D.goodForms V`, the
image of the idempotent `D.e₀`.

## Main definitions and results

* `New.Data.sphericalAlgebra`, `New.Data.heckeAlgebra`: the spherical elements of the group algebra
  and the operators that they give; `New.Data.heckeOnGood` is the action on good forms.
* `New.Data.heckeOperator`: the operators `T_{w,i}` at the places `New.Data.IsSplitOffLevel`, as
  members of the Hecke algebra; `New.Data.principalHeckeSplit` is the operator on one space.
* `New.Data.eigenPart`: the part with a given eigensystem. The parts are independent
  (`New.Data.iSupIndep_eigenPart`), and in finite dimension they span the forms
  (`New.Data.iSup_eigenPart_eq_top`).
* `New.Data.exists_hecke_proj_eigenPart`: a Hecke operator that is `1` on one part and `0` on
  finitely many others.

Notions from other files:
* `New.Data.principalForms`: the forms on `V` of archimedean type `typeKernel D.paramW s` that are
  fixed by the principal level `J_M = D.chosenLevel` at the chosen places; `V.formRep` is the
  action of the finite adelic unitary group `G_f = Gf E n` on forms, and `K₀ = stdLevel E n` is its
  standard maximal compact subgroup.
* `New.heckeSplit`: the Hecke operator `T_{w,i}` at a split place `w`, of the double coset of
  `diag (ϖ 1_i, 1)`.
* `New.universalLevelAlgebra`: the elements of a group algebra that keep the vectors of a given
  level in every representation.
-/

noncomputable section

namespace New

open Submodule MonoidAlgebra Representation Gf Module ComplexOrder

section General

variable {E n : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [Fintype n]
  [DecidableEq n] {S : Set (FinPlace E)}

/-- A vector has level `K` (with trivial character) if and only if every element of `K` fixes it. -/
lemma mem_levelSpace_iff_forall_apply_eq {G M : Type*} [Group G] [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ G M} {K : Subgroup G} {y : M} :
    y ∈ levelSpace ρ K ↔ ∀ k ∈ K, ρ k y = y := by simp

/-- Let `G_f = Gf E n` be the finite adelic unitary group over the CM field `E` in the variables
indexed by `n`, let `S` be a set of finite places of `E`, and let `H = trivialOn n S` be the
subgroup of the elements with component `1` at the places of `S`. In every representation `ρ` of
`G_f`, an element `a` of the group algebra of `H` commutes with the action of each `k` that is
supported at the places of `S` and their conjugates. -/
lemma commute_asAlgebraHom_mapDomain_trivialOn {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Gf E n) W) {k : Gf E n} (hk : k ∈ supportedOn n S)
    (a : ℂ[trivialOn n S]) :
    Commute (ρ k) (ρ.asAlgebraHom (mapDomain (trivialOn n S).subtype a)) := by
  rw [asAlgebraHom_mapDomain]
  exact commute_asAlgebraHom
    (fun g : trivialOn n S ↦ (commute_supportedOn_trivialOn hk g.prop).map ρ) a

/-- Let `G_f = Gf E n` be the finite adelic unitary group over the CM field `E` in the variables
indexed by `n`, `S` a set of finite places of `E`, and `H = trivialOn n S` the subgroup of the
elements with component `1` at the places of `S`. Let `J` be a subgroup of the maximal compact group
`K₀ = stdLevel E n` that contains `K₀ ∩ H`. If an element `a` of `ℂ[H]` keeps the vectors fixed by
`K₀ ∩ H` in every representation of `H`, then its image in `ℂ[G_f]` keeps the vectors fixed by `J`
in every representation of `G_f`. -/
lemma mapDomain_mem_universalLevelAlgebra {J : Subgroup (Gf E n)} (hJ_le : J ≤ stdLevel E n)
    (hJ_ge : stdLevel E n ⊓ trivialOn n S ≤ J) {a : ℂ[trivialOn n S]}
    (ha : a ∈ universalLevelAlgebra ((stdLevel E n).subgroupOf (trivialOn n S))) :
    mapDomain (trivialOn n S).subtype a ∈ universalLevelAlgebra J := by
  refine mem_universalLevelAlgebra.2 fun W _ _ ρ ↦ mem_levelAlgebra.2 fun y hy ↦
    mem_levelSpace_iff_forall_apply_eq.2 fun k hk ↦ ?_
  rw [mem_levelSpace_iff_forall_apply_eq] at hy
  set T : End ℂ W := ρ.asAlgebraHom (mapDomain (trivialOn n S).subtype a) with hT
  -- Split `k ∈ J` as `u v` with `u` at `S` and `v ∈ K₀ ∩ H`; then `v` and `u` lie in `J`.
  obtain ⟨u, hu, v, hv, rfl, h_int⟩ := exists_supportedOn_mul_trivialOn S k
  have hv_int : v ∈ stdLevel E n := (h_int (hJ_le hk)).right
  have hu_mem : u ∈ J := (J.mul_mem_cancel_right (hJ_ge ⟨hv_int, hv⟩)).1 hk
  -- The vector `y` is fixed by `K₀ ∩ H`, hence so is `T y`.
  have hTy_off : T y ∈ levelSpace (ρ.comp (trivialOn n S).subtype)
      ((stdLevel E n).subgroupOf (trivialOn n S)) := by
    rw [hT, asAlgebraHom_mapDomain]
    exact mem_levelAlgebra.1 (universalLevelAlgebra_le _ _ ha) y
      (mem_levelSpace_iff_forall_apply_eq.2 fun z hz ↦ hy z (hJ_ge ⟨hz, z.prop⟩))
  have h_comm : Commute (ρ u) T := commute_asAlgebraHom_mapDomain_trivialOn ρ hu a
  have hv_fix : ρ v (T y) = T y := mem_levelSpace_iff_forall_apply_eq.1 hTy_off ⟨v, hv⟩ hv_int
  calc ρ (u * v) (T y) = ρ u (T y) := by rw [map_mul, End.mul_apply, hv_fix]
    _ = T y := by rw [← End.mul_apply, h_comm, End.mul_apply, hy u hu_mem]

end General

namespace Data

variable {P : Parameters} (D : Data P) {s : D.RowIndex → ℤˣ} (V : Space D.E D.RowIndex s)

/-- The level `M` is the product of the two primes `D.levelPrime 0` and `D.levelPrime 1`, and the
places `D.chosenPlace x` are the chosen places of `D.E` above them. The Hecke operators are read at
the finite places `w` that are split (`star w ≠ w`, where `star w` is the complex conjugate) and are
neither a chosen place nor the conjugate of one. In this file, "not above `M`" and "away from `M`"
refer to the places that are neither chosen nor conjugate to a chosen one. -/
structure IsSplitOffLevel (w : FinPlace D.E) : Prop where
  /-- The place `w` differs from its conjugate. -/
  isSplit : w.IsSplit
  /-- The place `w` is neither a chosen place nor the conjugate of one. -/
  notMem_conjClosure : w ∉ (Set.range D.chosenPlace).conjClosure

/-- If the place `w` is split and neither it nor its conjugate is a chosen place above the level
`M`, then the same holds of the conjugate `star w`. -/
protected lemma IsSplitOffLevel.star {D : Data P} {w : FinPlace D.E}
    (hw : D.IsSplitOffLevel w) : D.IsSplitOffLevel (star w) where
  isSplit h_eq := hw.isSplit (star_injective h_eq)
  notMem_conjClosure h_mem := hw.notMem_conjClosure <| by
    simpa only [Set.mem_union, Set.mem_preimage, star_star, or_comm] using h_mem

/-- The group `G^M` of the elements of the finite adelic unitary group `G_f` that have component
`1` at the chosen places above `M`. -/
abbrev offLevelGroup : Subgroup (Gf D.E D.RowIndex) :=
  trivialOn D.RowIndex (Set.range D.chosenPlace)

/-- If `w` is split and neither it nor its conjugate is a chosen place above the level `M`, the
embedding `ofSplitPlace` of `GL(E_w)` in the finite adelic unitary group `G_f`, at the places `w`
and `star w`, has its image in the group `G^M = D.offLevelGroup` of the elements that are `1` at
every chosen place. -/
lemma IsSplitOffLevel.ofSplitPlace_mem {D : Data P} {w : FinPlace D.E} (hw : D.IsSplitOffLevel w)
    (g : GL D.RowIndex (LocField w)) : ofSplitPlace hw.isSplit g ∈ D.offLevelGroup := by
  obtain ⟨hw_off, hw_star_off⟩ : w ∉ Set.range D.chosenPlace ∧ star w ∉ Set.range
    D.chosenPlace := by
    simpa only [Set.mem_union, Set.mem_preimage, not_or] using hw.notMem_conjClosure
  exact mem_trivialOn.2 fun u hu ↦ atPlace_ofSplitPlace_of_ne hw.isSplit g
    (ne_of_mem_of_not_mem hu hw_off) fun h_eq ↦ hw_star_off (by simpa [← h_eq] using hu)

/-- If `w` is split and not above `M`, the forms of principal level are spherical at `w`, that is,
fixed by the part of `K₀` supported at `w` and its conjugate. -/
lemma principalForms_le_sphericalAt {w : FinPlace D.E} (hw : D.IsSplitOffLevel w) :
    D.principalForms V ≤ sphericalAt (V.formRep (typeKernel D.paramW s)) w :=
  levelSpace_anti (maxCompactAt_le_levelOf hw.notMem_conjClosure)

/-- Let `w` be a split place such that neither it nor its conjugate is a chosen place above the
level `M`. The Hecke operator `T_{w,i}` keeps the forms of principal level on `V`. -/
lemma heckeSplit_mem_principalForms {w : FinPlace D.E} (hw : D.IsSplitOffLevel w) (i : ℕ)
    {y : V.Form (typeKernel D.paramW s)} (hy : y ∈ D.principalForms V) :
    heckeSplit (V.formRep (typeKernel D.paramW s)) hw.isSplit i y ∈ D.principalForms V :=
  heckeSplit_mem_levelSpace hw.isSplit i (D.principalForms_le_sphericalAt V hw hy)
    levelOf_le_stdLevel hy

/-- The restriction of the Hecke operator `T_{w,i}` to the forms of principal level on `V`, at a
split place `w` such that neither it nor its conjugate is a chosen place above the level `M`. -/
def principalHeckeSplit {w : FinPlace D.E} (hw : D.IsSplitOffLevel w) (i : ℕ) :
    End ℂ (D.principalForms V) :=
  (heckeSplit (V.formRep (typeKernel D.paramW s)) hw.isSplit i).restrict
    fun _ hy ↦ D.heckeSplit_mem_principalForms V hw i hy

lemma coe_principalHeckeSplit_apply {w : FinPlace D.E} (hw : D.IsSplitOffLevel w) (i : ℕ)
    (y : D.principalForms V) :
    (D.principalHeckeSplit V hw i y).val =
      heckeSplit (V.formRep (typeKernel D.paramW s)) hw.isSplit i y := rfl

/-- The spherical elements away from `M`: the elements of the group algebra of
`G^M = D.offLevelGroup` that keep the vectors fixed by the principal level `J_M = D.chosenLevel` in
every representation of `G_f`. -/
def sphericalAlgebra : Subalgebra ℂ ℂ[D.offLevelGroup] :=
  (universalLevelAlgebra D.chosenLevel).comap (mapDomainAlgHom ℂ ℂ D.offLevelGroup.subtype)

lemma mem_sphericalAlgebra {a : ℂ[D.offLevelGroup]} :
    a ∈ D.sphericalAlgebra ↔
      mapDomain D.offLevelGroup.subtype a ∈ universalLevelAlgebra D.chosenLevel := Iff.rfl

/-- An element `a` of the group algebra of `G^M = D.offLevelGroup`, the elements of the finite
adelic unitary group `G_f` that are `1` at the chosen places above the level `M`, is spherical away
from `M` as soon as it keeps the vectors fixed by `K₀ ∩ G^M` in every representation of `G^M`. -/
lemma mem_sphericalAlgebra_of_mem_universalLevelAlgebra {a : ℂ[D.offLevelGroup]}
    (ha : a ∈ universalLevelAlgebra ((stdLevel D.E D.RowIndex).subgroupOf D.offLevelGroup)) :
    a ∈ D.sphericalAlgebra :=
  D.mem_sphericalAlgebra.2
    (mapDomain_mem_universalLevelAlgebra levelOf_le_stdLevel inf_trivialOn_le_levelOf ha)

/-- The spherical Hecke operators away from `M`: the families `T` of operators `T V` on the forms of
principal level of all hermitian spaces `V` that are given by one spherical element `a` of the group
algebra of `G^M = D.offLevelGroup`. -/
def heckeAlgebra : Subalgebra ℂ
    (∀ {s : D.RowIndex → ℤˣ} (V : Space D.E D.RowIndex s), End ℂ (D.principalForms V)) where
  carrier := {T | ∃ a ∈ D.sphericalAlgebra,
    ∀ {s : D.RowIndex → ℤˣ} (V : Space D.E D.RowIndex s) (y : D.principalForms V),
      (T V y).val = (V.formRep (typeKernel D.paramW s)).asAlgebraHom
        (mapDomain D.offLevelGroup.subtype a) y}
  mul_mem' := by
    rintro S T ⟨a, ha, hS⟩ ⟨b, hb, hT⟩
    exact ⟨a * b, mul_mem ha hb,
      fun V y ↦ by simp only [mapDomain_mul, map_mul, End.mul_apply, Pi.mul_apply, hS, hT]⟩
  add_mem' := by
    rintro S T ⟨a, ha, hS⟩ ⟨b, hb, hT⟩
    exact ⟨a + b, add_mem ha hb, fun V y ↦ by simp [mapDomain_add, hS, hT]⟩
  algebraMap_mem' c := ⟨c • 1, D.sphericalAlgebra.smul_mem (one_mem _) c,
    fun V y ↦ by simp [one_def, Algebra.algebraMap_eq_smul_one]⟩

/-- Let `G^M = D.offLevelGroup` be the group of the finite adelic elements that are `1` at the
chosen places above the level `M`. A family `T` of operators on the forms of principal level of all
hermitian spaces `V` lies in the Hecke algebra if and only if one spherical element acts as `T V`
for every `V`. -/
lemma mem_heckeAlgebra
    {T : ∀ {s : D.RowIndex → ℤˣ} (V : Space D.E D.RowIndex s), End ℂ (D.principalForms V)} :
    (fun {s : D.RowIndex → ℤˣ} (V : Space D.E D.RowIndex s) ↦ T V) ∈ D.heckeAlgebra ↔
      ∃ a ∈ D.sphericalAlgebra,
        ∀ {s : D.RowIndex → ℤˣ} (V : Space D.E D.RowIndex s) (y : D.principalForms V),
          (T V y).val = (V.formRep (typeKernel D.paramW s)).asAlgebraHom
            (mapDomain D.offLevelGroup.subtype a) y := Iff.rfl

/-- Let `G^M = D.offLevelGroup` be the group of the elements of `G_f` that are `1` at the chosen
places, the prime divisors of `D.piM`. Let `a` be a spherical element of its group algebra. Then `a`
gives a member `T` of the Hecke algebra `D.heckeAlgebra`. On each hermitian space `V` with signs `s`
at the infinite places, `T` acts on `D.principalForms V` as `a` does through `V.formRep`. -/
lemma exists_heckeAlgebra_eq_asAlgebraHom {a : ℂ[D.offLevelGroup]} (ha : a ∈ D.sphericalAlgebra) :
    ∃ T : D.heckeAlgebra,
      ∀ {s : D.RowIndex → ℤˣ} (V : Space D.E D.RowIndex s) (y : D.principalForms V),
        (T.val V y).val = (V.formRep (typeKernel D.paramW s)).asAlgebraHom
          (mapDomain D.offLevelGroup.subtype a) y := by
  have h_level {s : D.RowIndex → ℤˣ} (V : Space D.E D.RowIndex s) :
      mapDomain D.offLevelGroup.subtype a ∈
        levelAlgebra (V.formRep (typeKernel D.paramW s)) D.chosenLevel :=
    universalLevelAlgebra_le _ _ (D.mem_sphericalAlgebra.1 ha)
  let T {s : D.RowIndex → ℤˣ} (V : Space D.E D.RowIndex s) : End ℂ (D.principalForms V) :=
    ((V.formRep (typeKernel D.paramW s)).asAlgebraHom
      (mapDomain D.offLevelGroup.subtype a)).restrict (mem_levelAlgebra.1 (h_level V))
  -- By the definition of the restriction, each operator of this family acts as the element.
  exact ⟨⟨T, D.mem_heckeAlgebra.2 ⟨a, ha, fun _ _ ↦ rfl⟩⟩, fun _ _ ↦ rfl⟩

/-- Let `w` be a split place of `D.E` such that neither `w` nor its conjugate is a chosen place
above the level `M`, and let `G^M = D.offLevelGroup` be the elements of the finite adelic unitary
group `G_f` that are `1` at the chosen places. One element `a ∈ ℂ[G^M]` acts as the Hecke operator
`T_{w,i}` in every representation `ρ` of `G_f`, on any complex vector space `W`. -/
lemma exists_asAlgebraHom_eq_heckeSplit {w : FinPlace D.E} (hw : D.IsSplitOffLevel w) (i : ℕ) :
    ∃ a : ℂ[D.offLevelGroup], ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Gf D.E D.RowIndex) W),
      ρ.asAlgebraHom (mapDomain D.offLevelGroup.subtype a) = heckeSplit ρ hw.isSplit i := by
  -- Apply the operator of the regular representation of `G^M` to `1`.
  let ι : GL D.RowIndex (LocField w) →* D.offLevelGroup :=
    (ofSplitPlace hw.isSplit).codRestrict D.offLevelGroup hw.ofSplitPlace_mem
  refine ⟨heckeGL ((leftRegular ℂ D.offLevelGroup).comp ι) i 1,
    fun M _ _ ρ ↦ LinearMap.ext fun y ↦ ?_⟩
  rw [asAlgebraHom_mapDomain]
  -- Both sides are the sum of `ρ (ofSplitPlace g) y` over the cosets `g K_w` in the double coset.
  simp [ι, heckeSplit, heckeGL, heckeFun_eq_sum_toFinset, one_def]

/-- Let `w` be a split place of `D.E` such that neither `w` nor its conjugate is a chosen place
above the level `M`, and let `T_{w,i}` be the Hecke operator of the double coset of
`diag (ϖ 1_i, 1)` at `w`. The family of its restrictions `D.principalHeckeSplit V hw i` to the forms
of principal level, as `V` runs over the hermitian spaces, lies in `D.heckeAlgebra`: one spherical
element of the group algebra of `D.offLevelGroup` gives all of them. -/
lemma principalHeckeSplit_mem_heckeAlgebra {w : FinPlace D.E} (hw : D.IsSplitOffLevel w) (i : ℕ) :
    (fun {s : D.RowIndex → ℤˣ} (V : Space D.E D.RowIndex s) ↦ D.principalHeckeSplit V hw i) ∈
      D.heckeAlgebra := by
  -- One element `a` of the group algebra of `G^M` acts as `T_{w,i}` in every representation.
  obtain ⟨a, ha⟩ : ∃ a : ℂ[D.offLevelGroup], ∀ (W : Type) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Gf D.E D.RowIndex) W),
      ρ.asAlgebraHom (mapDomain D.offLevelGroup.subtype a) = heckeSplit ρ hw.isSplit i :=
    D.exists_asAlgebraHom_eq_heckeSplit hw i
  have h_sph : a ∈ D.sphericalAlgebra := by
    refine D.mem_sphericalAlgebra.2 (mem_universalLevelAlgebra.2 fun W _ _ ρ ↦
      mem_levelAlgebra.2 fun y hy ↦ ?_)
    have hy_sph : y ∈ sphericalAt ρ w :=
      levelSpace_anti (maxCompactAt_le_levelOf hw.notMem_conjClosure) hy
    rw [ha]
    exact heckeSplit_mem_levelSpace hw.isSplit i hy_sph levelOf_le_stdLevel hy
  exact D.mem_heckeAlgebra.2 ⟨a, h_sph, fun V y ↦ by rw [ha, coe_principalHeckeSplit_apply]⟩

open scoped Classical in
/-- The Hecke operator `T_{w,i}`, as a member of the Hecke algebra, for `x = (w, i)` with `w` split
and not above `M`; it is `0` at the other places. -/
def heckeOperator (x : FinPlace D.E × ℕ) : D.heckeAlgebra :=
  if hx : D.IsSplitOffLevel x.1 then
    ⟨fun V ↦ D.principalHeckeSplit V hx x.2, D.principalHeckeSplit_mem_heckeAlgebra hx x.2⟩
  else 0

/-- At a split place `w` not above `M`, `D.heckeOperator (w, i)` acts on forms as `T_{w,i}`. -/
lemma coe_heckeOperator_apply {w : FinPlace D.E} (hw : D.IsSplitOffLevel w) (i : ℕ)
    (y : D.principalForms V) :
    ((D.heckeOperator (w, i)).val V y).val =
      heckeSplit (V.formRep (typeKernel D.paramW s)) hw.isSplit i y := by
  rw [heckeOperator, dite_eq_left hw, coe_principalHeckeSplit_apply]

/-- The part of the forms of principal level on `V` for the eigensystem `p`: the forms on which
each `D.heckeOperator (w, i)` acts by the scalar `p (w, i)`. -/
def eigenPart (p : FinPlace D.E × ℕ → ℂ) : Submodule ℂ (D.principalForms V) :=
  ⨅ x : FinPlace D.E × ℕ, ((D.heckeOperator x).val V).eigenspace (p x)

lemma mem_eigenPart {p : FinPlace D.E × ℕ → ℂ} {y : D.principalForms V} :
    y ∈ D.eigenPart V p ↔ ∀ x : FinPlace D.E × ℕ, (D.heckeOperator x).val V y = p x • y := by
  simp only [eigenPart, mem_iInf, End.mem_eigenspace_iff]

/-- Let `w` be a split place such that neither it nor its conjugate is a chosen place above the
level `M`, let `q` be the norm of `w` and `r` the number of elements of `D.RowIndex`, the rank of
`V`. A form `y` of principal level with Hecke eigensystem `p` is spherical at `w`, and for each
complex `X` the operator `∑_{i ≤ r} (-X)^i q^{i(i-1)/2} T_{w,i}`, the Hecke polynomial at `X`,
multiplies it by `∑_{i ≤ r} (-X)^i q^{i(i-1)/2} p (w, i)`. -/
lemma hasHeckePolynomial_of_mem_eigenPart {p : FinPlace D.E × ℕ → ℂ} {y : D.principalForms V}
    {w : FinPlace D.E} (hy : y ∈ D.eigenPart V p) (hw : D.IsSplitOffLevel w) :
    HasHeckePolynomial (V.formRep (typeKernel D.paramW s)) hw.isSplit
      (heckePolyEval D.RowIndex w fun i : ℕ ↦ p (w, i)) y.val :=
  hasHeckePolynomial_of_heckeSplit (D.principalForms_le_sphericalAt V hw y.prop) fun i ↦ by
    rw [← D.coe_heckeOperator_apply V hw, (D.mem_eigenPart V).1 hy, coe_smul]

/-- Let `T` be in the Hecke algebra, `T_x = D.heckeOperator x` for a pair `x = (w, i)`, and `a, b`
complex numbers. On a form `y` of principal level with eigensystem `d`, the operator
`a (T T_x - b T)` acts as `a (d x - b) T`. -/
lemma smul_mul_heckeOperator_sub_smul_apply {d : FinPlace D.E × ℕ → ℂ} {y : D.principalForms V}
    (hy : y ∈ D.eigenPart V d) (T : D.heckeAlgebra) (x : FinPlace D.E × ℕ) (a b : ℂ) :
    (a • (T * D.heckeOperator x - b • T)).val V y = (a * (d x - b)) • T.val V y := by
  simp [(D.mem_eigenPart V).1 hy x, ← sub_smul, ← mul_smul]

open scoped Classical in
/-- For an eigensystem `q` and a finite set `F` of eigensystems, one member `T` of the Hecke algebra
is, on all `V`, the identity on the forms with eigensystem `q` and zero on those with an eigensystem
`d ∈ F` other than `q`. -/
lemma exists_hecke_proj_eigenPart (q : FinPlace D.E × ℕ → ℂ) (F : Finset (FinPlace D.E × ℕ → ℂ)) :
    ∃ T : D.heckeAlgebra, ∀ d ∈ insert q F,
      ∀ {s : D.RowIndex → ℤˣ} {V : Space D.E D.RowIndex s}, ∀ y ∈ D.eigenPart V d,
        T.val V y = if d = q then y else 0 := by
  induction F using Finset.induction with
  | empty => exact ⟨1, by simp⟩
  | insert e F _ ih =>
    obtain ⟨T, hT⟩ := ih
    by_cases he_eq_q : e = q
    · exact ⟨T, by rwa [he_eq_q, Finset.insert_idem]⟩
    -- Choose `x` with `e x ≠ q x` and multiply by `(T_x - e x) / (q x - e x)`, which is `1` on the
    -- `q`-part and `0` on the `e`-part.
    obtain ⟨x, hx⟩ : ∃ x : FinPlace D.E × ℕ, q x ≠ e x := Function.ne_iff.1 (Ne.symm he_eq_q)
    refine ⟨(q x - e x)⁻¹ • (T * D.heckeOperator x - e x • T), fun d hd s V y hy ↦ ?_⟩
    rw [D.smul_mul_heckeOperator_sub_smul_apply V hy]
    obtain rfl | hd_ne_e := eq_or_ne d e
    · simp [he_eq_q]
    rw [hT d (by simpa [hd_ne_e] using hd) y hy]
    by_cases hd_eq_q : d = q <;> simp [hd_eq_q, sub_ne_zero.2 hx]

/-- An element `g` of `D.chosenGL` acts on forms of principal level through its integral lift
`liftResidue g` to `G_f`. -/
lemma coe_principalRep_apply (g : D.chosenGL) (y : D.principalForms V) :
    (D.principalRep V g y).val = V.formRep (typeKernel D.paramW s) (liftResidue g).val y := rfl

/-- The lift to the group algebra of `G_f` of an element of the group algebra of the finite group
`D.chosenGL`: each group element is replaced by an integral lift that is `1` off `M`. -/
def liftGroupAlgebra (x : ℂ[D.chosenGL]) : ℂ[Gf D.E D.RowIndex] :=
  mapDomain (fun g ↦ (liftResidue g).val) x

lemma liftGroupAlgebra_add (x x' : ℂ[D.chosenGL]) :
    D.liftGroupAlgebra (x + x') = D.liftGroupAlgebra x + D.liftGroupAlgebra x' := mapDomain_add ..

/-- An element `x` of the group algebra of `D.chosenGL` acts on forms of principal level through its
lift to the group algebra of `G_f`. -/
lemma coe_principalRep_asAlgebraHom_apply (x : ℂ[D.chosenGL]) (y : D.principalForms V) :
    ((D.principalRep V).asAlgebraHom x y).val =
      (V.formRep (typeKernel D.paramW s)).asAlgebraHom (D.liftGroupAlgebra x) y := by
  induction x using induction_linear with
  | zero => simp [liftGroupAlgebra]
  | add x x' hx hx' => simp [liftGroupAlgebra_add, hx, hx']
  | single g c => simp [liftGroupAlgebra, coe_principalRep_apply]

/-- The integral lift `liftResidue g` of `g : D.chosenGL` normalises the principal level
`D.chosenLevel`. So in every representation `ρ` of `G_f` it maps `levelSpace ρ D.chosenLevel`, the
vectors fixed by that level, into itself. -/
lemma liftResidue_apply_mem_levelSpace {M : Type} [AddCommGroup M] [Module ℂ M]
    {ρ : Representation ℂ (Gf D.E D.RowIndex) M} (g : D.chosenGL) {y : M}
    (hy : y ∈ levelSpace ρ D.chosenLevel) :
    ρ (liftResidue g).val y ∈ levelSpace ρ D.chosenLevel := by
  -- The representation `levelRep` of `D.chosenGL` on these vectors lets `g` act by
  -- `ρ (liftResidue g)`.
  let π : Representation ℂ D.chosenGL (levelSpace ρ D.chosenLevel) :=
    levelRep ρ (1 : (⊥ : Subgroup D.chosenGL) →* ℂ) (.id D.chosenGL) (by simp)
  exact (π g ⟨y, hy⟩).prop

/-- The lift to `G_f` of an element of the group algebra of `D.chosenGL` keeps the vectors fixed by
the principal level `D.chosenLevel` in every representation. -/
lemma liftGroupAlgebra_mem_universalLevelAlgebra (x : ℂ[D.chosenGL]) :
    D.liftGroupAlgebra x ∈ universalLevelAlgebra D.chosenLevel := by
  induction x using induction_linear with
  | zero => simp [liftGroupAlgebra]
  | add x x' hx hx' => simpa only [liftGroupAlgebra_add] using add_mem hx hx'
  | single g c =>
    refine mem_universalLevelAlgebra.2 fun M _ _ ρ ↦ mem_levelAlgebra.2 fun y hy ↦ ?_
    simpa [liftGroupAlgebra] using smul_mem _ c (D.liftResidue_apply_mem_levelSpace g hy)

/-- Let `D.chosenGL` be the finite group `∏ GL(𝔽_w)` over the chosen places `w` above the two primes
of the level `M`, with `𝔽_w` the residue field and rows indexed by `D.RowIndex`. The action of every
`x` of its group algebra commutes with every member `T` of `D.heckeAlgebra`, the spherical Hecke
operators away from `M`, which are given by elements of `G_f` that are `1` at the chosen places. -/
lemma commute_heckeAlgebra_principalRep (T : D.heckeAlgebra) (x : ℂ[D.chosenGL]) :
    Commute (T.val V) ((D.principalRep V).asAlgebraHom x) := by
  obtain ⟨a, -, ha⟩ := D.mem_heckeAlgebra.1 T.prop
  refine commute_asAlgebraHom (fun g : D.chosenGL ↦ ?_) x
  -- `T` acts as `A`, from `G^M`, and `g` as `ρ (liftResidue g).val`, whose lift `liftResidue g` is
  -- `1` off `M`; these commute.
  set ρ := V.formRep (typeKernel D.paramW s)
  let A : End ℂ (V.Form (typeKernel D.paramW s)) :=
    ρ.asAlgebraHom (mapDomain D.offLevelGroup.subtype a)
  have h_comm : Commute (ρ (liftResidue g).val) A :=
    commute_asAlgebraHom_mapDomain_trivialOn ρ (liftResidue_mem_supportedOn g) a
  ext y : 2
  calc ((T.val V * D.principalRep V g) y).val = A (ρ (liftResidue g).val y) := by
        rw [End.mul_apply, ha, D.coe_principalRep_apply]
    _ = ρ (liftResidue g).val (A y) := by rw [← End.mul_apply, ← h_comm.eq, End.mul_apply]
    _ = ((D.principalRep V g * T.val V) y).val := by
        rw [End.mul_apply, D.coe_principalRep_apply, ha]

/-- A spherical Hecke operator away from `M` preserves the good forms of `V`, the image of the
idempotent `D.e₀` in the forms of principal level. This is the resulting action of the Hecke
algebra on the good forms. -/
def heckeOnGood : D.heckeAlgebra →* End ℂ (D.goodForms V) where
  toFun T := (T.val V).restrict <| by
    -- The good forms are the range of `e₀`, which commutes with `T`.
    rintro _ ⟨y, rfl⟩
    exact ⟨T.val V y, LinearMap.congr_fun (D.commute_heckeAlgebra_principalRep V T D.e₀).eq.symm y⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- On good forms a member of the Hecke algebra acts as it does on the forms of principal level. -/
lemma coe_heckeOnGood_apply (T : D.heckeAlgebra) (y : D.goodForms V) :
    (D.heckeOnGood V T y).val = T.val V y := rfl

/-- The forms of principal level with eigensystem `p` are stable under the group algebra of
`D.chosenGL`. -/
lemma principalRep_mem_eigenPart {p : FinPlace D.E × ℕ → ℂ} {y : D.principalForms V}
    (hy : y ∈ D.eigenPart V p) (x : ℂ[D.chosenGL]) :
    (D.principalRep V).asAlgebraHom x y ∈ D.eigenPart V p := by
  refine (D.mem_eigenPart V).2 fun z ↦ ?_
  rw [← End.mul_apply, (D.commute_heckeAlgebra_principalRep V _ x).eq, End.mul_apply,
    (D.mem_eigenPart V).1 hy z, map_smul]

/-- The parts of the forms of principal level for the Hecke eigensystems are independent, so their
sum is direct. -/
lemma iSupIndep_eigenPart : iSupIndep (D.eigenPart V) :=
  iSupIndep.iInf _ fun x ↦ End.eigenspaces_iSupIndep ((D.heckeOperator x).val V)

/-- If the forms of principal level on `V` are finite-dimensional, only finitely many Hecke
eigensystems occur in a subspace `N`. -/
lemma finite_setOf_inf_eigenPart_ne_bot [Module.Finite ℂ (D.principalForms V)]
    (N : Submodule ℂ (D.principalForms V)) :
    {p : FinPlace D.E × ℕ → ℂ | N ⊓ D.eigenPart V p ≠ ⊥}.Finite :=
  finite_ne_bot_of_iSupIndep ((D.iSupIndep_eigenPart V).mono fun _ ↦ inf_le_right)

/-- Let `y` be a form of principal level on `V` that is an eigenvector of the Hecke operator
`T_{w,i}` for every `i` and every split place `w` away from the level `M`. Then `y` lies in
`D.eigenPart V p` for some eigensystem `p`. -/
lemma exists_mem_eigenPart_of_heckeSplit_eq_smul {y : D.principalForms V}
    (hy : ∀ (w : FinPlace D.E) (hw : D.IsSplitOffLevel w) (i : ℕ), ∃ c : ℂ,
      heckeSplit (V.formRep (typeKernel D.paramW s)) hw.isSplit i y = c • y.val) :
    ∃ p : FinPlace D.E × ℕ → ℂ, y ∈ D.eigenPart V p := by
  have h_eigen (x : FinPlace D.E × ℕ) : ∃ c : ℂ, (D.heckeOperator x).val V y = c • y := by
    obtain ⟨w, i⟩ := x
    by_cases hw : D.IsSplitOffLevel w
    · obtain ⟨c, hc⟩ := hy w hw i
      exact ⟨c, Subtype.ext (by rw [D.coe_heckeOperator_apply V hw, hc, coe_smul])⟩
    · exact ⟨0, by simp [heckeOperator, hw]⟩
  choose p hp using h_eigen
  exact ⟨p, (D.mem_eigenPart V).2 hp⟩

/-- Let `D` be admissible data with CM field `E = D.E`, and `V` a hermitian space over `E` with
signs `s` at the infinite places. An eigensystem `p` assigns a complex number `p (w, i)` to each
finite place `w` of `E` and natural number `i`, and `D.eigenPart V p` consists of the forms of
principal level on `V` on which each `D.heckeOperator (w, i)` acts by `p (w, i)`. If the forms of
principal level on `V` are finite-dimensional, they are the sum of these parts over all `p`. -/
lemma iSup_eigenPart_eq_top (D : Data P) {s : D.RowIndex → ℤˣ} (V : Space D.E D.RowIndex s)
    [Module.Finite ℂ (D.principalForms V)] :
    ⨆ p : FinPlace D.E × ℕ → ℂ, D.eigenPart V p = ⊤ := by
  -- By the spectral theorem for the commuting normal operators `T_{w,i}`, the forms of principal
  -- level lie in the span of their joint eigenvectors.
  let ρ := V.formRep (typeKernel D.paramW s)
  let I : Type := {w : FinPlace D.E // D.IsSplitOffLevel w} × ℕ
  have h_unitary : IsUnitary ρ (innerₛₗ ℂ) := ⟨fun z hz ↦ by simp [hz], V.inner_formRep⟩
  have h_span : D.principalForms V ≤ span ℂ {z | z ∈ D.principalForms V ∧
      ∃ c : I → ℂ, ∀ x : I, heckeSplit ρ x.1.prop.isSplit x.2 z = c x • z} :=
    h_unitary.le_span_hecke_eigenvectors (fun w hw ↦ ⟨hw.isSplit, hw.star⟩)
      (fun w hw ↦ D.principalForms_le_sphericalAt V hw)
      fun w hw i z hz ↦ D.heckeSplit_mem_principalForms V hw i hz
  rw [eq_top_iff, ← map_le_map_iff_of_injective (D.principalForms V).injective_subtype,
    map_subtype_top]
  refine h_span.trans (span_le.2 ?_)
  -- Each joint eigenvector `z` lies in the part of some eigensystem.
  rintro z ⟨hz, c, hc⟩
  obtain ⟨p, hp⟩ := D.exists_mem_eigenPart_of_heckeSplit_eq_smul V (y := ⟨z, hz⟩)
    fun w hw i ↦ ⟨c (⟨w, hw⟩, i), hc (⟨w, hw⟩, i)⟩
  exact mem_map_of_mem (mem_iSup_of_mem p hp)

end Data

end New

end
