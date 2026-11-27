import Lib.GaloisRep.LocalGlobal.LocalFormTypes
import Lib.GaloisRep.Main.AllRanks

/-!
# Auxiliary places, base level, integral Hecke algebra and operators at the auxiliary places

Base data `D` consist of a finite set `D.places` of places and a space `D.forms` of forms of a fixed
type at `D.places`. The forms of principal level at finitely many further places make up a
finite-dimensional space with an integral lattice. Functions on the systems of eigenvalues act on
this space, by a scalar on the forms of each system. Those that keep integral forms make up a closed
integral Hecke algebra. At the auxiliary places, translations and the action of `GL_N` over the
residue fields give operators that commute with this algebra.

## Main definitions and results

* `New.Patching.TaylorWilesPlaces`: Frobenius data at places `w j` whose residue fields have
  order ≡ 1 mod m.
* `New.Patching.BaseLevel.formsOfLevel`: the forms of that type and principal level at `L`, with the
  lattice `New.Patching.BaseLevel.ellIntegralForms` of integral forms and the algebra
  `New.Patching.BaseLevel.integralEnd` that keeps it.
* `New.Patching.BaseLevel.heckeAlgebra`, `New.Patching.BaseLevel.heckeAction`: the functions whose
  operator keeps integral forms, and their action; `New.Patching.BaseLevel.isClosed_heckeAlgebra`:
  they form a closed set for the product topology on functions from systems to `PadicAlgCl ℓ`.
* `New.Patching.BaseLevel.localOperators`: the operators that come from translations at one place
  `w j`. They commute with the Hecke algebra.
* `New.Patching.BaseLevel.residueRep`: the action of the groups `GL_N` over the residue fields,
  `N = |n|`; its fixed forms are those of base level
  (`New.Patching.BaseLevel.mem_formsOfLevel_empty_iff_residueRep_fixed`).
* `New.Patching.BaseLevel.exists_higman_operator`: for a finite group `Δ` embedded in the product of
  the groups `GL_N` over the residue fields at the places `w j` (all off level), an operator `Ψ`
  with `∑ g⁻¹ Ψ g = c`.

Notions from other files:
* `New.levelOf`: The elements of K₀ = `stdLevel E n` whose reductions modulo the places w_i lie in a
  subgroup H of ∏_i GL_n(k_{w_i}); for H = ⊥ this is the principal level at these places.
* `New.Space.forms`: Algebraic modular forms of weight κ on a definite space V: functions f on G_f
  with open right stabiliser and f(γg) = ρ_κ(γ)f(g) for rational γ, ρ_κ = `New.Space.weightRep`.
* `New.Patching.Isotypic`: An isotypic space of forms: for a system t of Hecke eigenvalues at the
  finite places, the forms that are Hecke eigenforms with eigenvalues t at almost all places.
* `New.Patching.localFormRep`: The action of GL_N(E_w), N = |n|, on forms at a split place w.

## Relation to the literature

Known result: Taylor–Wiles freeness at auxiliary primes, up to the orders of the stabilisers. Here
the setting is integral forms of principal level on a definite unitary group, with any finite
subgroup of the product of the finite general linear groups at the auxiliary places. Freeness holds
only up to a fixed integer and is expressed as one Higman operator. Source: Taylor–Wiles, Ann. Math.
141 (1995); Clozel–Harris–Taylor, Publ. IHES 108 (2008), §3.
-/

noncomputable section

/-!
## Auxiliary places, base level and integral forms

* `New.Patching.TaylorWilesPlaces`, `New.Patching.BaseLevel`: the auxiliary places and the base
  data.
* `New.Patching.BaseLevel.ellIntegralForms`, `New.Patching.BaseLevel.formsOfLevel`,
  `New.Patching.BaseLevel.integralEnd`: the integral forms, the forms of level `L`, and the
  endomorphisms of the latter that keep integral forms.
* `New.Patching.BaseLevel.Eigensystem`, `New.Patching.BaseLevel.IsOffLevel`: the systems of
  eigenvalues that occur, and the places at which all of them have their eigenvalues.
-/

namespace New.Patching

open Gf NumberField Module Algebra NormedField

variable {ℓ : ℕ} (E J : Type)
  {n : Type} [Field E] [CMType E] [Fintype n] [DecidableEq n]
  (V : Space E n 1) (κ : Weight E) (m : ℕ)

/-- Auxiliary places as in the Taylor–Wiles method: for each index `j` a Frobenius datum at a
finite place `w j` of `E`, such that no two of these places are equal or conjugate and `m` divides
`q_j − 1`, where `q_j` is the order of the residue field at `w j`. -/
structure TaylorWilesPlaces (E J : Type) [Field E] [NumberField E] [IsCMField E] (m : ℕ)
    [Algebra E Ω] where
  /-- For each index `j`, the Frobenius datum at the place `w j`. -/
  frobData : J → FrobeniusDatum E
  /-- No two of the places `w j` are equal or conjugate. -/
  apart : IsConjApart (frobData · |>.place)
  /-- `m` divides `q_j − 1` for each `j`. -/
  dvd_q_sub_one (j : J) : m ∣ (frobData j).place.q - 1

variable {E J}

/-- The place `w j` of `Q`: the finite place of its Frobenius datum with index `j`. -/
abbrev TaylorWilesPlaces.place {E : Type} [Field E] [NumberField E] [IsCMField E]
    {m : ℕ} [Algebra E Ω] (Q : TaylorWilesPlaces E J m) (j : J) :
    FinPlace E :=
  (Q.frobData j).place

attribute [instance] TaylorWilesPlaces.apart

/-! ### The base level and deeper levels -/

/-- Base data: a finite set `places` of places; a space `forms` of forms of fixed type at `places`;
a common multiple m of the orders of all stabilisers Γ ∩ gK₀g⁻¹. Here Γ is the group of rational
points and K₀ = `stdLevel E n`. -/
structure BaseLevel where
  /-- The finite set of places of the level. -/
  places : Finset (FinPlace E)
  /-- The space of forms of weight `κ` that have the given type at `places`. -/
  forms : Submodule ℂ (V.forms κ)
  /-- `forms` is kept by every operator that commutes with the maximal level at the places of
  `places` and their conjugates. -/
  map_mem_forms (T : V.forms κ →ₗ[ℂ] V.forms κ) :
    (∀ k : stdLevel E n, Commute (V.formTranslation κ (componentOn n places k)) T) → forms ≤
      forms.comap T
  /-- Some open subgroup acts on `forms` by a character, through its components at the places of
  `places` and their conjugates. -/
  exists_level :
    ∃ (K : Subgroup (Gf E n)) (χ : K →* ℂ),
      K.IsOpen ∧ forms ≤ levelSpace ((V.formTranslation κ).comp (componentOn n places)) K χ
  /-- `m` is a multiple of the order of each stabiliser `Γ ∩ g K₀ g⁻¹`, where `Γ` is the group of
  rational points and `K₀ = stdLevel E n`. -/
  card_aut_dvd (g : Gf E n) : Nat.card (classAut V.Γf (stdLevel E n) g) ∣ m

variable {V κ m} {D : BaseLevel V κ m} (L : J → FinPlace E)

namespace BaseLevel

/-- Integral forms: the `New.Patching.EllAdicIntegers`-module of forms whose values at all points g
integral above ℓ (the components of g at the places above ℓ lie in the local level) have coordinates
that ιℓ sends to ℓ-adic integers. -/
def ellIntegralForms [ThePrime ℓ] [PadicIso ℓ] : Submodule EllAdicIntegers (V.forms κ) where
  carrier :=
    {f : ↥(V.forms κ) |
      ∀ g ∈ integralAbove n ℓ, ∀ i : WeylIndex n κ.1, ιℓ (f.1 g i) ∈ valuation.integer}
  add_mem' := by simp_all [add_mem]
  zero_mem' := by simp
  -- `ιℓ` sends the image of `c` in `ℂ` back to `c`, an `ℓ`-adic integer
  smul_mem' c f hf g hg i := by
    have h_val :
        ιℓ ((c • f).1 g i) = algebraMap EllAdicIntegers (PadicAlgCl ℓ) c * ιℓ (f.1 g i) := by
      simp [smul_def, iota_ell_algebraMap]
    rw [h_val]
    exact mul_mem c.2 (hf g hg i)

/-- For a finite place `w` not above `ℓ`, the operators generated by the translations supported at
`w` and `w̄` keep the integral forms. -/
lemma localGroupAlgebra_le_endPreserving [ThePrime ℓ] [PadicIso ℓ] {w : FinPlace E}
    (hw : ↑ℓ ∉ w.asIdeal) :
    localGroupAlgebra w ≤ endPreserving (W := V.forms κ) ellIntegralForms := by
  refine adjoin_le ?_
  rintro _ ⟨a, ha, rfl⟩ f hf g hg i
  have h_ne (v : FinPlace E) (hv : ↑ℓ ∈ v.asIdeal) : v ≠ w := by
    rintro rfl
    exact hw hv
  -- `a` has component `1` at the places above `ℓ`, which differ from `w` and `star w`.
  have h_a_one (v : FinPlace E) (hv : ↑ℓ ∈ v.asIdeal) : a.atPlace v = 1 := by
    have hv_star : ↑ℓ ∈ (star v).asIdeal := by rwa [mem_star_place, star_natCast]
    exact mem_supportedOn.mp ha v (h_ne v hv) (h_ne (star v) hv_star)
  have h_mul : g * a ∈ integralAbove n ℓ := by
    refine mem_localLevel.mpr fun v hv ↦ ?_
    rw [map_mul, h_a_one v hv, mul_one]
    exact mem_localLevel.mp hg v hv
  exact hf (g * a) h_mul i

/-- The action of G_f on forms of weight κ on V by right translation through the components at the
places outside `D.places` and its conjugates. -/
abbrev repOff : Gf E n →* V.forms κ →ₗ[ℂ] V.forms κ :=
  (V.formTranslation κ).comp (componentOn n (Set.conjClosure D.places)ᶜ)

/-- The forms in `D.forms` that are fixed by the components off `D.places` and its conjugates of the
principal level subgroup of K₀ at the places L. -/
abbrev formsOfLevel : Submodule ℂ ↥(V.forms κ) :=
  D.forms ⊓ levelSpace D.repOff (levelOf L ⊥)

/-- Systems of eigenvalues of level L: the isotypic spaces that contain a nonzero form of
`New.Patching.BaseLevel.formsOfLevel`. -/
def Eigensystem : Set (Isotypic V κ) :=
  {x : Isotypic V κ | ∃ f ∈ x.val ⊓ D.formsOfLevel L, f ≠ 0}

/-- The places off the level `L`: (a) neither `w` nor its conjugate is in `D.places`, and `w` is not
above `ℓ`; (b) for each system `x` of level `L`, the forms of `x` in `D.formsOfLevel L` lie in
`eigenformsAt V κ w (t w)`, where `t = x.heckeEigenvalues` is the chosen system of eigenvalues that
defines `x`. If `w` splits, (b) says that these forms are spherical at `w` with Hecke eigenvalues
`t w`; otherwise it is no condition. -/
def IsOffLevel [ThePrime ℓ] (w : FinPlace E) : Prop :=
  -- (a) `w` and its conjugate are off `D.places`, and `w` is not above `ℓ`
  w ∉ D.places ∧
  star w ∉ D.places ∧
  ↑ℓ ∉ w.asIdeal ∧
  -- (b) the forms of level `L` in each system have its eigenvalues at `w`
  ∀ x ∈ D.Eigensystem L, x.val ⊓ D.formsOfLevel L ≤ eigenformsAt V κ w (x.heckeEigenvalues w)

/-- An element `k` with component `1` at the places of `D.places` acts through `D.repOff`, the
action through the components off `D.places` and its conjugates, as the plain translation by `k`. -/
lemma repOff_eq_of_mem_trivialOn (k : Gf E n) (hk : k ∈ trivialOn n D.places) :
    D.repOff k = V.formTranslation κ k := by
  -- Cutting off the components at `D.places` and its conjugates leaves `k` unchanged.
  have h_cut : componentOn n (.conjClosure D.places)ᶜ k = k :=
    Gf.ext fun w ↦ by simp_all [← supportedOn_compl]
  rw [repOff, MonoidHom.comp_apply, h_cut]

/-- The `New.Patching.EllAdicIntegers`-algebra of ℂ-linear endomorphisms of the space of forms
`New.Patching.BaseLevel.formsOfLevel` attached to the base data D and the family of finite places
L. -/
@[reducible]
def FormEnd [ThePrime ℓ] [PadicIso ℓ] : Type := End ℂ (D.formsOfLevel L)
  deriving Semiring, Ring, Algebra EllAdicIntegers

/-- The `New.Patching.EllAdicIntegers`-algebra of ℂ-linear endomorphisms of the space of forms
`New.Patching.BaseLevel.formsOfLevel` that preserve its integral forms. -/
abbrev integralEnd [ThePrime ℓ] [PadicIso ℓ] : Subalgebra EllAdicIntegers (D.FormEnd L) :=
  endPreserving (ellIntegralForms.comap ((formsOfLevel L).subtype.restrictScalars EllAdicIntegers))

/-- The forms of the base level, with no auxiliary places, are forms of every level `L`. -/
lemma formsOfLevel_base_le : D.formsOfLevel ![] ≤ D.formsOfLevel L := by
  -- The principal level at the places `L` lies in the level of the empty family of places.
  have h_le : (levelOf L ⊥ : Subgroup (Gf E n)) ≤ levelOf (![] : Fin 0 → FinPlace E) ⊥ :=
    -- The product of the groups over the empty family is trivial.
    fun g hg ↦ mem_levelOf.mpr
      ⟨levelOf_le_stdLevel hg, Subgroup.mem_bot.mpr (Subsingleton.elim _ _)⟩
  exact inf_le_inf_left D.forms (levelSpace_anti h_le)

end BaseLevel

end New.Patching

/-!
## Scalar action of systems and the integral Hecke algebra

For base data `D` (`New.Patching.BaseLevel`) and finitely many places `L`,
`New.Patching.BaseLevel.formsOfLevel` is the space of forms in `V.forms κ` with two properties. At
`D.places` they satisfy the level condition of `D`. Off `D.places` and its conjugates they have
principal level at `L` and maximal level elsewhere.

* The space has finite dimension and is spanned by its isotypic parts
  (`New.Patching.BaseLevel.formsOfLevel_le_of_eigensystem`), so operators can be compared there
  (`New.Patching.BaseLevel.formEnd_ext`).
* The space has only finitely many systems, and almost every place is off the level
  (`New.Patching.BaseLevel.eventually_isOffLevel`).
* `New.Patching.BaseLevel.diagOp`, `New.Patching.BaseLevel.systemAction`: a function `t` from
  systems to `PadicAlgCl ℓ` acts on the part `x` by the scalar `ιℓ.symm (t x)`.
-/

namespace New.Patching.BaseLevel

open NumberField Module Filter LinearMap Submodule Gf DFinsupp

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
  {E : Type} [Field E] [CMType E] {n : Type} [Fintype n] [DecidableEq n]
  {V : Space E n 1} {κ : Weight E} {c : ℕ} {D : BaseLevel (n := n) V κ c} {J : Type} [Finite J]
  {L : J → FinPlace E} (t : D.Eigensystem L → PadicAlgCl ℓ)

open scoped Classical in
/-- The forms of level `L` make up a finite-dimensional space: an open subgroup acts on them by a
character. -/
instance : FiniteDimensional ℂ (D.formsOfLevel L) := by
  -- The group `K ⊓ levelOf L ⊥` is open and acts on `D.formsOfLevel L` through the character `χ`.
  obtain ⟨K, χ, hK, hY⟩ := D.exists_level
  let χ' : ↥(K ⊓ levelOf L ⊥) →* ℂ := χ.comp (Subgroup.inclusion inf_le_left)
  have h_fin : Module.Finite ℂ (levelSpace (V.formTranslation κ) (K ⊓ levelOf L ⊥) χ') :=
    V.finite_formTranslation_levelSpace κ (hK.and isOpen_levelOf) χ'
  have h_le : D.formsOfLevel L ≤ levelSpace (V.formTranslation κ) (K ⊓ levelOf L ⊥) χ' := by
    refine fun f ⟨hf_Y, hf_lev⟩ ↦ mem_levelSpace.mpr fun ⟨k, hk_K, hk_lev⟩ ↦ ?_
    -- `k` is its part at `D.places`, which acts by `χ`, times its part off `D.places`, which fixes
    -- `f`
    have h_split : componentOn n D.places k * componentOn n (.conjClosure D.places)ᶜ k = k := by
      refine Gf.ext fun w ↦ ?_
      -- At `w` one factor keeps the component of `k` and the other is `1`.
      simp only [map_mul, atPlace_componentOn, Set.mem_union, Set.mem_preimage, Set.mem_compl_iff,
        Finset.mem_coe, star_star]
      grind
    have h_fix : V.formTranslation κ (componentOn n (.conjClosure D.places)ᶜ k) f = f := by
      simpa using mem_levelSpace.mp hf_lev ⟨k, hk_lev⟩
    have h_char : V.formTranslation κ (componentOn n D.places k) f = χ ⟨k, hk_K⟩ • f :=
      mem_levelSpace.mp (hY hf_Y) ⟨k, hk_K⟩
    calc
      V.formTranslation κ k f =
          V.formTranslation κ (componentOn n D.places k * componentOn n (.conjClosure D.places)ᶜ k)
            f := by
        rw [h_split]
      _ = χ ⟨k, hk_K⟩ • f := by rw [map_mul, End.mul_apply, h_fix, h_char]
  exact .of_fg ((Finite.iff_fg.mp h_fin).of_le h_le)

/-- Only finitely many systems of eigenvalues have level `L`. -/
instance : Fintype (D.Eigensystem L) := by
  -- Choose a nonzero form of level `L` in each system. These forms are linearly independent in
  -- `D.formsOfLevel L`, which has finite dimension.
  refine Set.Finite.fintype ?_
  have h_exists : ∀ x : D.Eigensystem L,
      ∃ f ∈ (x : Isotypic V κ).val ⊓ D.formsOfLevel L, f ≠ 0 :=
    fun x ↦ x.prop
  choose f hf hf_ne using h_exists
  have h_indep : LinearIndependent ℂ fun x : Eigensystem L ↦ (⟨f x, (hf x).2⟩ : D.formsOfLevel L) :=
    .of_comp (formsOfLevel L).subtype
      (Isotypic.iSupIndep_val.linearIndependent _ (fun x ↦ (hf x).1) hf_ne)
  exact h_indep.finite

/-- A finitely generated space `U` of forms inside an isotypic space `x` lies in
`eigenformsAt V κ w (x.heckeEigenvalues w)` for almost every finite place `w`: its forms are
eigenforms at `w` with the eigenvalues of `x`. -/
lemma _root_.New.Patching.Isotypic.eventually_le_eigenformsAt_of_fg (x : Isotypic V κ)
    (U : Submodule ℂ (V.forms κ)) (hU : U.FG) :
    U ≤ x.val → ∀ᶠ w : FinPlace E in cofinite, U ≤ eigenformsAt V κ w (x.heckeEigenvalues w) := by
  -- Each generator is such an eigenform at almost every place, and so is a finite sum.
  refine fg_induction
    (motive := fun U _ ↦
      U ≤ x.val → ∀ᶠ w : FinPlace E in cofinite, U ≤ eigenformsAt V κ w (x.heckeEigenvalues w))
    ?_ ?_ U hU
  · intro f h_le
    filter_upwards [Isotypic.mem_iff_eventually.mp (h_le (mem_span_singleton_self f))] with w hw
    exact (span_singleton_le_iff_mem f _).mpr hw
  · intro U₁ U₂ hU₁ hU₂ ih₁ ih₂ h_le
    filter_upwards [ih₁ (le_sup_left.trans h_le), ih₂ (le_sup_right.trans h_le)] with w h₁ h₂
    exact sup_le h₁ h₂

omit [PadicIso ℓ] in
/-- Almost every finite place is off the level `L`: it avoids `D.places`, its conjugates and the
places above `ℓ`, and each system of level `L` has its eigenvalues there. -/
lemma eventually_isOffLevel : ∀ᶠ w : FinPlace E in cofinite, D.IsOffLevel L w := by
  -- Each of the finitely many systems `x` of level `L` has its eigenvalues at almost all places on
  -- `x.val ⊓ D.formsOfLevel L`, a space of finite dimension.
  have h_systems : ∀ᶠ w : FinPlace E in cofinite, ∀ x ∈ D.Eigensystem L,
      x.val ⊓ D.formsOfLevel L ≤ eigenformsAt V κ w (x.heckeEigenvalues w) := by
    refine (Set.toFinite (D.Eigensystem L)).eventually_all.mpr fun x _hx ↦ ?_
    exact x.eventually_le_eigenformsAt_of_fg _ (Finite.iff_fg.mp inferInstance) inf_le_left
  filter_upwards [GaloisRep.eventually_notMem_star_notMem ℓ D.places, h_systems]
    with w ⟨hw_S, hw_star, hw_ell⟩ hw_eig
  exact ⟨hw_S, hw_star, hw_ell, hw_eig⟩

open scoped Classical in
/-- Forms of level `L` are fixed by the elements of K₀ = `stdLevel E n` whose components at the
places of `L` and of `D.places` are `1`. -/
lemma formsOfLevel_le_levelSpace :
    D.formsOfLevel L ≤
      levelSpace (V.formTranslation κ)
        (stdLevel E n ⊓ trivialOn n ↑((Set.finite_range L).toFinset ∪ D.places)) := by
  -- An integral element trivial at `L` and `D.places` lies in the level, where `D.repOff` is the
  -- plain translation.
  refine fun f ⟨_, hf_lev⟩ ↦ mem_levelSpace.mpr fun ⟨k, hk⟩ ↦ ?_
  -- Both facts follow from `hk`.
  have hk_off : k ∈ trivialOn n D.places := by simp_all [trivialOn]
  have hk_lev : k ∈ levelOf L ⊥ := inf_trivialOn_le_levelOf (by simp_all [trivialOn])
  have h_fix : D.repOff k f = f := by simpa using mem_levelSpace.mp hf_lev ⟨k, hk_lev⟩
  -- The level acts through the trivial character: the right side is `1 • f`.
  calc
    V.formTranslation κ k f = D.repOff k f := by rw [D.repOff_eq_of_mem_trivialOn k hk_off]
    _ = f := h_fix
    _ = _ := by simp

/-! ### Functions on systems as operators -/

open scoped Classical in
/-- For a function `t` from systems to `PadicAlgCl ℓ`, a chosen endomorphism of the space of forms
acting on the isotypic space of each system `x` by the scalar `ιℓ.symm (t x)`. -/
@[irreducible]
def diagOp : End ℂ (V.forms κ) :=
  DFinsupp.lsum ℕ (fun x ↦ ιℓ.symm (t x) • x.1.1.subtype) ∘ₗ
    (DFinsupp.lsum ℕ fun x : D.Eigensystem L ↦ x.1.1.subtype).leftInverse

omit [Finite J] in
/-- On the isotypic space of a system `x`, the operator `diagOp t` is the scalar `ιℓ⁻¹ (t x)`. -/
lemma diagOp_apply (x : Eigensystem L) {f : ↥(V.forms κ)} (hf : f ∈ (x : Isotypic V κ).val) :
    diagOp t f = ιℓ.symm (t x) • f := by
  classical
  -- The isotypic spaces are independent, so the sum map is injective and its left inverse sends
  -- `f` to the family supported at `x`.
  have h_inv :
      (lsum ℕ fun y : D.Eigensystem L ↦ (y : Isotypic V κ).val.subtype).leftInverse f =
        .single x ⟨f, hf⟩ := by
    simpa using
      leftInverse_apply_of_inj (ker_eq_bot.mpr Isotypic.iSupIndep_val.dfinsupp_lsum_injective)
        (.single x ⟨f, hf⟩)
  simp [diagOp, h_inv]

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.univ in
/-- The space `New.Patching.BaseLevel.formsOfLevel` is spanned by its eigenforms: a subspace N
containing its intersection with every isotypic space of level L contains all of it. -/
lemma formsOfLevel_le_of_eigensystem {N : Submodule ℂ (V.forms κ)}
    (hN : ∀ x : D.Eigensystem L, (x : Isotypic V κ).val ⊓ D.formsOfLevel L ≤ N) :
    D.formsOfLevel L ≤ N := by
  -- `D.formsOfLevel L` is stable under the Hecke operators at the split places off `L` and
  -- `D.places`, so it is spanned by their common eigenforms (`le_span_isSphericalOff`), each of
  -- which lies in an isotypic space.
  refine (le_span_isSphericalOff _ formsOfLevel_le_levelSpace ?_).trans ?_
  · intro w hw hw_off hw_off' j f hf
    obtain ⟨hf_Y, hf_lev⟩ := Submodule.mem_inf.mp hf
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · -- The type `D.forms` is kept: the operator at `w` commutes with the components at `D.places`.
      have h_comm (k : stdLevel E n) : Commute (V.formTranslation κ (componentOn n D.places k))
          (heckeSplit (V.formTranslation κ) hw j) := by
        -- The component of `k` at `D.places` is trivial at `w`, as `w` and `star w` are off
        -- `D.places`.
        have hk_triv : componentOn n D.places (k : Gf E n) ∈ trivialOn n {w} := by
          simp_all [mem_trivialOn, atPlace_componentOn]
        refine LinearMap.ext fun x ↦ ?_
        rw [End.mul_apply, End.mul_apply]
        exact heckeSplit_comm_of_trivialOn hw j hk_triv
      exact D.map_mem_forms _ h_comm hf_Y
    · -- The level is kept: `f` is spherical at `w`, where the level elements are integral.
      have hf_sph : f ∈ sphericalAt (V.formTranslation κ) w :=
        levelSpace_le_sphericalAt hw_off hw_off' (formsOfLevel_le_levelSpace hf)
      refine mem_levelSpace.mpr fun k ↦ ?_
      have h_comp_int :
          (componentOn n (.conjClosure D.places)ᶜ (k : Gf E n)).atPlace w ∈ localIntGL n w := by
        simp_all [mem_stdLevel_iff.mp (levelOf_le_stdLevel k.prop)]
      have h_fix : D.repOff k f = f := by simpa using mem_levelSpace.mp hf_lev k
      calc
        D.repOff k (heckeSplit (V.formTranslation κ) hw j f) =
            heckeSplit (V.formTranslation κ) hw j (D.repOff k f) :=
          (heckeSplit_comm_of_atPlace_mem hw j hf_sph h_comp_int).symm
        _ = (1 : ↥(levelOf L ⊥) →* ℂ) k • heckeSplit (V.formTranslation κ) hw j f := by
          rw [h_fix, MonoidHom.one_apply, one_smul]
  · refine span_le.mpr ?_
    rintro f ⟨hf, P, hP⟩
    obtain ⟨x, hfx, hf_ne⟩ : ∃ x : Isotypic V κ, f ∈ x.val ∧ f ≠ 0 :=
      exists_isotypic_of_isSphericalOff hP
    have hx : x ∈ D.Eigensystem L := ⟨f, ⟨hfx, hf⟩, hf_ne⟩
    exact hN ⟨x, hx⟩ ⟨hfx, hf⟩

/-- Two endomorphisms of the space `New.Patching.BaseLevel.formsOfLevel` L are equal if they agree
on every form that lies in an isotypic space of a system of level L. -/
lemma formEnd_ext {a b : D.FormEnd L}
    (h_agree :
      ∀ (x : D.Eigensystem L) (y : D.formsOfLevel L), ↑y ∈ (x : Isotypic V κ).val → a y = b y) :
    a = b := by
  -- The forms on which `a` and `b` agree contain the isotypic parts, hence everything.
  have h_le : D.formsOfLevel L ≤ (eqLocus a b).map (formsOfLevel L).subtype :=
    formsOfLevel_le_of_eigensystem fun x y ⟨hy_iso, hy_lev⟩ ↦
      ⟨⟨y, hy_lev⟩, h_agree x ⟨y, hy_lev⟩ hy_iso, rfl⟩
  refine LinearMap.ext fun y ↦ ?_
  obtain ⟨z, hz, hz_y⟩ := Submodule.mem_map.mp (h_le y.prop)
  obtain rfl : z = y := Subtype.ext hz_y
  exact hz

/-- The `EllAdicIntegers`-algebra map that sends a function t from the systems of eigenvalues of
level L (`New.Patching.BaseLevel.Eigensystem`) to `PadicAlgCl ℓ` to the operator (in `D.FormEnd L`,
the ℂ-linear endomorphisms; ιℓ : ℂ → `PadicAlgCl ℓ` is the identification fixed by `PadicIso ℓ`) on
`New.Patching.BaseLevel.formsOfLevel` L that multiplies the forms of each system x by the scalar
`ιℓ.symm (t x)`. -/
def systemAction : (D.Eigensystem L → PadicAlgCl ℓ) →ₐ[EllAdicIntegers] D.FormEnd L where
  toFun t :=
    (diagOp t).restrict <|
      formsOfLevel_le_of_eigensystem fun x _ ⟨hf_iso, hf⟩ ↦
        Submodule.mem_comap.2 (diagOp_apply t x hf_iso ▸ smul_mem (formsOfLevel (m := c) (D := D) L)
          (ιℓ.symm (t x)) hf)
  -- Each law is checked on the isotypic spaces, where `diagOp t` is the scalar `ιℓ.symm (t x)`.
  map_one' := formEnd_ext fun x f hf ↦ Subtype.ext (by simp [diagOp_apply _ x hf])
  map_mul' _ _ :=
    formEnd_ext fun x f hf ↦ Subtype.ext (by simp [diagOp_apply _ x hf, smul_smul, mul_comm])
  map_zero' := formEnd_ext fun x f hf ↦ Subtype.ext (by simp [diagOp_apply _ x hf])
  map_add' _ _ := formEnd_ext fun x f hf ↦ Subtype.ext (by simp [diagOp_apply _ x hf, add_smul])
  commutes' _ :=
    formEnd_ext fun x f hf ↦ Subtype.ext (by simp [diagOp_apply _ x hf, ← iota_ell_algebraMap])

/-! ### The Hecke algebra -/

/-- The Hecke algebra: the functions t from the systems of level L to `PadicAlgCl ℓ` whose
operator `systemAction t` (multiplication of the forms of each system x by `ιℓ.symm (t x)`) keeps
the integral forms of `New.Patching.BaseLevel.formsOfLevel` L integral. -/
def heckeAlgebra (L : J → FinPlace E) :
    Subalgebra EllAdicIntegers (Eigensystem (m := c) (D := D) L → PadicAlgCl ℓ) :=
  (D.integralEnd (J := J) L).comap systemAction

/-- The `EllAdicIntegers`-algebra map that sends t in the Hecke algebra to its operator
`systemAction t`, which multiplies the forms of each system x by `ιℓ.symm (t x)` and keeps the
integral forms. -/
def heckeAction : D.heckeAlgebra L →ₐ[EllAdicIntegers] D.integralEnd L :=
  (systemAction.comp (heckeAlgebra L).val).codRestrict (D.integralEnd L) fun t ↦ t.2

/-- The Hecke algebra is closed in the space of functions from the systems of level `L` to
`PadicAlgCl ℓ`. -/
lemma isClosed_heckeAlgebra :
    IsClosed (D.heckeAlgebra L : Set (D.Eigensystem L → PadicAlgCl ℓ)) := by
  classical
  -- Membership of `t` says: for every integral form `f` in `D.formsOfLevel L`, point `g` integral
  -- above `ℓ` and coordinate `i`, the value of `systemAction t f` at `g` and `i` is integral.
  change IsClosed {t : D.Eigensystem L → PadicAlgCl ℓ |
    ∀ f ∈ ellIntegralForms.comap ((formsOfLevel L).subtype.restrictScalars EllAdicIntegers),
      ∀ g ∈ integralAbove n ℓ, ∀ i : WeylIndex n κ.fst,
        NormedField.valuation
          (ιℓ (((systemAction t f : V.forms κ) : Gf E n → WeylIndex n κ.fst → ℂ) g i)) ≤ 1}
  -- an intersection over `f`, `hf`, `g`, `hg` and `i` of sets given by one inequality each
  simp only [Set.ofPred_forall]
  iterate 5 refine isClosed_iInter fun _ ↦ ?_
  refine isClosed_le ?_ continuous_const
  -- the value is a finite sum over the systems `x` of `t x` times a constant, continuous in `t`
  simp [systemAction, diagOp, sumAddHom_apply]
  fun_prop

end New.Patching.BaseLevel

/-!
## Operators at the auxiliary places

Fix base data `D : New.Patching.BaseLevel` (a type of forms at a finite set of places, a multiple
`c` of the orders of all stabilisers) and auxiliary split places `w j` given by
`Q : New.Patching.TaylorWilesPlaces`.
-/

section AuxPlaceOperators

namespace New.Patching.BaseLevel

open Pi Fintype Polynomial Algebra Gf stdLevel MonoidHom Subgroup MulAction Module

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
  {E : Type} [Field E] [CMType E] {n : Type} [Fintype n] [DecidableEq n]
  {V : Space E n 1} {κ : Weight E} {J : Type} [Fintype J] {ν c : ℕ}
  (D : BaseLevel V κ c) [Algebra E Ω]
  (Q : TaylorWilesPlaces E J (ℓ ^ ν)) (j : J)

/-- The isomorphism ∏_j GL_N(k_{w_j}) ≅ ∏_j GL_n(k_{w_j}), N = |n|, that relabels rows and
columns along a chosen ordering of the index set n. -/
abbrev reindexResidueGL {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [Algebra E Ω]
    (Q : TaylorWilesPlaces E J (ℓ ^ ν)) :
    ((j : J) → GL (Fin (card n)) (ResField (Q.place j))) ≃*
      ((j : J) → GL n (ResField (Q.place j))) :=
  MulEquiv.piCongrRight fun j ↦ (reindexGL (R := ResField (Q.place j)) (equivFin n)).symm

/-! ### Operators at one place and the action of the finite groups -/

/-- The operators at `w j`: the endomorphisms of the forms of principal level at the places
`Q.place` that keep the integral forms and agree there with an element of
`localGroupAlgebra (Q.place j)`, the `EllAdicIntegers`-combinations of translations by elements of
G_f supported at `w j` and its conjugate. -/
def localOperators : Subalgebra EllAdicIntegers (D.integralEnd Q.place) where
  carrier :=
    {a : integralEnd Q.place |
      ∃ b : localGroupAlgebra (Q.place j), ∀ y : ↥(formsOfLevel Q.place), (a.1 y).1 = b.1 y}
  mul_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a * b, by simp [ha, hb]⟩
  add_mem' := fun ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, by simp [ha, hb]⟩
  algebraMap_mem' r := ⟨r • 1, by simp⟩

/-- The action of ∏_j GL_N(k_{w_j}), with k_{w_j} = `ResField (Q.place j)` and N = |n|, on forms of
principal level at the places `Q.place`: an element acts by `D.repOff` of a lift to `stdLevel E n`
(`liftResidue`), the translation by its components off `D.places` and its conjugates. It keeps the
integral forms. -/
def residueRep : (∀ j : J, GL (Fin (card n)) (ResField (Q.place j))) →* D.integralEnd Q.place :=
  -- `g` acts through its lift to `stdLevel`, as in the representation `R` on all forms of principal
  -- level
  let R := levelRep (H := ⊥) D.repOff 1 (reindexResidueGL Q).toMonoidHom (by simp)
  { toFun g :=
      ⟨(D.repOff (liftResidue ((reindexResidueGL Q).toMonoidHom g))).restrict fun y hy ↦
          -- the type `D.forms` is kept, as `D.repOff` commutes with the components at `D.places`
          ⟨D.map_mem_forms _ (fun _ ↦ Commute.map (Gf.ext (by aesop)) (V.formTranslation κ)) hy.1,
            (R g ⟨y, hy.2⟩).2⟩,
        -- integral forms are kept, as the lift is integral above `ℓ`
        fun y hy x hx ↦ hy _ (mul_mem hx (stdLevel_le_localLevel
          (componentOn_mem_stdLevel (by simp))))⟩
    map_one' := by
      ext y : 3
      exact (congrArg Subtype.val (LinearMap.congr_fun R.map_one ⟨_, y.2.2⟩) :)
    map_mul' g h := by
      ext y : 3
      exact (congrArg Subtype.val (LinearMap.congr_fun (R.map_mul g h) ⟨_, y.2.2⟩) :) }

variable {D Q j}

private lemma residueRep_apply_coe (g : ∀ j : J, GL (Fin (card n)) (ResField (Q.place j)))
    (y : ↥(formsOfLevel Q.place)) :
    ((D.residueRep Q g).val y : V.forms κ) =
      D.repOff (liftResidue ((reindexResidueGL Q).toMonoidHom g)) y :=
  rfl

/-- A form of principal level at the auxiliary places has the maximal level `stdLevel` off
`D.places` and its conjugates exactly when it is fixed by the group ∏_j GL_N(k_{w_j}), N = |n|. -/
lemma mem_formsOfLevel_empty_iff_residueRep_fixed {y : ↥(formsOfLevel Q.place)} :
    ↑y ∈ D.formsOfLevel ![] ↔
      ∀ g : (j : J) → GL (Fin (card n)) (ResField (Q.place j)), (D.residueRep Q g).val y = y := by
  obtain ⟨hy_Y, hy_level⟩ := Submodule.mem_inf.1 y.prop
  refine ⟨fun hy g ↦ Subtype.ext ?_, fun hy ↦ ⟨hy_Y, ?_⟩⟩
  · -- `D.residueRep Q g` acts through an element `k` of `stdLevel`, which is in the level of no
    -- places and so fixes a form of base level
    have hk_level : (liftResidue ((reindexResidueGL Q).toMonoidHom g) : Gf E n) ∈ levelOf ![] ⊥ :=
      mem_levelOf.2 ⟨(liftResidue _).prop, Subgroup.mem_bot.2 (funext nofun)⟩
    simpa [residueRep_apply_coe] using
      mem_levelSpace.1 (Submodule.mem_inf.1 hy).2 ⟨_, hk_level⟩
  · -- an element `k` of `stdLevel` acts on `y` as its reduction at the auxiliary places does
    rintro ⟨_, k, hk, rfl⟩
    have h_red : (D.residueRep Q ((reindexResidueGL Q).symm (reduceFamily Q.place k))).val y =
      D.repOff k y :=
      apply_liftResidue_eq (χ := 1) ⟨_, hy_level⟩ k ((reindexResidueGL Q).right_inv _).symm
    simpa [hy] using h_red.symm

/-- An operator at `w j` commutes with the operator of every element t of the Hecke algebra. -/
lemma localOperators.commute_heckeAction {a : integralEnd Q.place} (ha : a ∈ D.localOperators Q j)
    (t : heckeAlgebra Q.place) :
    Commute (heckeAction t) a := by
  -- test on forms `y` of one system `x`: `a` keeps these, and `heckeAction t` acts on them by a
  -- scalar
  obtain ⟨b, hb⟩ := ha
  refine Subtype.ext (formEnd_ext fun x y hy ↦ Subtype.ext ?_)
  have hby : b.val y ∈ (x : Isotypic V κ).val := Isotypic.map_mem b.prop hy
  simp [BaseLevel.heckeAction, systemAction, diagOp_apply _ x, hb, hy, hby]

/-! ### Auxiliary places off the level

In the results below, the hypothesis `hQ`, where it is assumed, says that every place `w j` is off
the base level: `w j` and its conjugate are not in `D.places`, `w j` is not above `ℓ`, and the forms
of base level in each system have its eigenvalues at `w j` (`New.Patching.BaseLevel.IsOffLevel`).
-/

/-- Let the places `w j` be off the base level. For an integral matrix `k` at `w j`, its reduction
placed at the index `j` acts on a form `y` of principal level as `k` does in the representation
`New.Patching.localFormRep` of GL_N(E_{w j}) on forms. -/
lemma residueRep_mulSingle [DecidableEq J] (hQ : ∀ j : J, D.IsOffLevel ![] (Q.place j))
    (k : localIntGL (Fin (card n)) (Q.place j)) (y : ↥(formsOfLevel Q.place)) :
    ((D.residueRep Q (Pi.mulSingle j (reduceGL k))).val y).val =
      localFormRep V κ (Q.apart.star_ne j j) k y := by
  -- `k'` is `k` with indices in `n`; `x` has component `k'` at `w j` and is `1` off `w j` and
  -- its conjugate, so `D.repOff` does not cut it
  have hk'_int : (reindexGL (equivFin n)).symm (k : GL (Fin (card n)) (LocField (Q.place j))) ∈
      localIntGL n (Q.place j) := by
    obtain ⟨m, hm⟩ := k.prop
    exact ⟨reindexGL (equivFin n).symm m, by rw [← hm]; rfl⟩
  let k' : localIntGL n (Q.place j) := ⟨(reindexGL (equivFin n)).symm k, hk'_int⟩
  let x : stdLevel E n := ⟨ofSplitPlace (Q.apart.star_ne j j) k', by simp⟩
  have x_red : reduceFamily Q.place x = reindexResidueGL Q (mulSingle j (reduceGL k)) :=
    (reduceFamily_ofSplitPlace j k').trans (Function.update_eq_iff.2 (by aesop))
  obtain ⟨h_w_notMem, h_star_w_notMem, -, -⟩ := hQ j
  have x_off : (x : Gf E n) ∈ trivialOn n D.places :=
    supportedOn_compl.le (supportedOn_mono (by simp [h_w_notMem, h_star_w_notMem])
      (ofSplitPlace_mem_supportedOn _ _))
  calc _ = D.repOff x y :=
        apply_liftResidue_eq (χ := 1) ⟨_, (Submodule.mem_inf.1 y.prop).2⟩ x x_red
    _ = V.formTranslation κ x y := by rw [repOff_eq_of_mem_trivialOn _ x_off]

/-- Let the places `w j` be off the base level. An element `g` of GL_N(k_{w j}), placed at the
index `j`, acts by an operator at `w j`. -/
lemma residueRep_mem_localOperators [DecidableEq J] (hQ : ∀ j : J, D.IsOffLevel ![] (Q.place j))
    (g : GL (Fin (card n)) (ResField (Q.place j))) :
    D.residueRep Q (Pi.mulSingle j g) ∈ D.localOperators Q j := by
  -- `g` is the reduction of an integral `k`, and acts as the translation by `k` at `w j`
  obtain ⟨k, rfl⟩ := reduceGL_surjective g
  exact ⟨⟨localFormRep V κ (Q.apart.star_ne j j) k, subset_adjoin ⟨_, by simp, rfl⟩⟩,
    residueRep_mulSingle hQ k⟩

omit [ThePrime ℓ] [PadicIso ℓ] [Fintype J] in
/-- An element `k` of the principal level at the places `Q.place` has its component at `w j`,
reindexed along the chosen ordering of `n`, in the pro-p Iwahori group: it is integral and reduces
to `1`. -/
private lemma reindexGL_atPlace_mem_proIwahori_of_mem_levelOf {k : Gf E n}
    (hk : k ∈ levelOf Q.place ⊥) : reindexGL (equivFin n) (k.atPlace (Q.place j)) ∈ proIwahori := by
  obtain ⟨m, hm⟩ := mem_stdLevel_iff.1 (levelOf_le_stdLevel hk) (Q.place j)
  obtain ⟨hk_Kf, hk_red⟩ := mem_levelOf.1 hk
  have h_red_one : reduceFamily Q.place ⟨k, hk_Kf⟩ = 1 := Subgroup.mem_bot.1 hk_red
  refine ⟨⟨reindexGL (equivFin n) m, by rw [← hm]; rfl⟩, ?_⟩
  -- `reduceAt_eq_zero` is applied by hand: as a `simp` lemma it makes the kernel check very slow
  have h_entries := fun a b ↦ reduceAt_eq_zero.1 ((map_eq_one n).1 (congrFun h_red_one j) a b)
  simp [reindex_equiv (equivFin n), Gf.atPlace, apply_ite, ite_apply,
    Matrix.one_apply] at h_entries ⊢
  grind

omit [Fintype J] in
/-- Let `w j = Q.place j` be the Taylor–Wiles places, all off the base level (`D.IsOffLevel ![]`).
Let `a` be an operator at `w j`, i.e. an element of `D.localOperators Q j`: an endomorphism of the
forms `formsOfLevel Q.place` that keeps the integral forms and agrees with an
`EllAdicIntegers`-combination of translations supported at `w j` and its conjugate. If the values of
`a` are fixed by the pro-p Iwahori group I₁ = `proIwahori` in the representation
ρ = `New.Patching.localFormRep` of GL_N(E_{w j}), N = |n|, then for g in GL_N(E_{w j}) (stated over
`(Q.frobData j).place`, which is `Q.place j` by definition) and G in `EllAdicIntegers[X]` there is
an operator `b` at `w j` with b(y) = G([I₁gI₁])(a(y)) for all y, where
[I₁gI₁] = `heckeCoset ρ.ρ proIwahori g` is the Hecke operator of the double coset I₁gI₁. -/
lemma exists_localOperators_aeval_hecke (hQ : ∀ j : J, D.IsOffLevel ![] (Q.place j))
    {a : D.integralEnd Q.place} (ha : a ∈ D.localOperators Q j)
    (g : GL (Fin (card n)) (LocField (Q.frobData j).place)) (G : EllAdicIntegers[X]) :
    let ρ := localFormRep V κ (Q.apart.star_ne j j)
    (∀ y : ↥(formsOfLevel Q.place), (a.val y).val ∈ levelSpace ρ.ρ proIwahori) →
    ∃ b ∈ D.localOperators Q j,
      ∀ y : ↥(formsOfLevel Q.place),
        (b.val y).val = aeval (heckeCoset ρ.ρ proIwahori g) G (a.val y).val := by
  -- The operator `T = G([I₁gI₁])` lies in the algebra of operators at `w j`. It keeps the type
  -- `D.forms`, and on forms fixed by I₁ at `w j` it commutes with the principal level; so `T ∘ a`
  -- keeps the forms of principal level, and it is an operator at `w j`.
  intro ρ ha_fix
  obtain ⟨h_w_notMem, h_star_w_notMem, h_ell_notMem, -⟩ := hQ j
  -- a polynomial in the Hecke operator comes from the group at `w j` and keeps the forms fixed
  -- by `proIwahori`, since the Hecke operator does
  obtain ⟨T_local, T_fix⟩ :
      aeval (heckeCoset ρ.ρ proIwahori g) G ∈
        localGroupAlgebra (Q.place j) ⊓
          endPreserving (.restrictScalars EllAdicIntegers (levelSpace ρ.ρ proIwahori)) := by
    refine adjoin_singleton_le ?_ (G.aeval_mem_adjoin_singleton EllAdicIntegers _)
    exact ⟨heckeFun_mem_localGroupAlgebra (Q.apart.star_ne j j) _, fun _ ↦
      (isHeckeFunction_doubleCoset isOpen_proIwahori g).heckeFun_mem⟩
  -- The operator is abstracted with `generalize`: otherwise the kernel unfolds the Hecke operator.
  generalize aeval (heckeCoset ρ.ρ proIwahori g) G = T at *
  -- `T` commutes with the components at `D.places`, which are trivial at `w j`: it keeps the type
  -- `D.forms`
  have mem_type (y : D.formsOfLevel Q.place) : T (a.val y).val ∈ D.forms := by
    obtain ⟨hy_Y, -⟩ := Submodule.mem_inf.1 (a.val y).prop
    have h_comm_S (k : stdLevel E n) : Commute (V.formTranslation κ (componentOn n D.places k)) T :=
      commute_of_mem_localGroupAlgebra T_local (by simp [h_w_notMem, h_star_w_notMem])
    exact D.map_mem_forms T h_comm_S hy_Y
  have mem_level (y : D.formsOfLevel Q.place) :
      T (a.val y).val ∈ levelSpace D.repOff (levelOf Q.place ⊥) := by
    obtain ⟨-, hy_level⟩ := Submodule.mem_inf.1 (a.val y).prop
    refine mem_levelSpace.2 fun k ↦ ?_
    have k_iwahori : reindexGL (equivFin n) ((k : Gf E n).atPlace (Q.place j)) ∈ proIwahori :=
      reindexGL_atPlace_mem_proIwahori_of_mem_levelOf k.prop
    -- `x` has the component of `k⁻¹` at `w j`; it fixes `a y` and `T (a y)`
    let x : Gf E n := ofSplitPlace (Q.apart.star_ne j j) ((k : Gf E n)⁻¹.atPlace _)
    have x_fix (z : V.forms κ) (hz : z ∈ levelSpace ρ.ρ proIwahori) :
        V.formTranslation κ x z = z := by
      simpa [ρ, x] using hz ⟨_, k_iwahori⟩⁻¹
    -- the part of `k` off `D.places`, times `x`, is trivial at `w j`, so it commutes with `T`
    have h_comm : Commute (D.repOff k * V.formTranslation κ x) T := by
      rw [comp_apply, ← map_mul]
      exact commute_of_mem_localGroupAlgebra T_local (by simp [x, h_w_notMem, h_star_w_notMem])
    calc D.repOff k (T (a.val y).val)
      _ = D.repOff k (V.formTranslation κ x (T (a.val y).val)) := by
        rw [x_fix _ (T_fix _ (ha_fix y))]
      _ = T (D.repOff k (V.formTranslation κ x (a.val y).val)) := LinearMap.congr_fun h_comm.eq _
      _ = _ := by rw [x_fix _ (ha_fix y), mem_levelSpace.1 hy_level k, map_smul]
  -- the operator is `T ∘ a`; it keeps integral forms, as `w j` is not above `ℓ`
  obtain ⟨a', ha'⟩ := ha
  let b : D.integralEnd Q.place :=
    ⟨(T ∘ₗ (D.formsOfLevel Q.place).subtype ∘ₗ a.val).codRestrict _ fun y ↦
      ⟨mem_type y, mem_level y⟩,
      fun y hy ↦ localGroupAlgebra_le_endPreserving h_ell_notMem T_local _ (a.prop y hy)⟩
  refine ⟨b, ⟨⟨T, T_local⟩ * a', fun y ↦ ?_⟩, fun y ↦ rfl⟩
  exact congrArg T (ha' y)

/-- Let `Γ`, `K` be subgroups of `G`, let `π` map `K` and let `ψ` embed a finite group `Δ` into
`H`, and let `c` be a multiple of the orders of all the groups `classAut Γ K g` = Γ ∩ gKg⁻¹. Then
there are weights `u q d` in ℕ, for `q` in `G ⧸ Γ` and `d` in `Δ`, such that
`u (y⁻¹ • q) 1 = u q d` whenever `y` in `K` has `π y = ψ d⁻¹`, and the weights `u q d` add up to
`c` over `d` for each `q`. -/
lemma exists_orbit_weight {G H Δ : Type*} [Group G] [Group H] [Group Δ] [Fintype Δ]
    {Γ K : Subgroup G} (π : K →* H) {ψ : Δ →* H} (hψ : Function.Injective ψ) {c : ℕ}
    (h_aut : ∀ g : G, Nat.card (classAut Γ K g) ∣ c) :
    ∃ u : G ⧸ Γ → Δ → ℕ,
      (∀ (q : G ⧸ Γ) (y : K) (d : Δ), π y = ψ d⁻¹ → u (y⁻¹ • q) 1 = u q d) ∧
      ∀ q : G ⧸ Γ, ∑ d : Δ, u q d = c := by
  classical
  -- The preimage of `ψ.range` in `K` acts on `G ⧸ Γ`. Choose `x q` that moves `q` to the chosen
  -- point of its orbit, and let `A q` be the image of the stabiliser of that point. The weight is
  -- `c / #(ψ⁻¹ (A q))` on the coset of the `d` with `π (x q) / ψ d ∈ A q`, and `0` elsewhere.
  have h_out : ∀ a : G ⧸ Γ, orbitRel (comap π ψ.range) (G ⧸ Γ) ⟦a⟧.out a :=
    Quotient.mk_out (s := orbitRel (ψ.range.comap π) (G ⧸ Γ))
  choose x hx using h_out
  let A (q : G ⧸ Γ) : Subgroup H := (stabilizer K ((x q).val • q)).map π
  refine ⟨fun q d ↦ if π (x q) / ψ d ∈ A q then c / card ((A q).comap ψ) else 0, fun q y d hy ↦ ?_,
    fun q ↦ ?_⟩
  · -- `y⁻¹ • q` and `q` lie in one orbit, so they have the same chosen point
    have h_point : (x (y⁻¹ • q)).val • y⁻¹ • q = (x q).val • q := by
      simp only [← Subgroup.smul_def, hx]
      have hy_mem : y ∈ comap π ψ.range := ⟨d⁻¹, hy.symm⟩
      exact congrArg Quotient.out (Quotient.sound ⟨(⟨y, hy_mem⟩ : comap π ψ.range)⁻¹, rfl⟩)
    have h_stab_mem :
        (↑(x (y⁻¹ • q)) * y⁻¹ / ↑(x q) : K) ∈ stabilizer K ((x q).val • q) := by
      simp [mul_smul, h_point, division_def]
    have h_mem : π (x (y⁻¹ • q) * y⁻¹ / x q) ∈ A q := mem_map_of_mem π h_stab_mem
    simp [hy, h_point, A, ← mul_mem_cancel_left (y := π (x q) / ψ d) h_mem]
  · -- the stabiliser of the point `g Γ` in `K` embeds in `classAut Γ K g⁻¹` by conjugation
    have h_stab (p : G ⧸ Γ) : Nat.card (stabilizer K p) ∣ c := by
      obtain ⟨g, rfl⟩ : ∃ a : G, (a : G ⧸ Γ) = p := QuotientGroup.mk_surjective p
      let f : K →* G := (MulAut.conj g⁻¹).toMonoidHom.comp K.subtype
      have h_le : stabilizer K (g : G ⧸ Γ) ≤ (classAut Γ K g⁻¹).comap f := fun k hk ↦ by
        simpa [f, classAut, mul_assoc] using QuotientGroup.eq.mp hk.symm
      calc _ ∣ Nat.card ((classAut Γ K g⁻¹).comap f) := card_dvd_of_le h_le
        _ ∣ Nat.card (classAut Γ K g⁻¹) := card_comap_dvd_of_injective _ f (by simp [f])
        _ ∣ c := h_aut g⁻¹
    have h_dvd : Nat.card ((A q).comap ψ) ∣ c :=
      calc Nat.card ((A q).comap ψ)
        _ ∣ Nat.card (A q) := (A q).card_comap_dvd_of_injective _ hψ
        _ ∣ Nat.card (stabilizer K ((x q).val • q)) := (stabilizer K _).card_map_dvd π
        _ ∣ c := h_stab _
    -- with `ψ k = π (x q)`, substitute `d⁻¹ * k` for `d`: the coset becomes `ψ⁻¹ (A q)`
    obtain ⟨k, hk⟩ : ∃ k : Δ, ψ k = π (x q) := (x q).prop
    have h_cond (d : Δ) : π (x q) / ψ ((Equiv.divLeft k).symm d) ∈ A q ↔ d ∈ (A q).comap ψ := by
      simp [← hk]
    rw [← (Equiv.divLeft k).symm.sum_comp]
    simp_rw [h_cond]
    -- the weight `c / #(ψ⁻¹ (A q))` is summed over `ψ⁻¹ (A q)`, which has order dividing `c`
    simpa [Finset.sum_ite, Fintype.card_subtype] using Nat.mul_div_cancel' h_dvd

/-- Higman's criterion up to c, for auxiliary places `w j` off the base level: for a finite group Δ
embedded by φ in ∏_j GL_N(k_{w_j}), N = |n|, some operator Ψ on forms of principal level that keeps
the integral forms has ∑_{g∈Δ} g⁻¹Ψg = c, with g acting by `New.Patching.BaseLevel.residueRep` and c
the common multiple of the stabiliser orders fixed in `D`. -/
lemma exists_higman_operator (hQ : ∀ j : J, D.IsOffLevel ![] (Q.place j))
    {Δ : Type*} [Group Δ] [Fintype Δ]
    (φ : Δ →* ∀ j : J, GL (Fin (card n)) (ResField (Q.place j))) (hφ : Function.Injective φ) :
    ∃ Ψ : D.integralEnd Q.place, ∑ g : Δ,
      D.residueRep Q (φ g⁻¹) * Ψ * D.residueRep Q (φ g) = c := by
  -- `Ψ` multiplies a form by the weight `g ↦ u g⁻¹ 1` of `exists_orbit_weight`. Conjugated by
  -- `φ d` it multiplies by `u g⁻¹ d`, and these numbers add up to `c`.
  obtain ⟨u, h_shift, h_sum⟩ := exists_orbit_weight (reduceFamily Q.place)
    (ψ := (reindexResidueGL Q).toMonoidHom.comp φ) ((reindexResidueGL Q).injective.comp hφ)
    D.card_aut_dvd
  -- cutting off the components at `D.places` does not change the reductions at the auxiliary places
  have h_cut (x : stdLevel E n) :
      reduceFamily Q.place ⟨_, componentOn_mem_stdLevel (S := (.conjClosure D.places)ᶜ) x.prop⟩ =
        reduceFamily Q.place x :=
    funext fun j ↦ (div_mem_ker_iff _).1 (reduceAt_eq_one_of_atPlace (by simp [forall_and.1 hQ]))
  -- the weight is invariant under the principal level
  have h_inv (q : Gf E n ⧸ V.Γf) (x : Gf E n) (hx : x ∈ levelOf Q.place ⊥) :
      u (x⁻¹ • q) 1 = u q 1 :=
    h_shift q ⟨x, (mem_levelOf.1 hx).1⟩ 1 (by simpa using (mem_levelOf.1 hx).2)
  -- for `x` in the principal level that fixes `f`, the weighted `f` has at `g x` its value at `g`
  have h_weight_mul (f : Gf E n → WeylIndex n κ.fst → ℂ) (x : Gf E n)
      (hx_stab : ∀ g : Gf E n, f (g * x) = f g) (hx_level : x ∈ levelOf Q.place ⊥) (g : Gf E n) :
      u (x⁻¹ • ↑g⁻¹) 1 • f (g * x) = u ↑g⁻¹ 1 • f g := by
    rw [h_inv ↑g⁻¹ x hx_level, hx_stab g]
  -- multiplication by the weight keeps forms: the weight ignores rational points, and the product
  -- is fixed by the stabiliser of `f` intersected with the principal level, which is open
  let T : End ℂ (V.forms κ) :=
    .restrict ((fun g : Gf E n ↦ u ↑g⁻¹ 1) • 1) fun f hf ↦
      ⟨(rightStabilizer _ ⊓ levelOf Q.place ⊥).isOpen_mono
          (fun x hx g ↦ h_weight_mul f x hx.left hx.right g) (.and hf.left isOpen_levelOf),
        by simp [hf.right _, -nsmul_eq_mul]⟩
  have h_comm (k : Gf E n) (hk : k ∈ levelOf Q.place ⊥) : Commute (V.formTranslation κ k) T := by
    refine LinearMap.ext fun f ↦ Subtype.ext (funext fun g ↦ ?_)
    -- at `g` the sides are the weights at `g k` and at `g` times `f (g k)`; they agree by `h_inv`
    exact congrArg (fun w : ℕ ↦ w • (f : Gf E n → WeylIndex n κ.fst → ℂ) (g * k)) (h_inv ↑g⁻¹ k hk)
  -- so `T` keeps the type at `D.places` and the principal level
  have hT : ∀ f ∈ D.formsOfLevel Q.place, T f ∈ D.formsOfLevel Q.place := by
    intro f hf
    obtain ⟨hf_Y, hf_level⟩ := Submodule.mem_inf.1 hf
    refine ⟨D.map_mem_forms T (fun k ↦ h_comm _ ?_) hf_Y, map_mem_levelSpace_of_commute hf_level ?_⟩
    · -- the part of `k` at `D.places` is trivial at the places `w j`, which are off `D.places`
      exact inf_trivialOn_le_levelOf ⟨componentOn_mem_stdLevel k.prop, by simp [forall_and.1 hQ]⟩
    · rintro ⟨_, x, hx, rfl⟩
      exact h_comm _ ⟨_, (h_cut x).trans hx, rfl⟩
  -- at `g`, `T f` agrees with an integer multiple of `f`, so `T` keeps the integral forms
  use ⟨T.restrict hT, fun f hf g ↦ nsmul_mem hf (u ↑g⁻¹ 1) g⟩
  ext y g i
  -- evaluate at `y`, `g`, `i`, write `c` as `∑ d, u g⁻¹ d`, and compare term by term
  let f : Gf E n → WeylIndex n κ.fst → ℂ := (y : V.forms κ)
  suffices h_terms : ∑ d : Δ,
      (((D.residueRep Q (φ d⁻¹)).val (T.restrict hT ((D.residueRep Q (φ d)).val y)) : V.forms κ) :
        Gf E n → WeylIndex n κ.fst → ℂ) g i = ∑ d : Δ, u ↑g⁻¹ d • f g i by
    simpa [f, ← h_sum ↑g⁻¹, -CharP.cast_eq_zero] using h_terms
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have h_cancel : D.residueRep Q (φ d⁻¹) * D.residueRep Q (φ d) = 1 := map_mul_eq_one _ (by simp)
  -- `D.residueRep Q (φ d⁻¹)` translates by `k`, the part off `D.places` of a lift of `φ d⁻¹`; this
  -- turns the weight into `u g⁻¹ d`
  let k : stdLevel E n := ⟨_, componentOn_mem_stdLevel (S := (.conjClosure D.places)ᶜ)
    (liftResidue (((reindexResidueGL Q).toMonoidHom.comp φ) d⁻¹)).prop⟩
  have h_weight : u (k⁻¹ • ↑g⁻¹) 1 = u ↑g⁻¹ d :=
    h_shift ↑g⁻¹ k d ((h_cut _).trans (reduceFamily_liftResidue _))
  -- by definition of `T` the left side is the weight at `g k` times the value of the composite
  calc _ = u (k⁻¹ • ↑g⁻¹) 1 • ((((D.residueRep Q (φ d⁻¹) * D.residueRep Q (φ d)).val y :
          V.forms κ) : Gf E n → WeylIndex n κ.fst → ℂ) g i) := rfl
    _ = u ↑g⁻¹ d • f g i := by
      rw [h_weight, h_cancel]
      rfl

end New.Patching.BaseLevel

end AuxPlaceOperators

end
