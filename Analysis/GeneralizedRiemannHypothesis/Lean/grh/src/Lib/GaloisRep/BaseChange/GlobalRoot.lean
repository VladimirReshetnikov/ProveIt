import Lib.ClassField.Global.CMSplittingCharacters
import Lib.ClassField.Global.ExistenceTheorem
import Lib.GaloisRep.BaseChange.CommutingHeckeFamilies
import Lib.General.NumberTheory.CMFields

/-!
# Idele Hasse principle, unitary roots and rationality of adelic roots up to coboundary

The main setting is a cyclic extension `E'/E` of CM fields of prime degree with character `μ`
(`New.IsStep`: `μ` kills `Eˣ`, and each idele `t` of `E` with `μ (t * star t) = 1` is a norm from
`E'` times an element of `Eˣ`) and Galois automorphism `σ`. For a unitary matrix `γ` and a
polynomial `z`, `New.IsRootQuotient γ z a` means `a * z(γ)ᴴ = z(γ)`. The file proves a Hasse
principle for ideles in a single CM field `L` and develops the calculus of this relation. It
combines the two to show that an adelic root for a `σ`-fixed characteristic polynomial is rational
up to a coboundary.

## Main definitions and results

* `New.exists_isSelfAdjoint_principalIdele_mul`: an adele `w` with `w = x * star w`, `x` in `L`,
  becomes conjugation invariant after multiplication by an element of `Lˣ`.
* `New.IsStep.exists_isSelfAdjoint_of_mem_kerCompNorm`: the twisted form, for an idele in
  `kerCompNorm L μ` whose norm under a Galois automorphism `g` has this property, where `x` is fixed
  by `g` and `E'[x] = ⊤`. It uses the Artin map, Hasse's norm theorem and Hilbert 90 for ideles.
* `New.U.existsUnique_isRootQuotient`: if `z(γ)` is invertible there is exactly one unitary `a`.
* `New.exists_global_root`: let `z` be a root for `P`, where `P` is the characteristic polynomial of
  a unitary matrix over `E'` and is fixed by `σ`. Then there are a rational `w` and an adelic `c`
  with the following property. Let `x = w * z * σ c`. At every adelic unitary `γ` killed by the
  radical of `P`, `x(γ)` is invertible, and `a = x(γ) / x(γ)ᴴ` satisfies `a * c(γ)ᴴ = c(γ)`.

Notions from other files:
* `New.adeleMap`: For an embedding f: K → L of number fields, the induced ring homomorphism from the
  finite adeles of K to those of L.
* `New.kerCompNorm`: The group of finite ideles of E' whose norm to E is killed by μ.
* `New.U.mapEnd`: The endomorphism of the unitary group {g : gᴴg = 1} over R given by applying
  entrywise a ring endomorphism σ commuting with the involution.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` for sources.
-/

/-!
## The Hasse principle for ideles in one CM field

The Hasse principle behind `New.exists_global_root`, in a single CM field `L`.
-/

section IdeleHassePrinciple

open Subgroup NumberField Algebra IntermediateField New.Cohomology IsGalois ComplexEmbedding Finset

/-- Let `L` be a CM field. If the finite adele `w` satisfies `w = x * star w` with `x` in `L`, then
`y * w` is invariant under conjugation for some `y` in `Lˣ`. -/
lemma New.exists_isSelfAdjoint_principalIdele_mul {L : Type*} [Field L] [NumberField L]
    [IsCMField L] (x : L) {w : 𝔸f L} (hw : w = (x : 𝔸f L) * star w) :
    ∃ y : Lˣ, IsSelfAdjoint ((principalIdele y : (𝔸f L)ˣ) * w) := by
  -- Take `y = star (z + x * star z)` with `z + x * star z ≠ 0`. Since `star x * w = star w`,
  -- `y * w = star z * w + z * star w`, which is invariant under conjugation.
  have h_star : algebraMap L (𝔸f L) (star x) * w = star w := by simpa using (congrArg star hw).symm
  obtain ⟨z, hz⟩ : ∃ z : L, IsUnit (z + x * star z) := by
    -- `z = 1` works unless `x = -1`, and then any `z ≠ star z` works
    by_cases hx : x = -1
    · simpa [hx, sub_eq_add_neg] using exists_isUnit_sub_star (E := L)
    · refine ⟨1, Ne.isUnit fun h ↦ hx ?_⟩
      rw [star_one, mul_one] at h
      exact eq_neg_of_add_eq_zero_right h
  have h_mul : (principalIdele hz.star.unit : (𝔸f L)ˣ) * w =
      star (z : 𝔸f L) * w + (z : 𝔸f L) * star w := by
    -- with `star w = star x * w`, both sides are `(star z + star x * z) * w`
    have h_ring : (algebraMap L (𝔸f L) (star z) +
          algebraMap L (𝔸f L) (star x) * algebraMap L (𝔸f L) z) * w =
        algebraMap L (𝔸f L) (star z) * w +
          algebraMap L (𝔸f L) z * (algebraMap L (𝔸f L) (star x) * w) := by
      ring
    simpa [← h_star] using h_ring
  refine ⟨hz.star.unit, ?_⟩
  rw [h_mul]
  simp [IsSelfAdjoint, add_comm, mul_comm]

/-- The norm from `L` to the fixed field of `g` is the product of the conjugates under the powers
of `g`. -/
lemma New.finAdeleIncl_adeleNorm_fixedField_zpowers {E L : Type} [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra E L] (g : Gal(L/E)) (w : 𝔸f L) :
    finAdeleIncl (fixedField (zpowers g)) L (adeleNorm (fixedField (zpowers g)) L w) =
      ∏ i ∈ range (orderOf g), adeleMap (↑(g ^ i) : L →+* L) w := by
  have : IsGalois (fixedField (zpowers g)) L := of_fixed_field L (zpowers g)
  let e : Fin (orderOf g) ≃ Gal(L/fixedField (zpowers g)) :=
    (finEquivZPowers (isOfFinOrder_of_finite g)).trans (subgroupEquivAlgEquiv (zpowers g)).toEquiv
  rw [finAdeleIncl_adeleNorm, prod_range]
  exact (e.prod_comp fun σ ↦ adeleMap (σ : L →+* L) w).symm

/-- Let `K` be the fixed field of `g ∈ Gal(L/E)`, and let `t` be a finite idele of `L` whose norm to
`K` is the principal idele of a totally positive `k`. Then `z / t * g c = c` for some `z` in `Lˣ`
and some invertible finite adele `c`. -/
lemma New.exists_principalIdele_div_mul_adeleMap_eq {E L : Type} [Field E] [NumberField E] [Field L]
    [NumberField L] [Algebra E L] {g : Gal(L/E)} {t : (𝔸f L)ˣ} {k : (fixedField (zpowers g))ˣ}
    (hk_pos : IsTotallyPositive (k : fixedField (zpowers g)))
    (hk : principalIdele k = t.map (adeleNorm (fixedField (zpowers g)) L)) :
    ∃ (z : Lˣ) (c : 𝔸f L), IsUnit c ∧
      ↑(principalIdele z / t) * adeleMap (g : L →+* L) c = c := by
  let K : IntermediateField E L := fixedField (zpowers g)
  have : IsGalois K L := of_fixed_field L (zpowers g)
  have : IsCyclic Gal(L/K) := (subgroupEquivAlgEquiv (zpowers g)).isCyclic.mp (isCyclic_zpowers g)
  -- `k` is the norm of an idele of `L`, so a local norm everywhere, so a norm from `L`
  obtain ⟨z, rfl⟩ : ∃ z : Lˣ, z.map (norm K) = k := by
    refine hasse_norm k (fun v ↦ ?_) hk_pos
    have hk_v : algebraMap K (LocField v) k = adeleNorm K L t v :=
      congrArg (fun x : (𝔸f K)ˣ ↦ (x : 𝔸f K) v) hk
    rw [hk_v]
    exact adeleNorm_mem_closure
  -- `z / t` has norm one, so Hilbert 90 for ideles applies
  refine ⟨z, hilbert90_finite_idele ?_⟩
  rw [← finAdeleIncl_adeleNorm_fixedField_zpowers, ← Units.coe_map, map_div, ← hk,
    map_adeleNorm_principalIdele, div_self', Units.val_one, map_one]

/-- Let `L` be a CM field and `g` an automorphism of `L` over the CM field `E`. Then the fixed field
of `g` is a CM field: it is stable under conjugation, which commutes with `g`. -/
lemma New.isCMField_fixedField_zpowers {E L : Type} [Field E] [NumberField E] [IsCMField E]
    [Field L] [NumberField L] [IsCMField L] [Algebra E L] (g : Gal(L/E)) :
    IsCMField (fixedField (zpowers g)) := by
  refine isCMField_of_forall_exists_conj E fun y : fixedField (zpowers g) ↦
    ⟨⟨star y.val, fun a ↦ ?_⟩, fun φ ↦ ?_⟩
  · -- `star y` is fixed by `g`, as `y` is and conjugation commutes with `g`
    exact (map_star_CM a.val.toRingHom y).trans (congrArg star (y.property a))
  · simp [← lift_algebraMap_apply L φ]

/-- Hasse principle in one CM field. Let `E'/E` be a step with character `μ` (`IsStep`): `E`
contains a primitive 5040th root of unity, `E'` is a CM field Galois over `E` of prime degree, and
`μ` is a finite idele character of `E` with open kernel, trivial on `Eˣ`. Let `L = E'[x]` be a CM
field, and let `g ∈ Gal(L/E)` fix `x` and have order `n`. Let `u` be a finite idele of `L` with
`μ (N_{L/E} u) = 1` whose norm `N = ∏_{i < n} g ^ i u` satisfies `N = x * star N`. Then
`star c * (z * u * g c)` is self-adjoint for `star` for some `z` in `Lˣ` and some invertible finite
adele `c`. -/
lemma New.IsStep.exists_isSelfAdjoint_of_mem_kerCompNorm {E E' L : Type} [Field E] [NumberField E]
    [IsCMField E] [Field E'] [NumberField E'] [IsCMField E'] [Field L] [NumberField L] [IsCMField L]
    [Algebra E E'] [Algebra E' L] [Algebra E L] [IsScalarTower E E' L]
    {μ : (𝔸f E)ˣ →* ℂˣ} (hμ : IsStep E' μ) {g : Gal(L/E)} {x : L}
    (hx : g x = x) (hL : E'[x] = ⊤) (u : (𝔸f L)ˣ) (hu : u ∈ kerCompNorm L μ)
    (hN :
      let N : 𝔸f L := ∏ i ∈ range (orderOf g), adeleMap (↑(g ^ i) : L →+* L) u
      N = (x : 𝔸f L) * star N) :
    ∃ (z : Lˣ) (c : 𝔸f L), IsUnit c ∧
      IsSelfAdjoint (star c * (↑(principalIdele z * u) * adeleMap (g : L →+* L) c)) := by
  -- Let `K` be the fixed field of `g`. The norm of `u` to `K` is `a / y * (w * star w)`; class
  -- field theory shows that `w` is a norm from `L` up to `Kˣ`, say of `s`. Hasse's norm theorem
  -- and Hilbert 90 for ideles then write `z * u / (s * star s)` as a coboundary.
  let K : IntermediateField E L := fixedField (zpowers g)
  -- an embedding of `L` into `Ω` places all four fields inside `Ω`
  algebraize [Ω.fieldEmb L, (Ω.fieldEmb L).comp (algebraMap E L),
    (Ω.fieldEmb L).comp (algebraMap E' L)]
  have : IsScalarTower E E' Ω := IsScalarTower.to₁₂₄ E E' L Ω
  lift x to K using fun a ↦ smul_eq_self_of_mem_zpowers a.property hx
  have : IsGalois K L := of_fixed_field L (zpowers g)
  have h_cyc : IsCyclic Gal(L/K) :=
    (subgroupEquivAlgEquiv (zpowers g)).isCyclic.mp (isCyclic_zpowers g)
  have : IsCMField K := isCMField_fixedField_zpowers g
  have h_norm : finAdeleIncl K L (adeleNorm K L u) =
      ∏ i ∈ range (orderOf g), adeleMap (↑(g ^ i) : L →+* L) u :=
    finAdeleIncl_adeleNorm_fixedField_zpowers g u
  -- the hypothesis on the norm, pulled back from `L` to `K`
  have hN_map : adeleMap (algebraMap K L) (adeleNorm K L u) =
      adeleMap (algebraMap K L) (x * star (adeleNorm K L u)) := by
    simpa [adeleMap_star, h_norm] using hN
  have hN' : adeleNorm K L u = x * star (adeleNorm K L u) :=
    adeleMap_injective (algebraMap K L) hN_map
  -- `y` times the norm of `u` is invariant under conjugation, and such an idele of the CM field `K`
  -- has the form `a * (w * star w)` (`exists_eq_principalIdele_mul_mul_star_of_star_eq`)
  obtain ⟨y, hy⟩ := exists_isSelfAdjoint_principalIdele_mul x hN'
  let : CMType K := {}
  obtain ⟨a, w, hw⟩ : ∃ (a : Kˣ) (w : (𝔸f K)ˣ),
      principalIdele y * u.map (adeleNorm K L) = principalIdele a * (w * star w) :=
    exists_eq_principalIdele_mul_mul_star_of_star_eq hy
  -- the characters `χ`, `ψ` cut out `E' / E` and `L / K`
  obtain ⟨χ, hχ⟩ : ∃ χ : QZChar Gal(Ω/E), IsProGalois (QZChar.ker χ) E' Ω :=
    exists_isProGalois_ker_of_isCyclic (isCyclic_of_prime_card (card_aut_eq_finrank E E'))
  obtain ⟨ψ, hψ⟩ : ∃ ψ : QZChar Gal(Ω/K), IsProGalois (QZChar.ker ψ) L Ω :=
    exists_isProGalois_ker_of_isCyclic h_cyc
  -- `μ` kills `Eˣ` and the norm of `u`, hence the norm of `w * star w`; by the definition of a step
  -- the norm of `w` to `E` is then a norm from `E'` up to `Eˣ`
  have h_step : ∃ (b : Eˣ) (v : (𝔸f E')ˣ), IsTotallyPositive (b : E) ∧
      w.map (adeleNorm E K) = principalIdele b * v.map (adeleNorm E E') := by
    have h_tower : (adeleNorm E K).comp (adeleNorm K L) = adeleNorm E L :=
      MonoidHom.ext adeleNorm_adeleNorm
    -- the norm of `u` to `E` is that of `w * star w` times principal ideles, which `μ` kills
    have h_ww : μ (w.map (adeleNorm E K) * star (w.map (adeleNorm E K))) = 1 := by
      simpa [← h_tower, hμ.apply_principal, map_adeleNorm_principalIdele,
        units_map_adeleNorm_star, eq_inv_mul_of_mul_eq hw] using hu
    obtain ⟨b, v, hbv⟩ := (hμ.apply_norm_eq_one_iff _).mp h_ww
    exact ⟨b, v, isTotallyPositive_of_isTotallyComplex _, hbv⟩
  -- the Artin symbol `f` of `w` fixes `E'` and `x`, hence all of `L = E'[x]`
  have h_art : New.QZChar.abelianLift ψ (artinMap Gal(Ω/K) w) = 1 := by
    obtain ⟨f, hf⟩ := Quot.exists_rep (artinMap Gal(Ω/K) w)
    -- `f` is also the symbol of the norm of `w` to `E`, so it lies in the kernel of `χ`, the
    -- subgroup that fixes `E'`
    have hf_norm : artinMap Gal(Ω/E) (w.map (adeleNorm E K)) = f.restrictScalars E :=
      artinMap_map_adeleNorm hf.symm 1 (fun _ ↦ rfl) fun _ ↦ rfl
    have hf_ker : New.QZChar.abelianLift χ ↑(f.restrictScalars E) = 1 := by
      rwa [← hf_norm, abelianLift_artinMap_eq_one_iff]
    obtain ⟨χ_ker, -⟩ : QZChar.ker χ = fixingSubgroup Gal(Ω/E) (Set.range (algebraMap E' Ω)) ∧
        (QZChar.ker χ).index = Module.finrank E E' :=
      eq_fixingSubgroup_of_isProGalois (J := hχ)
    obtain ⟨ψ_ker, -⟩ : QZChar.ker ψ = fixingSubgroup Gal(Ω/K) (Set.range (algebraMap L Ω)) ∧
        (QZChar.ker ψ).index = Module.finrank K L :=
      eq_fixingSubgroup_of_isProGalois (J := hψ)
    have hf_E' (t : E') : f (algebraMap E' Ω t) = algebraMap E' Ω t :=
      χ_ker.le hf_ker ⟨algebraMap E' Ω t, Set.mem_range_self t⟩
    let f' : L →ₐ[E'] Ω := ⟨f.toRingHom.comp (algebraMap L Ω), hf_E'⟩
    have hf_L (t : L) : f (algebraMap L Ω t) = algebraMap L Ω t :=
      AlgHom.adjoin_le_equalizer f' (algHom E' L Ω) (forall_eq.mpr (f.commutes x)) (hL.ge trivial)
    rw [← hf]
    exact ψ_ker.ge fun ⟨_, t, rfl⟩ ↦ hf_L t
  -- so `w = b * N s` with `b` in `Kˣ` and `s` an idele of `L`, and `N (s * star s / u)` is in `Kˣ`
  obtain ⟨b, s, -, rfl⟩ := (abelianLift_artinMap_eq_one_iff ψ w).mp h_art
  obtain ⟨k, hk⟩ : ∃ k : Kˣ, principalIdele k = (s * star s / u).map (adeleNorm K L) := by
    refine ⟨y / (a * b * star b), ?_⟩
    -- after substituting `hw`, the two sides in `𝔸f K` differ by the order of the factors
    have h_vals : algebraMap K (𝔸f K) a * (algebraMap K (𝔸f K) b * adeleNorm K L s *
        (algebraMap K (𝔸f K) (star (b : K)) * star (adeleNorm K L s))) =
        adeleNorm K L s * star (adeleNorm K L s) *
          (algebraMap K (𝔸f K) a * algebraMap K (𝔸f K) b * algebraMap K (𝔸f K) (star (b : K))) := by
      ring
    simpa [div_eq_div_iff_mul_eq_mul, hw, Units.ext_iff] using h_vals
  obtain ⟨z, c, hc, h_cob⟩ : ∃ (z : Lˣ) (c : 𝔸f L), IsUnit c ∧
      ↑(principalIdele z / (s * star s / u)) * adeleMap (g : L →+* L) c = c :=
    exists_principalIdele_div_mul_adeleMap_eq (isTotallyPositive_of_isTotallyComplex _) hk
  -- `z * u * g c = s * star s * c`, so the product is `star c * (s * star s * c)`
  have h_split : principalIdele z * u = s * star s * (principalIdele z / (s * star s / u)) := by
    rw [div_div_eq_mul_div, mul_div_cancel]
  refine ⟨z, c, hc, ?_⟩
  rw [h_split, Units.val_mul, mul_assoc, h_cob]
  -- `star c * (s * star s * c)` is its own adjoint, as `𝔸f L` is commutative
  simp only [IsSelfAdjoint, star_mul, star_star, Units.val_mul, Units.coe_star]
  ring

end IdeleHassePrinciple

/-! ## Unitary roots, twisted norms and products of matching pairs -/

namespace New

open Matrix Polynomial U

variable {R : Type*} {S : Type*}
  {n : Type*} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]
  {γ γ' a c : U (1 : Matrix n n R)} {σ : R →+* R} {z w : R[X]} {p : ℕ} {u v : R} {D : Subgroup Rˣ}
  {x y : Matrix n n R} [CommRing S] [StarRing S]
  {hσ : ∀ (x : R), σ (star x) = star (σ x)}

/-- A unitary matrix commutes with its adjoint, which is its inverse. -/
instance : IsStarNormal γ.val.val where
  star_comm_self := by simp [commute_iff_eq, star, ← inv_val_eq_conjTranspose]

/-! ### Roots -/

/-- Suppose `γ * c = c * γ'` in the unitary group and `a` satisfies `a * z(γ')ᴴ = z(γ')`
(`New.IsRootQuotient`). Then the conjugate `c * a * c⁻¹` satisfies the same relation for `γ`
and `z`. -/
lemma U.isRootQuotient_conj (hc : γ * c = c * γ') (ha : IsRootQuotient γ' z a) :
    IsRootQuotient γ z ↑(c * a * c⁻¹) := by
  have h_semiconj : SemiconjBy c.val.val γ'.val.val γ.val.val :=
    congrArg (fun g : U (1 : Matrix n n R) ↦ g.val.val) hc.symm
  have h_conj : c.val.val * aeval γ'.val.val z * c.val⁻¹.val = aeval γ.val.val z :=
    c.val.mul_inv_eq_iff_eq_mul.mpr (aeval_semiconj h_semiconj z)
  have ha_conj : c.val.val * (a.val.val * (aeval γ'.val.val z)ᴴ) * c.val⁻¹.val =
      c.val.val * aeval γ'.val.val z * c.val⁻¹.val :=
    congrArg (fun M : Matrix n n R ↦ c.val.val * M * c.val⁻¹.val) ha
  -- As `c` is unitary, `cᴴ = c⁻¹` and the inner factors `c⁻¹ * c` cancel.
  simpa [← h_conj, ← inv_val_eq_conjTranspose, IsRootQuotient, mul_assoc,
    conjTranspose_nonsing_inv] using ha_conj

/-- Let `f` be a ring homomorphism commuting with the involutions. If `a * z(γ)ᴴ = z(γ)`, then
applying `f` to `γ`, to `a` and to the coefficients of `z` preserves this relation. -/
lemma U.isRootQuotient_map {f : R →+* S} (hf : ∀ x : R, f (star x) = star (f x))
    (h_root : IsRootQuotient γ z a) :
    IsRootQuotient (map f hf (one_map_ringHom f) γ) (z.map f)
      (map f hf (one_map_ringHom f) a : U (1 : Matrix n n S)) := by
  have h_map : (a.val.val * (aeval γ.val.val z)ᴴ).map f = (aeval γ.val.val z).map f :=
    congrArg (fun M : Matrix n n R ↦ M.map f) h_root
  show (a.val.val).map f * (aeval ((γ.val.val).map f) (z.map f))ᴴ =
    aeval ((γ.val.val).map f) (z.map f)
  simpa [conjTranspose_map _ hf, map_aeval_matrix] using h_map

/-- If `z(γ)` is invertible, exactly one unitary `a` satisfies `a * z(γ)ᴴ = z(γ)`
(`New.IsRootQuotient`), namely `z(γ) * (z(γ)ᴴ)⁻¹`. -/
lemma U.existsUnique_isRootQuotient (h_unit : IsUnit (aeval γ.val.val z)) :
    ∃! a : U 1, IsRootQuotient γ z a.val.val := by
  have h_invertible : Invertible (aeval γ.val.val z) := h_unit.invertible
  -- The root is `z(γ) / z(γ)ᴴ`, which is unitary as `z(γ)` commutes with its adjoint.
  have h_unitary :
      (aeval γ.val.val z * ⅟(aeval γ.val.val z)ᴴ)ᴴ * 1 *
        (aeval γ.val.val z * ⅟(aeval γ.val.val z)ᴴ) = 1 := by
    simp [commute_conjTranspose_aeval, Commute.left_comm, conjTranspose_nonsing_inv, mul_assoc]
  refine ⟨of isUnit_one _ h_unitary,
    invOf_mul_cancel_right (aeval γ.val.val z) (aeval γ.val.val z)ᴴ, fun b hb ↦ ?_⟩
  exact Subtype.ext (Units.ext (mul_right_eq_iff_eq_mul_invOf.mp hb))

/-- If `x * z(γ)ᴴ = z(γ)` and `y * w(γ)ᴴ = w(γ)`, then `(x * y) * (z * w)(γ)ᴴ = (z * w)(γ)`: the
values of polynomials at `γ` commute with their adjoints. -/
lemma IsRootQuotient.mul (hx : IsRootQuotient γ z x) (hy : IsRootQuotient γ w y) :
    IsRootQuotient γ (z * w) (x * y) := by
  have h_comm :
      (aeval γ.val.val z)ᴴ * aeval γ.val.val w = aeval γ.val.val w * (aeval γ.val.val z)ᴴ :=
    (commute_conjTranspose_aeval γ.val.val).eq
  grind [conjTranspose_mul]

/-! ### Matching pairs and norms -/

/-- Let `u`, `v` be orthogonal self-adjoint idempotents. If `(f, φ)` is a matching pair for `u` and
level `K` and `(f', φ')` one for `v` and level `L`, then the products `(f * f', φ * φ')` form a
matching pair for `u + v` and level `K ⊓ L`. -/
lemma IsMatchingPair.mul {A : Type*} {j : A → U (1 : Matrix n n R)}
    {K L : Subgroup (U (1 : Matrix n n R))} {f f' : A → ℂ} {φ φ' : U (1 : Matrix n n R) → ℂ}
    (h : IsMatchingPair hσ p u D j K f φ) (h' : IsMatchingPair hσ p v D j L f' φ')
    (huv : u * v = 0) (hu_idem : u * u = u) (hv_idem : v * v = v) (hu_star : star u = u)
    (hv_star : star v = v) :
    IsMatchingPair hσ p (u + v) D j (K ⊓ L) (f * f') (φ * φ') := by
  -- For orthogonal idempotents `u`, `v` the product `z * w` of the two roots is a root for `u + v`:
  -- it is `z` on the part cut out by `u`, `w` on the part cut out by `v`, and `1` elsewhere.
  obtain ⟨h_inv, h_match⟩ := h
  obtain ⟨h'_inv, h'_match⟩ := h'
  refine ⟨fun k hk δ ↦ ?_, fun P hP hPσ ↦ ?_⟩
  · -- Invariance under `K ⊓ L` holds factor by factor.
    obtain ⟨hk_K, hk_L⟩ : k ∈ K ∧ k ∈ L := Subgroup.mem_inf.mp hk
    simp only [Pi.mul_apply, h_inv k hk_K δ, h'_inv k hk_L δ]
  -- The supports of the products lie in those of the factors.
  have hP_of_support {f₀ : A → ℂ} {φ₀ : U (1 : Matrix n n R) → ℂ}
      (hf : (f * f').support ⊆ f₀.support) (hφ : (φ * φ').support ⊆ φ₀.support) :
      P ∈ (fun g : U (1 : Matrix n n R) ↦ g.val.val.charpoly) ''
        (j '' f₀.support ∪ twistedNorm (mapEnd hσ) p '' φ₀.support) :=
    Set.image_mono (Set.union_subset_union (Set.image_mono hf) (Set.image_mono hφ)) hP
  obtain ⟨z, ⟨hz_off, hz_root⟩, hz_match⟩ := h_match P (hP_of_support
    (Function.support_mul_subset_left f f') (Function.support_mul_subset_left φ φ')) hPσ
  obtain ⟨w, ⟨hw_off, hw_root⟩, hw_match⟩ := h'_match P (hP_of_support
    (Function.support_mul_subset_right f f') (Function.support_mul_subset_right φ φ')) hPσ
  refine ⟨z * w, ⟨?_, fun γ hγ ↦ ⟨?_, ?_⟩⟩, fun γ r hγ hr ↦ ?_⟩
  · -- `(1 - u) (1 - v) = 1 - (u + v)`.
    have h_off_mul : (1 - u) • z * (1 - v) • w = (1 - u) • (1 : R[X]) * (1 - v) • (1 : R[X]) := by
      rw [hz_off, hw_off]
    grind [smul_mul_smul]
  · -- The determinant of `(z * w)(γ)` is a product of two elements of `D`.
    grind [mul_mem, det_mul]
  · -- `(1 + u (γ - 1)) (1 + v (γ - 1)) = 1 + (u + v) (γ - 1)`.
    obtain ⟨-, hz_norm⟩ := hz_root γ hγ
    obtain ⟨-, hw_norm⟩ := hw_root γ hγ
    have h_norm_mul : twistedNorm (Polynomial.map σ) p (z * w) =
        twistedNorm (Polynomial.map σ) p z * twistedNorm (Polynomial.map σ) p w := by
      simp [twistedNorm_map_eq_prod, Finset.prod_mul_distrib]
    have h_factor : (1 + u • (γ.val.val - 1)) * (1 + v • (γ.val.val - 1)) =
        1 + (u + v) • (γ.val.val - 1) := by
      simp [add_mul, mul_add, smul_smul, huv, mul_comm v u, add_smul, add_assoc]
    rw [h_norm_mul, ← h_factor]
    exact hz_norm.mul hw_norm
  · -- A quotient `r` for `(u + v) z w` is one for `u z` and one for `v w`.
    have hw_off_u : z * u • ((1 - v) • w) = z * u • ((1 - v) • (1 : R[X])) := by
      rw [hw_off]
    have hz_off_v : v • ((1 - u) • z) * w = v • ((1 - u) • (1 : R[X])) * w := by
      rw [hz_off]
    have huzw : u • (z * w) = u • z := by
      simpa [smul_smul, mul_sub, huv] using hw_off_u
    have hvzw : v • (z * w) = v • w := by
      simpa [smul_smul, mul_sub, mul_comm v u, huv] using hz_off_v
    -- multiply the relation for `(u + v) • (z * w)` by `e = u`, and by `e = v`
    have hr_part {e : R} {f₀ : R[X]} (he : e * (u + v) = e) (he_star : star e = e)
        (h_part : e • (z * w) = e • f₀) : IsRootQuotient γ (e • f₀) r.val := by
      rw [← h_part]
      simpa [smul_smul, he, he_star, hu_star, hv_star, IsRootQuotient] using
        congrArg (fun M : Matrix n n R ↦ e • M) hr
    have hu_sum : u * (u + v) = u := by rw [mul_add, hu_idem, huv, add_zero]
    have hv_sum : v * (u + v) = v := by rw [mul_add, mul_comm v u, huv, hv_idem, zero_add]
    have hr_u : IsRootQuotient γ (u • z) r.val := hr_part hu_sum hu_star huzw
    have hr_v : IsRootQuotient γ (v • w) r.val := hr_part hv_sum hv_star hvzw
    simp +contextual [hz_match γ r hγ hr_u, hw_match γ r hγ hr_v]

/-- Let `z(γ)` be invertible, and let `a * z(γ)ᴴ = z(γ)`. Let `γ * N(γ)ᴴ = N(γ)` for
`N = twistedNorm (.map σ) p z = z * σ(z) * ⋯ * σ^(p-1)(z)` (likewise `twistedNorm (mapEnd hσ) p
c = c * σ(c) * ⋯ * σ^(p-1)(c)`), and let `c` conjugate `σ γ` to `γ`. Then the twisted norm of `c` is
`γ` times that of `a⁻¹ * c`. -/
lemma IsRootQuotient.twistedNorm_eq_mul
    (h_norm : IsRootQuotient γ (twistedNorm (Polynomial.map σ) p z) γ)
    (h_conj : γ * c = c * mapEnd hσ γ) (h_root_a : IsRootQuotient γ z a)
    (h_isUnit : IsUnit (aeval γ.val.val z)) :
    twistedNorm (mapEnd hσ) p c = γ * twistedNorm (mapEnd hσ) p (a⁻¹ * c) := by
  -- By induction on `q`, the quotient of the two norms of length `q` is the root for the norm
  -- of `z` of length `q`, whose value at `γ` is a unit. For `q = p` roots are unique.
  have h_quotient_root (q : ℕ) :
      IsUnit (aeval γ.val.val (twistedNorm (.map σ) q z)) ∧
      IsRootQuotient γ (twistedNorm (.map σ) q z)
        ↑(twistedNorm (mapEnd hσ) q c * (twistedNorm (mapEnd hσ) q (a⁻¹ * c))⁻¹) := by
    induction q with
    | zero => simp [twistedNorm, IsRootQuotient]
    | succ q ih =>
      obtain ⟨ih_unit, ih_root⟩ := ih
      -- Apply `σ`, conjugate by `c` back to `γ`, and multiply by the root `a` of `z`.
      have h_unit : IsUnit (c.val.val * σ.mapMatrix (aeval γ.val.val (twistedNorm (.map σ) q z))) :=
        c.val.isUnit.mul (ih_unit.map σ.mapMatrix)
      have h_root :
          IsRootQuotient γ ((twistedNorm (.map σ) q z).map σ * z)
            ((c *
              mapEnd hσ (twistedNorm (mapEnd hσ) q c * (twistedNorm (mapEnd hσ) q (a⁻¹ * c))⁻¹) *
              c⁻¹).val.val * a.val.val) :=
        (isRootQuotient_conj h_conj (isRootQuotient_map hσ ih_root)).mul h_root_a
      have h_succ : twistedNorm (Polynomial.map σ) (q + 1) z =
          (twistedNorm (Polynomial.map σ) q z).map σ * z :=
        (twistedNorm_succ' (mapRingHom σ).toMonoidHom q z).trans (mul_comm _ _)
      rw [h_succ]
      have h_semiconj : SemiconjBy c.val.val (γ.val.val.map σ) γ.val.val :=
        congrArg (fun g : U (1 : Matrix n n R) ↦ g.val.val) h_conj.symm
      simpa [h_isUnit, aeval_semiconj h_semiconj, twistedNorm_succ', mul_assoc,
        map_aeval_matrix] using And.intro h_unit h_root
  obtain ⟨h_unit_p, h_root_p⟩ := h_quotient_root p
  exact eq_mul_of_mul_inv_eq ((existsUnique_isRootQuotient h_unit_p).unique h_root_p h_norm)

end New

/-!
## Rationality of adelic roots up to a coboundary

The global step of the comparison of traces for a cyclic extension `E'/E` of prime degree
(`New.IsStep`, with its character `μ`). A root (`New.IsNormRoot`) for a polynomial `P` is an adelic
polynomial `z` whose `σ`-norm `N` satisfies `γ = N(γ) / N(γ)ᴴ` at unitary `γ` with characteristic
polynomial `P`, with a determinant condition given by `μ`.

The proof of `New.exists_global_root` works in the CM fields `E'[X] / (q)` for the prime factors `q`
of `P`, applies the Hasse principle `New.IsStep.exists_isSelfAdjoint_of_mem_kerCompNorm` at each
prime factor fixed by `σ`, and glues along the orbits of `σ`.
-/

section GlobalRoot

open NumberField Matrix Polynomial UniqueFactorizationMonoid AdjoinRoot MulAction Function
  Norms.L2Operator Algebra AlgEquiv MulDistribMulAction Ideal ComplexConjugate Ring

/-- If `v(γ)` inverts the unitary matrix `γ`, the adjoint of `f(γ)` is obtained by conjugating the
coefficients of `f` and substituting `v` for `X`. -/
lemma New.U.conjTranspose_aeval {R n : Type} [CommRing R] [StarRing R] [Fintype n] [DecidableEq n]
    {γ : U (1 : Matrix n n R)} {v : R[X]}
    (hv : aeval (γ : Matrix n n R) v * (γ : Matrix n n R) = 1) (f : R[X]) :
    (aeval (γ : Matrix n n R) f)ᴴ = aeval (γ : Matrix n n R) ((f.map conj).comp v) := by
  have h_inv : (γ : Matrix n n R)ᴴ = aeval (γ : Matrix n n R) v := by
    simpa using left_inv_eq_left_inv γ.property hv
  calc (aeval (γ : Matrix n n R) f)ᴴ = aeval (γ : Matrix n n R)ᴴ (f.map conj) :=
        star_aeval (R := R) (γ : Matrix n n R) f
    _ = aeval (γ : Matrix n n R) ((f.map conj).comp v) := by rw [h_inv, aeval_comp]

/-- The complex eigenvalues of a unitary matrix over a CM field have absolute value `1`. -/
lemma New.U.mul_star_eq_one_of_isRoot_charpoly {K n : Type} [Field K] [NumberField K]
    [IsCMField K] [Fintype n] [DecidableEq n] (γ : U (1 : Matrix n n K)) (φ : K →+* ℂ) {x : ℂ}
    (hx : ((γ : Matrix n n K).charpoly.map φ).IsRoot x) : x * star x = 1 := by
  have h_eigen : x ∈ spectrum ℂ ((γ : Matrix n n K).map φ) := by
    rw [← charpoly_map] at hx
    exact mem_spectrum_of_isRoot_charpoly hx
  have h_unitary : (γ : Matrix n n K).map φ ∈ unitaryGroup n ℂ :=
    U_one_mem_unitaryGroup (U.map φ (by simp) (one_map_ringHom φ) γ)
  exact Unitary.mul_star_self_of_mem (spectrum_subset_unitary_of_mem_unitary h_unitary h_eigen)

open scoped Classical in
/-- The Chinese remainder theorem for the prime factors of `P`, after a change of coefficients. -/
lemma New.exists_forall_map_dvd_sub {K S : Type} [Field K] [CommRing S] (f : K →+* S) (P : K[X])
    (x : primeFactors P → S[X]) : ∃ r : S[X], ∀ q : primeFactors P, q.val.map f ∣ r - x q := by
  have h_coprime : Pairwise fun q q' : primeFactors P ↦
      IsCoprime (span {q.val.map f}) (span {q'.val.map f}) := by
    intro q q' h_ne
    have h_rel : IsRelPrime q.val q'.val :=
      pairwise_primeFactors_isRelPrime q.property q'.property (Subtype.coe_injective.ne h_ne)
    rw [isCoprime_span_singleton_iff]
    exact h_rel.isCoprime.map (mapRingHom f)
  obtain ⟨r, hr⟩ : ∃ r : S[X], ∀ q : primeFactors P, r - x q ∈ span {q.val.map f} :=
    exists_forall_sub_mem_ideal h_coprime x
  exact ⟨r, fun q ↦ mem_span_singleton.mp (hr q)⟩

open scoped Classical in
/-- Polynomials congruent modulo every prime factor of `P` agree at an element killed by the
radical of `P`. -/
lemma New.aeval_eq_of_forall_map_dvd_sub {K S A : Type} [Field K] [CommRing S] [Ring A]
    [Algebra S A] (f : K →+* S) {P : K[X]} {a : A}
    (ha : aeval a ((UniqueFactorizationMonoid.radical P).map f) = 0) {g g' : S[X]}
    (hg : ∀ q ∈ primeFactors P, q.map f ∣ g - g') : aeval a g = aeval a g' := by
  have h_coprime : (primeFactors P : Set K[X]).Pairwise fun q q' ↦ IsCoprime (q.map f) (q'.map f) :=
    pairwise_primeFactors_isRelPrime.imp fun q q' h_rel ↦ h_rel.isCoprime.map (mapRingHom f)
  have h_dvd : ∏ q ∈ primeFactors P, q.map f ∣ g - g' := Finset.prod_dvd_of_coprime h_coprime hg
  -- the radical of `P` is the product of its prime factors
  have h_rad_dvd : (radical P).map f ∣ g - g' := by
    rw [UniqueFactorizationMonoid.radical, Polynomial.map_prod]
    exact h_dvd
  have h_zero : aeval a (g - g') = 0 := aeval_eq_zero_of_dvd_aeval_eq_zero h_rad_dvd ha
  rwa [map_sub, sub_eq_zero] at h_zero

/-- Each orbit of a permutation `τ` of a finite type has a representative `r a`, and the position
`j a` of `a` on its orbit, counted from `r a`, grows by one modulo the period under `τ`. -/
lemma New.exists_orbit_representatives {α : Type} [Finite α] (τ : α ≃ α) :
    ∃ (r : α → α) (j : α → ℕ),
      (∀ a : α, r (τ a) = r a) ∧
      (∀ a : α, j a < minimalPeriod τ (r a)) ∧
      (∀ a : α, a = τ^[j a] (r a)) ∧
      ∀ a : α, j (τ a) = (j a + 1) % minimalPeriod τ (r a) := by
  let r (a : α) : α :=
    haveI : Nonempty α := ⟨a⟩
    invFun (periodicOrbit τ) (periodicOrbit τ a)
  have h_mem (a : α) : r (τ a) = r a ∧ a ∈ periodicOrbit τ (r a) := by
    simp [r, τ.injective.mem_periodicPts, invFun_eq, periodicOrbit_apply_eq]
  have h_orbit (a : α) : r (τ a) = r a ∧ ∃ j < minimalPeriod τ (r a), a = τ^[j] (r a) := by
    simpa [periodicOrbit] using h_mem a
  choose r_τ j j_lt hr using h_orbit
  refine ⟨r, j, r_τ, j_lt, hr, fun a ↦ ?_⟩
  rw [← r_τ a]
  -- both sides are the position of `τ a` on the orbit of `r (τ a)`
  have h_iter : τ^[j (τ a)] (r (τ a)) = τ^[(j a + 1) % minimalPeriod τ (r (τ a))] (r (τ a)) := by
    rw [← hr (τ a), iterate_mod_minimalPeriod_eq, r_τ, iterate_succ_apply', ← hr a]
  exact iterate_injOn_Iio_minimalPeriod (j_lt (τ a)) (Nat.mod_lt _ (j_lt (τ a)).pos) h_iter

/-- Transport along the orbits of `τ`. Let `θ a` read `B` in a star ring `A a`, with
`θ (τ a) (T b) = u (τ a) * g a (θ a b)` for units `u`. If at each `a` some `b` with `θ a b` a unit
and `y` in `Y a` make `star (θ a b) * (ι a y * θ a (T^[period of a] b))` self-adjoint, then some
`y a`, `c a` make `ι a (y a) * θ a (T b)` a unit and `star (θ a b)` times it self-adjoint, at every
`a`, whenever `θ a b = θ a (c a)` for all `a`. -/
lemma New.exists_isSelfAdjoint_along_orbits {α B : Type} [Finite α] {A Y : α → Type}
    [∀ a : α, CommRing (A a)] [∀ a : α, StarRing (A a)] [∀ a : α, Monoid (Y a)] (τ : α ≃ α)
    (θ : ∀ a : α, B → A a) (ι : ∀ a : α, Y a →* (A a)ˣ) (g : ∀ a : α, A a →+* A (τ a))
    {u : ∀ a : α, A a} (hu : ∀ a : α, IsUnit (u a)) {T : B → B}
    (hT : ∀ (a : α) (b : B), θ (τ a) (T b) = u (τ a) * g a (θ a b))
    (h_period : ∀ a : α, ∃ (y : Y a) (b : B), IsUnit (θ a b) ∧
      IsSelfAdjoint (star (θ a b) * ((ι a y).val * θ a (T^[minimalPeriod τ a] b)))) :
    ∃ (y : ∀ a : α, Y a) (c : α → B), ∀ b : B, (∀ a : α, θ a b = θ a (c a)) → ∀ a : α,
      IsUnit ((ι a (y a)).val * θ a (T b)) ∧
        IsSelfAdjoint (star (θ a b) * ((ι a (y a)).val * θ a (T b))) := by
  -- With `a = τ^[j a] (r a)`, take `c a = T^[j a] (b₀ (r a))`, and the given factor at the
  -- representatives of the orbits, `1` elsewhere.
  choose y b₀ b₀_unit b₀_adj using h_period
  obtain ⟨r, j, r_τ, j_lt, hr, j_succ⟩ := exists_orbit_representatives τ
  refine ⟨fun a ↦ if j a = 0 then y a else 1, fun a ↦ T^[j a] (b₀ (r a)), fun b hb a ↦ ?_⟩
  obtain ⟨a, rfl⟩ := τ.surjective a
  have T_unit (i : ℕ) : IsUnit (θ (τ^[i] (r a)) (T^[i] (b₀ (r a)))) := by
    induction i with
    | zero => exact b₀_unit _
    | succ i ih =>
      rw [iterate_succ_apply', iterate_succ_apply', hT]
      exact (hu _).mul (ih.map _)
  have τ_eq : τ a = τ^[j a + 1] (r a) := by rw [iterate_succ_apply', ← hr]
  have T_eq : θ (τ a) (T b) = θ (τ a) (T^[j a + 1] (b₀ (r a))) := by
    rw [hT, hb, ← hT, iterate_succ_apply']
  have T_succ_unit : IsUnit (θ (τ a) (T^[j a + 1] (b₀ (r a)))) := by
    rw [τ_eq]
    exact T_unit _
  beta_reduce at hb ⊢
  rw [T_eq, hb, r_τ]
  refine ⟨(Units.isUnit _).mul T_succ_unit, ?_⟩
  obtain h_eq | h_lt := Nat.eq_or_lt_of_le (j_lt a)
  · -- `τ a` is the representative
    have hj : j (τ a) = 0 := by rw [j_succ, Nat.add_one, h_eq, Nat.mod_self]
    have h_back : τ a = r a := by rw [τ_eq, Nat.add_one, h_eq, iterate_minimalPeriod]
    rw [ite_eq_left hj, hj, Nat.add_one, h_eq, h_back]
    exact b₀_adj (r a)
  · -- elsewhere the element has the form `star t * t`
    have hj : j (τ a) = j a + 1 := by rw [j_succ, Nat.mod_eq_of_lt h_lt]
    rw [hj, ite_eq_right (Nat.succ_ne_zero _), map_one, Units.val_one, one_mul]
    exact .star_mul_self _

/-- An automorphism of `E'[X] / (q)` that extends `σ` and fixes the root has the prime order
of `σ`. -/
lemma New.orderOf_eq_of_semiconj {E E' : Type} [Field E] [Field E'] [Algebra E E'] {p : ℕ}
    (hp : p.Prime) {σ : Gal(E'/E)} (hσ_pow : σ ^ p = 1) (hσ : σ ≠ 1) {q : E'[X]}
    [Fact (Irreducible q)] {g : AdjoinRoot q ≃ₐ[E] AdjoinRoot q} (hg : Semiconj (of q) σ g)
    (hg_root : g (root q) = root q) : orderOf g = p := by
  have hp_fact : Fact p.Prime := ⟨hp⟩
  have g_pow : g ^ p = 1 := by
    apply coe_toAlgHom_injective
    ext
    · simp [← coe_pow σ, ← hg.iterate_right p _, hσ_pow]
    · simp [iterate_fixed hg_root]
  have g_ne : g ≠ 1 := by
    intro h_one
    apply hσ
    ext x
    have h_of : of q (σ x) = of q x := by simpa [h_one] using hg x
    exact coe_injective' h_of
  exact orderOf_eq_prime g_pow g_ne

/-- If `γ * N(γ)ᴴ = N(γ)` and `v(γ)` inverts `γ`, the same relation holds for the polynomial `N`
up to nilpotents modulo the characteristic polynomial of `γ`. -/
lemma New.IsRootQuotient.charpoly_dvd_pow {R n : Type} [CommRing R] [StarRing R] [Fintype n]
    [DecidableEq n] {γ : U (1 : Matrix n n R)} {v N : R[X]}
    (hv : aeval (γ : Matrix n n R) v * (γ : Matrix n n R) = 1)
    (hN : IsRootQuotient γ N (γ : Matrix n n R)) :
    (γ : Matrix n n R).charpoly ∣ (X * (N.map conj).comp v - N) ^ Fintype.card n := by
  let D : R[X] := X * (N.map conj).comp v - N
  have h_vanish : aeval (γ : Matrix n n R) D = 0 := by
    rw [map_sub, map_mul, aeval_X, ← U.conjTranspose_aeval hv, hN, sub_self]
  -- `charpoly γ` divides `(charpoly D(γ)).comp D`, and `charpoly 0 = X ^ Fintype.card n`
  have h_dvd : (γ : Matrix n n R).charpoly ∣ (aeval (γ : Matrix n n R) D).charpoly.comp D :=
    charpoly_dvd_charpoly_aeval_comp D
  rwa [h_vanish, charpoly_zero, X_pow_comp] at h_dvd

/-- Let the maps `θ i` detect equality of values at `γ`, and let `β` represent both the adjoint at
`γ` and `star` under each `θ i`. If `x` has an inverse `x'` and `star c * x` is self-adjoint
under every `θ i`, then `x(γ)` is invertible, and every `a` with `a * x(γ)ᴴ = x(γ)` also has
`a * c(γ)ᴴ = c(γ)`. -/
lemma New.isUnit_and_isRootQuotient_of_isSelfAdjoint {R n ι : Type} [CommRing R] [StarRing R]
    [Fintype n] [DecidableEq n] {A : ι → Type} [∀ i : ι, CommRing (A i)]
    [∀ i : ι, StarRing (A i)] [∀ i : ι, Algebra R (A i)] {γ : U (1 : Matrix n n R)}
    (θ : ∀ i : ι, R[X] →ₐ[R] A i)
    (h_glue : ∀ {f f' : R[X]}, (∀ i : ι, θ i f = θ i f') →
      aeval (γ : Matrix n n R) f = aeval (γ : Matrix n n R) f')
    {β : R[X] → R[X]}
    (hβ_adjoint : ∀ f : R[X], (aeval (γ : Matrix n n R) f)ᴴ = aeval (γ : Matrix n n R) (β f))
    (hβ_star : ∀ (i : ι) (f : R[X]), θ i (β f) = star (θ i f)) {x x' c : R[X]}
    (h_inv : ∀ i : ι, θ i x * θ i x' = 1)
    (h_adj : ∀ i : ι, IsSelfAdjoint (star (θ i c) * θ i x)) :
    IsUnit (aeval (γ : Matrix n n R) x) ∧
      ∀ a : Matrix n n R, IsRootQuotient γ x a → IsRootQuotient γ c a := by
  have h_inv_glued : aeval (γ : Matrix n n R) (x * x') = aeval (γ : Matrix n n R) (1 : R[X]) := by
    refine h_glue fun i ↦ ?_
    rw [map_mul, h_inv, map_one]
  have h_inv_γ : aeval (γ : Matrix n n R) x * aeval (γ : Matrix n n R) x' = 1 := by
    rwa [map_mul, map_one] at h_inv_glued
  refine ⟨.of_mul_eq_one _ h_inv_γ, fun a ha ↦ ?_⟩
  have β_eq : aeval (γ : Matrix n n R) (β c) = aeval (γ : Matrix n n R) (β x * (c * x')) := by
    refine h_glue fun i ↦ ?_
    have h_swap : star (θ i x) * θ i c = star (θ i c) * θ i x := by
      rw [← (h_adj i).star_eq, star_mul, star_star]
    rw [map_mul, map_mul, hβ_star, hβ_star, ← mul_assoc, h_swap, mul_assoc, h_inv, mul_one]
  calc
    a * (aeval (γ : Matrix n n R) c)ᴴ =
        a * (aeval (γ : Matrix n n R) x)ᴴ * aeval (γ : Matrix n n R) (c * x') := by
      rw [hβ_adjoint, hβ_adjoint, β_eq, map_mul, mul_assoc]
    _ = aeval (γ : Matrix n n R) (c * (x * x')) := by rw [ha, ← map_mul, mul_left_comm]
    _ = aeval (γ : Matrix n n R) c := by
      refine h_glue fun i ↦ ?_
      rw [map_mul, map_mul, h_inv, mul_one]

/-- The complex roots of a factor `q` of the characteristic polynomial `P` of a unitary matrix over
a CM field have absolute value `1`. -/
lemma New.U.mul_star_eq_one_of_mem_roots_of_dvd {K n : Type} [Field K] [NumberField K]
    [IsCMField K] [Fintype n] [DecidableEq n] (γ : U (1 : Matrix n n K)) (φ : K →+* ℂ)
    {P q : K[X]} (hP : (γ : Matrix n n K).charpoly = P) (hq : q ∣ P) {x : ℂ}
    (hx : x ∈ (q.map φ).roots) :
    x * star x = 1 := by
  have h_root : ((γ : Matrix n n K).charpoly.map φ).IsRoot x := by
    rw [hP]
    exact (isRoot_of_mem_roots hx).dvd (map_dvd φ hq)
  exact U.mul_star_eq_one_of_isRoot_charpoly γ φ h_root

open scoped Classical in
/-- An automorphism `σ` of `E'` over `E` that fixes the nonzero polynomial `P` maps each prime
factor of `P` to a prime factor of `P`. -/
lemma New.smul_mem_primeFactors_of_smul_eq {E E' : Type} [Field E] [Field E'] [Algebra E E']
    {σ : Gal(E'/E)} {P q : E'[X]} (hP_ne : P ≠ 0) (hP_fix : σ • P = P) (hq : q ∈ primeFactors P) :
    σ • q ∈ primeFactors P := by
  have mem_fac {f : E'[X]} : f ∈ primeFactors P ↔ Irreducible f ∧ f.Monic ∧ f ∣ P :=
    mem_primeFactors.trans (Polynomial.mem_normalizedFactors_iff hP_ne)
  obtain ⟨h_irred, h_monic, h_dvd⟩ := mem_fac.mp hq
  refine mem_fac.mpr ⟨h_irred.map (toMulEquiv _ σ), ?_, ?_⟩
  · simpa [smul_eq_map] using h_monic
  · exact (_root_.map_dvd (toMulEquiv _ σ) h_dvd).trans hP_fix.dvd

/-- Let `z` be a norm root for `P` over `R` with `u = 1` (`New.IsNormRoot`), let `γ` be a unitary
matrix with characteristic polynomial `P`, and let `v' * P + v * X = 1`. Then `P` divides a power
of `X * N̄(v) - N`, where `N` is the twisted norm of `z` under `σ` and `N̄` has conjugated
coefficients. -/
lemma New.IsNormRoot.dvd_pow_of_charpoly_eq {R n : Type} [CommRing R] [StarRing R] [Fintype n]
    [DecidableEq n] {σ : R →+* R} {p : ℕ} {D : Subgroup Rˣ} {P z : R[X]}
    (hz : IsNormRoot n σ p 1 D P z) {γ : U (1 : Matrix n n R)}
    (hγ : (γ : Matrix n n R).charpoly = P)
    {v v' : R[X]} (hv : v' * P + v * X = 1) :
    P ∣ (X * ((twistedNorm (.map σ) p z).map conj).comp v - twistedNorm (.map σ) p z) ^
      Fintype.card n := by
  obtain ⟨-, hz_roots⟩ := hz
  obtain ⟨-, h_quot⟩ := hz_roots γ hγ
  have cayley : aeval (γ : Matrix n n R) P = 0 := by rw [← hγ, aeval_self_charpoly]
  have v_inv : aeval (γ : Matrix n n R) v * (γ : Matrix n n R) = 1 := by
    have h_bezout : aeval (γ : Matrix n n R) (v' * P + v * X) = 1 := by rw [hv, map_one]
    simpa [cayley] using h_bezout
  have h_quot_γ : IsRootQuotient γ (twistedNorm (.map σ) p z) (γ : Matrix n n R) := by
    simpa using h_quot
  rw [← hγ]
  exact IsRootQuotient.charpoly_dvd_pow v_inv h_quot_γ

/-- Let `A` be a finite free algebra over `R` and `D` a subgroup of `Rˣ`. If `det z(M)` lies in `D`
for every square matrix `M` over `R` with `P(M) = 0`, then the norm of `z(a)` from `A` to `R` lies
in `D` for every `a` in `A` with `P(a) = 0`. -/
theorem exists_mem_coe_eq_norm_aeval_of_forall_det_aeval_mem {R A : Type*} [CommRing R]
    [Nontrivial R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A] {P z : R[X]}
    {D : Subgroup Rˣ}
    (hz : ∀ (m : ℕ) (M : Matrix (Fin m) (Fin m) R), aeval M P = 0 →
      (aeval M z).det ∈ D.toSubmonoid.map (Units.coeHom R))
    {a : A} (ha : aeval a P = 0) : ∃ d ∈ D, (d : R) = Algebra.norm R (aeval a z) := by
  -- apply the hypothesis to the matrix of multiplication by `a` in a basis of `A`
  let b : Module.Basis (Fin (Module.finrank R A)) R A := Module.finBasis R A
  have h_P : aeval (leftMulMatrix b a) P = 0 := by rw [aeval_algHom_apply, ha, map_zero]
  obtain ⟨d, hd, hd_det⟩ := hz _ (leftMulMatrix b a) h_P
  refine ⟨d, hd, ?_⟩
  rw [Algebra.norm_eq_matrix_det b, ← aeval_algHom_apply]
  exact hd_det

/-- The `i`-th power of `Polynomial.mapRingHom f` maps the coefficients by `f ^ i`. -/
theorem Polynomial.mapRingHom_pow_apply {R : Type*} [Semiring R] (f : R →+* R) (i : ℕ)
    (p : R[X]) : (mapRingHom f ^ i) p = p.map (f ^ i) := by
  induction i with
  | zero => simp [RingHom.one_def]
  | succ i ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, coe_mapRingHom, Polynomial.map_map,
      pow_succ', RingHom.mul_def]

/-- The finite idele of `y` in `Lˣ` is the image of `y` in the finite adeles. -/
private lemma New.coe_principalIdele {L : Type*} [Field L] [NumberField L] (y : Lˣ) :
    ((principalIdele y : (𝔸f L)ˣ) : 𝔸f L) = algebraMap L (𝔸f L) y :=
  rfl

/-- The Hasse principle at one prime factor `q`, for the step `E'/E` with character `μ` and `σ` of
prime order `p`. Here `θ` presents the adeles of the CM field `L = E'[X] / (q)` as adelic
polynomials modulo `q`, and `T c = z * σ c`. Here `θ (f̄(v)) = star (θ f)`, `θ z` is a unit with
norm in `kerCompNorm E' μ`, and `q` divides `(X * N̄(v) - N) ^ m` for the twisted norm `N` of `z`.
For `l = p`, or `l = 1` when `σ` fixes `q`, some `y` in `Lˣ` and `c` with `θ c` a unit make
`star (θ c) * (y * θ (T^[l] c))` self-adjoint. -/
private lemma New.IsStep.exists_isSelfAdjoint_principalIdele_of_dvd_pow {E E' : Type} [Field E]
    [CMType E] [Field E'] [NumberField E'] [IsCMField E'] [Algebra E E'] {p : ℕ}
    {μ : (𝔸f E)ˣ →* ℂˣ} [hμ : IsStep (E := E) E' μ]
    {σ : Gal(E'/E)} (hp : p.Prime) (hσ_pow : σ ^ p = 1) (hσ : σ ≠ 1) {q v : E'[X]}
    [Fact (Irreducible q)] [IsCMField (AdjoinRoot q)]
    {θ : (𝔸f E')[X] →ₐ[𝔸f E'] 𝔸f (AdjoinRoot q)} (hθ : θ = aeval (root q : 𝔸f (AdjoinRoot q)))
    (hθ_surj : Surjective θ)
    (hθ_dvd : ∀ f : (𝔸f E')[X], q.map (algebraMap E' (𝔸f E')) ∣ f → θ f = 0)
    (hθ_star : ∀ f : (𝔸f E')[X],
      θ ((f.map conj).comp (v.map (algebraMap E' (𝔸f E')))) = star (θ f))
    {z : (𝔸f E')[X]} (hz_unit : IsUnit (θ z))
    (hz_norm : ∃ d ∈ kerCompNorm E' μ, d.val = Algebra.norm (𝔸f E') (θ z))
    {T : (𝔸f E')[X] → (𝔸f E')[X]}
    (hT : T = fun c : (𝔸f E')[X] ↦ z * mapRingHom (adeleMap σ.toRingHom) c) {m : ℕ}
    (h_dvd : q.map (algebraMap E' (𝔸f E')) ∣
      (X * ((twistedNorm (.map (adeleMap σ)) p z).map conj).comp
        (v.map (algebraMap E' (𝔸f E'))) - twistedNorm (.map (adeleMap σ)) p z) ^ m)
    {l : ℕ} (hl : σ • q = q ∧ l = 1 ∨ l = p) :
    ∃ (y : (AdjoinRoot q)ˣ) (c : (𝔸f E')[X]), IsUnit (θ c) ∧
      IsSelfAdjoint (star (θ c) * ((principalIdele y).val * θ (T^[l] c))) := by
  -- the twisted norm `N` of `z` is `T^[p] 1`
  have norm_eq : T^[p] 1 = twistedNorm (.map (adeleMap σ)) p z := by
    rw [hT, iterate_mul_apply, map_one, mul_one, twistedNorm_map_eq_prod]
    exact Finset.prod_congr rfl fun i _ ↦ Polynomial.mapRingHom_pow_apply _ i z
  -- the adeles of `L` have no nilpotents, so `N = root * star N` holds in them
  have h_reduced : IsReduced (𝔸f (AdjoinRoot q)) :=
    isReduced_of_injective (RingHom.pi (evalAt (E := AdjoinRoot q))) DFunLike.coe_injective
  have θ_X : θ X = root q := by rw [hθ, aeval_X]
  set D : (𝔸f E')[X] :=
    X * ((T^[p] 1).map conj).comp (v.map (algebraMap E' (𝔸f E'))) - T^[p] 1 with hD
  have h_pow : θ D ^ m = 0 := by
    rw [← map_pow, hD, norm_eq]
    exact hθ_dvd _ h_dvd
  have h_zero : θ D = 0 := IsNilpotent.eq_zero ⟨m, h_pow⟩
  have h_norm : root q * star (θ (T^[p] 1)) = θ (T^[p] 1) := by
    rwa [hD, map_sub, map_mul, θ_X, hθ_star, sub_eq_zero] at h_zero
  obtain ⟨h_fix, rfl⟩ | rfl := hl
  · -- `σ` fixes `q`: it extends to an automorphism `g` of `L` of order `p` that fixes the root,
    -- and the Hasse principle for `g` applies to the idele `θ z`
    rw [smul_eq_map E' σ] at h_fix
    let g : AdjoinRoot q ≃ₐ[E] AdjoinRoot q := mapAlgEquiv σ q q (.of_eq h_fix)
    have g_conj : Semiconj (of q) σ g := by simp [g, Semiconj]
    have g_root : g (root q) = root q := by simp [g]
    have g_ord : orderOf g = p := orderOf_eq_of_semiconj hp hσ_pow hσ g_conj g_root
    obtain ⟨d, hd, hd_norm⟩ := hz_norm
    -- the norm of `θ z` from `L` to `E` is that of `d` from `E'` to `E`
    have h_norm_eq : Units.map (adeleNorm E (AdjoinRoot q)) hz_unit.unit =
        Units.map (adeleNorm E E') d := by
      ext
      simp [hd_norm]
    have z_mem : hz_unit.unit ∈ kerCompNorm (AdjoinRoot q) μ := (congrArg μ h_norm_eq).trans hd
    have T_conj : Semiconj θ T fun a ↦ θ z * adeleMap g a := by
      intro f
      simp [hθ, hT, g, aeval_def, hom_eval₂, eval₂_map, algebraMap_eq_finAdeleIncl, RingHom.comp]
    have T_iterate : θ (T^[p] 1) = ∏ i ∈ Finset.range (orderOf g),
        adeleMap (↑(g ^ i) : AdjoinRoot q →+* AdjoinRoot q) (θ z) := by
      rw [g_ord, T_conj.iterate_right p 1, map_one, iterate_mul_apply, map_one, mul_one]
      simp only [adeleMap_gal_pow]
    set N : 𝔸f (AdjoinRoot q) := ∏ i ∈ Finset.range (orderOf g),
      adeleMap (↑(g ^ i) : AdjoinRoot q →+* AdjoinRoot q) (hz_unit.unit : 𝔸f (AdjoinRoot q))
      with hN
    have h_prod : N = (root q : 𝔸f (AdjoinRoot q)) * star N := by
      rw [hN, IsUnit.unit_spec, ← T_iterate]
      exact h_norm.symm
    obtain ⟨y, c, hc, h_adj⟩ :=
      hμ.exists_isSelfAdjoint_of_mem_kerCompNorm g_root adjoinRoot_eq_top _ z_mem h_prod
    obtain ⟨c, rfl⟩ := hθ_surj c
    refine ⟨y, c, hc, ?_⟩
    have h_eq : (principalIdele y).val * θ (T^[1] c) =
        (principalIdele y * hz_unit.unit).val * adeleMap g (θ c) := by
      rw [iterate_one, T_conj c, Units.val_mul, IsUnit.unit_spec, mul_assoc]
    rw [h_eq]
    exact h_adj
  · -- `l = p`, and `θ (T^[p] 1)` is the norm `N`: take `c = 1`, and `y` from `N = root * star N`
    -- alone
    obtain ⟨y, hy⟩ := exists_isSelfAdjoint_principalIdele_mul _ h_norm.symm
    refine ⟨y, 1, by simp, ?_⟩
    rw [map_one, star_one, one_mul]
    exact hy

open scoped Classical in
/-- Transport along the orbits of `σ` (as `τ` on the prime factors `q` of `P`). `θ q` evaluates at
the root of `q` in `𝔸f (E'[X] / (q))`, and `T c = z * σ c` with all `θ q z` units. If at each `q`
some unit `y` and `c` with `θ q c` a unit make `star (θ q c) * (y * θ q (T^[period of q] c))`
self-adjoint, then some `y q`, `c₀ q` make `y q * θ q (T c)` a unit and `star (θ q c)` times it
self-adjoint at all `q`, for every `c` with `θ q c = θ q (c₀ q)` for all `q`. -/
private lemma New.exists_isSelfAdjoint_principalIdele_of_forall_minimalPeriod {E E' : Type}
    [Field E] [Field E'] [NumberField E'] [IsCMField E'] [Algebra E E'] {P : E'[X]}
    [∀ q : primeFactors P, Fact (Irreducible q.val)]
    [∀ q : primeFactors P, IsCMField (AdjoinRoot q.val)]
    (θ : ∀ q : primeFactors P, (𝔸f E')[X] →ₐ[𝔸f E'] 𝔸f (AdjoinRoot q.val))
    (hθ : ∀ q : primeFactors P, θ q = aeval (root q.val : 𝔸f (AdjoinRoot q.val)))
    {σ : Gal(E'/E)} (τ : primeFactors P ≃ primeFactors P)
    (hτ : ∀ q : primeFactors P, σ • q.val = (τ q).val)
    {z : (𝔸f E')[X]} (hz_unit : ∀ q : primeFactors P, IsUnit (θ q z)) {T : (𝔸f E')[X] → (𝔸f E')[X]}
    (hT : T = fun c : (𝔸f E')[X] ↦ z * mapRingHom (adeleMap σ.toRingHom) c)
    (h_hasse : ∀ q : primeFactors P, ∃ (y : (AdjoinRoot q.val)ˣ) (c : (𝔸f E')[X]),
      IsUnit (θ q c) ∧
        IsSelfAdjoint (star (θ q c) * ((principalIdele y).val * θ q (T^[minimalPeriod τ q] c)))) :
    ∃ (y : ∀ q : primeFactors P, (AdjoinRoot q.val)ˣ) (c₀ : primeFactors P → (𝔸f E')[X]),
      ∀ c : (𝔸f E')[X], (∀ q : primeFactors P, θ q c = θ q (c₀ q)) → ∀ q : primeFactors P,
        IsUnit ((principalIdele (y q)).val * θ q (T c)) ∧
          IsSelfAdjoint (star (θ q c) * ((principalIdele (y q)).val * θ q (T c))) := by
  -- `σ` induces `g q : L q ≃ L (τ q)`, which carries `T` to a twisted multiplication by `z`
  have τ_map (q : primeFactors P) : Associated (q.val.map σ) (τ q).val := by
    have h_smul : σ • q.val = (τ q).val := hτ q
    rw [smul_eq_map E' σ] at h_smul
    exact .of_eq h_smul
  let g (q : primeFactors P) : AdjoinRoot q.val ≃ₐ[E] AdjoinRoot (τ q).val :=
    mapAlgEquiv σ q (τ q) (τ_map q)
  have θ_T (q : primeFactors P) (f : (𝔸f E')[X]) :
      θ (τ q) (T f) = θ (τ q) z * adeleMap (g q) (θ q f) := by
    simp [hθ, g, hT, aeval_def, hom_eval₂, eval₂_map, algebraMap_eq_finAdeleIncl, RingHom.comp]
  exact exists_isSelfAdjoint_along_orbits τ (fun q f ↦ θ q f) (fun _ ↦ principalIdele)
    (fun q ↦ adeleMap (g q)) hz_unit θ_T h_hasse

open scoped Classical in
/-- From solutions on the orbits to one global solution: transport along the orbits of `σ`, which
permutes the prime factors `q` of `P` as `τ`, then glue by the Chinese remainder theorem. Here
`v * X ≡ 1` mod `P`, and `θ q` presents the adeles of `E'[X] / (q)` as adelic polynomials modulo
`q`. Also `z` is a unit mod each `q` and `T c = z * σ c`. For each `q`, some unit `y` of `E'[X]/(q)`
and some `c` that is a unit mod `q` make `star c · y · T^[k] c` self-adjoint mod `q`, where `k` is
the length of the `τ`-orbit of `q`. Then some `w` over `E'` and adelic `c` make `x = w * T c`
satisfy, at each adelic unitary `γ` killed by the radical of `P`: `x(γ)` is a unit, and
`a * x(γ)ᴴ = x(γ)` implies `a * c(γ)ᴴ = c(γ)`. -/
private lemma New.exists_isUnit_aeval_and_isRootQuotient_of_isSelfAdjoint {E E' n : Type} [Field E]
    [Field E'] [NumberField E'] [IsCMField E'] [Algebra E E'] [Fintype n] [DecidableEq n]
    {P v v' : E'[X]} (hv : v' * P + v * X = 1) [∀ q : primeFactors P, Fact (Irreducible q.val)]
    [∀ q : primeFactors P, IsCMField (AdjoinRoot q.val)]
    (θ : ∀ q : primeFactors P, (𝔸f E')[X] →ₐ[𝔸f E'] 𝔸f (AdjoinRoot q.val))
    (hθ : ∀ q : primeFactors P, θ q = aeval (root q.val : 𝔸f (AdjoinRoot q.val)))
    (hθ_surj : ∀ q : primeFactors P, Surjective (θ q))
    (hθ_ker : ∀ (q : primeFactors P) (f : (𝔸f E')[X]),
      θ q f = 0 ↔ q.val.map (algebraMap E' (𝔸f E')) ∣ f)
    (hθ_rat : ∀ (q : primeFactors P) (f : E'[X]),
      θ q (f.map (algebraMap E' (𝔸f E'))) = AdjoinRoot.mk q.val f)
    (hθ_star : ∀ (q : primeFactors P) (f : (𝔸f E')[X]),
      θ q ((f.map conj).comp (v.map (algebraMap E' (𝔸f E')))) = star (θ q f))
    {σ : Gal(E'/E)} (τ : primeFactors P ≃ primeFactors P)
    (hτ : ∀ q : primeFactors P, σ • q.val = (τ q).val)
    {z : (𝔸f E')[X]} (hz_unit : ∀ q : primeFactors P, IsUnit (θ q z)) (T : (𝔸f E')[X] → (𝔸f E')[X])
    (hT : T = fun c : (𝔸f E')[X] ↦ z * mapRingHom (adeleMap σ.toRingHom) c)
    (h_hasse : ∀ q : primeFactors P, ∃ (y : (AdjoinRoot q.val)ˣ) (c : (𝔸f E')[X]),
      IsUnit (θ q c) ∧
        IsSelfAdjoint (star (θ q c) * ((principalIdele y).val * θ q (T^[minimalPeriod τ q] c)))) :
    ∃ (w : E'[X]) (c : (𝔸f E')[X]), ∀ γ : Gf E' n,
      aeval γ.val.val ((radical P).map (algebraMap E' (𝔸f E'))) = 0 →
      IsUnit (aeval γ.val.val (w.map (algebraMap E' (𝔸f E')) * T c)) ∧
        ∀ a : Matrix n n (𝔸f E'), IsRootQuotient γ (w.map (algebraMap E' (𝔸f E')) * T c) a →
          IsRootQuotient γ c a := by
  -- transport along the orbits of `τ`
  obtain ⟨y, c₀, h_local⟩ :=
    exists_isSelfAdjoint_principalIdele_of_forall_minimalPeriod θ hθ τ hτ hz_unit hT h_hasse
  -- choose `c` and `w` by the Chinese remainder theorem, and an inverse `x'` of `x` modulo each `q`
  obtain ⟨c, hc⟩ : ∃ c : (𝔸f E')[X], ∀ q : primeFactors P,
      q.val.map (algebraMap E' (𝔸f E')) ∣ c - c₀ q :=
    exists_forall_map_dvd_sub (algebraMap E' (𝔸f E')) P c₀
  obtain ⟨w, hw⟩ : ∃ w : E'[X], ∀ q : primeFactors P,
      q.val.map (RingHom.id E') ∣ w - (y q).val.out :=
    exists_forall_map_dvd_sub (RingHom.id E') P fun q ↦ (y q).val.out
  refine ⟨w, c, fun γ hγ ↦ ?_⟩
  set x : (𝔸f E')[X] := w.map (algebraMap E' (𝔸f E')) * T c with hx
  obtain ⟨x', hx'⟩ : ∃ x' : (𝔸f E')[X], ∀ q : primeFactors P,
      q.val.map (algebraMap E' (𝔸f E')) ∣ x' - surjInv (hθ_surj q) (θ q x)⁻¹ʳ :=
    exists_forall_map_dvd_sub (algebraMap E' (𝔸f E')) P fun q ↦ surjInv (hθ_surj q) (θ q x)⁻¹ʳ
  -- read the congruences modulo `q` as equalities in `AdjoinRoot q.val` and its adeles
  have hc_eq (q : primeFactors P) : θ q c = θ q (c₀ q) := by
    simpa only [← hθ_ker, map_sub, sub_eq_zero] using hc q
  have hw_eq (q : primeFactors P) : AdjoinRoot.mk q.val w = (y q).val := by
    have h_mk : AdjoinRoot.mk q.val w = AdjoinRoot.mk q.val (y q).val.out := by
      simpa only [Polynomial.map_id, ← mk_eq_mk] using hw q
    exact h_mk.trans (Quot.out_eq _)
  have hx'_eq (q : primeFactors P) : θ q x' = (θ q x)⁻¹ʳ := by
    simpa only [← hθ_ker, map_sub, sub_eq_zero, surjInv_eq] using hx' q
  have local_prop (q : primeFactors P) :
      IsUnit (θ q x) ∧ IsSelfAdjoint (star (θ q c) * θ q x) := by
    have θ_x : θ q x = (principalIdele (y q)).val * θ q (T c) := by
      rw [hx, map_mul, hθ_rat, hw_eq, coe_principalIdele]
    rw [θ_x]
    exact h_local c hc_eq q
  choose x_unit x_adj using local_prop
  -- an identity under all `θ q` holds modulo the radical of `P`, hence at `γ`
  have glue {f f' : (𝔸f E')[X]} (h_eq : ∀ q : primeFactors P, θ q f = θ q f') :
      aeval γ.val.val f = aeval γ.val.val f' := by
    refine aeval_eq_of_forall_map_dvd_sub _ hγ fun q hq ↦ (hθ_ker ⟨q, hq⟩ _).mp ?_
    rw [map_sub, h_eq, sub_self]
  -- `P` is a multiple of its radical, so `γ` is a root of `P`
  have hγP : aeval γ.val.val (P.map (algebraMap E' (𝔸f E'))) = 0 :=
    aeval_eq_zero_of_dvd_aeval_eq_zero (Polynomial.map_dvd _ (radical_dvd_self (a := P))) hγ
  -- `v` inverts `X` modulo `P`, so `f ↦ f̄(v)` represents the adjoint at `γ`
  have v_inv : aeval γ.val.val (v.map (algebraMap E' (𝔸f E'))) * γ.val.val = 1 := by
    have h_bezout : aeval γ.val.val ((v' * P + v * X).map (algebraMap E' (𝔸f E'))) = 1 := by
      rw [hv, Polynomial.map_one, map_one]
    simpa [hγP] using h_bezout
  have h_inv (q : primeFactors P) : θ q x * θ q x' = 1 := by
    rw [hx'_eq, mul_inverse_cancel _ (x_unit q)]
  exact isUnit_and_isRootQuotient_of_isSelfAdjoint θ glue (U.conjTranspose_aeval v_inv) hθ_star
    h_inv x_adj

open scoped Classical in
/-- Let `E'/E` be a step with character `μ`, `σ ≠ 1` with `σ ^ p = 1`, `p` prime, `P` the `σ`-fixed
characteristic polynomial of a unitary matrix over `E'`, and `z` a norm root for `P` (its twisted
norm `N` has `γ * N(γ)ᴴ = N(γ)` at adelic unitary `γ` with charpoly `P`;
`det z(A) ∈ kerCompNorm E' μ` if `P(A) = 0`). Then some `w` over `E'` and adelic `c` make
`x = w * z * σ c` satisfy, at each `γ` killed by the radical of `P`: `x(γ)` is a unit, and
`a * x(γ)ᴴ = x(γ)` gives `a * c(γ)ᴴ = c(γ)`. -/
lemma New.exists_global_root {E E' n : Type} [Field E] [CMType E] [Field E'] [NumberField E']
    [IsCMField E'] [Algebra E E'] [Fintype n] [DecidableEq n] {p : ℕ} {μ : (𝔸f E)ˣ →* ℂˣ}
    [hμ : IsStep (E := E) E' μ]
    {σ : Gal(E'/E)} (hp : p.Prime) (hσ_pow : σ ^ p = 1) (hσ : σ ≠ 1) {P : E'[X]}
    (hP : ∃ γ' : U (1 : Matrix n n E'), γ'.val.val.charpoly = P) (hP_fix : σ • P = P)
    {z : (𝔸f E')[X]}
    (hz : IsNormRoot n (adeleMap σ) p 1 (kerCompNorm E' μ) (P.map (algebraMap E' (𝔸f E'))) z) :
    ∃ (w : E'[X]) (c : (𝔸f E')[X]),
      let x : (𝔸f E')[X] := w.map (algebraMap E' (𝔸f E')) * (z * c.map (adeleMap σ))
      ∀ γ : Gf E' n,
        aeval γ.val.val ((UniqueFactorizationMonoid.radical P).map (algebraMap E' (𝔸f E'))) = 0 →
        IsUnit (aeval γ.val.val x) ∧
          ∀ a : Matrix n n (𝔸f E'), IsRootQuotient γ x a → IsRootQuotient γ c a := by
  -- Work in the CM fields `L q = E'[X] / (q)` for the prime factors `q` of `P`, permuted by `σ`.
  -- At each `q` the Hasse principle gives a rational `y` and an adelic `c` making
  -- `y * T^[period] c / c` invariant under conjugation; transport these along the orbits of `σ`,
  -- and glue by the Chinese remainder theorem.
  obtain ⟨γ', hγ'⟩ := hP
  have hp_fact : Fact p.Prime := ⟨hp⟩
  let k : E' →+* 𝔸f E' := algebraMap E' (𝔸f E')
  let T (c : (𝔸f E')[X]) : (𝔸f E')[X] := z * mapRingHom (adeleMap σ.toRingHom) c
  -- `γ₀`, the image of `γ'`, is an adelic unitary element with characteristic polynomial `P`
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : Gf E' n, γ₀.val.val.charpoly = P.map k :=
    ⟨U.map k (fun x : E' ↦ (star_algebraMap_finAdele x).symm) (one_map_ringHom k) γ',
      (charpoly_map γ'.val.val k).trans (congrArg (Polynomial.map k) hγ')⟩
  -- `γ'` is invertible, so `v' * P + v * X = 1` for some `v'` and `v`
  obtain ⟨v', v, hv⟩ : IsCoprime P X := by
    rw [← hγ']
    exact isUnit_aeval_iff_isCoprime.mp (by simp)
  have P_ne : P ≠ 0 := by
    rw [← hγ']
    exact (charpoly_monic _).ne_zero
  have fac (q : primeFactors P) : Fact (Irreducible q.val) ∧ q.val.Monic ∧ q.val ∣ P := by
    have h_mem : q.val ∈ normalizedFactors P := mem_primeFactors.mp q.property
    exact ((Polynomial.mem_normalizedFactors_iff P_ne).mp h_mem).imp_left Fact.mk
  choose irred monic dvd_P using fac
  -- `σ` permutes the prime factors of `P`
  let τ : primeFactors P ≃ primeFactors P :=
    (toPerm σ).subtypePermOfFintype fun q hq ↦ smul_mem_primeFactors_of_smul_eq P_ne hP_fix hq
  -- the twisted norm `N` of `z` has `N = X * N̄(v)` at `γ₀`; `P` divides a power of the difference
  have hv_map : v'.map k * P.map k + v.map k * X = 1 := by
    simpa using congrArg (Polynomial.map k) hv
  have norm_dvd : P.map k ∣ (X * ((twistedNorm (.map (adeleMap σ)) p z).map conj).comp (v.map k) -
      twistedNorm (.map (adeleMap σ)) p z) ^ Fintype.card n :=
    IsNormRoot.dvd_pow_of_charpoly_eq hz hγ₀ hv_map
  -- the roots of `P` have absolute value `1`, so each `L q` is a CM field
  have unit_root (q : primeFactors P) (φ : E' →+* ℂ) (x : ℂ) (hx : x ∈ (q.val.map φ).roots) :
      x * star x = ((1 : ℚ) : ℂ) := by
    exact_mod_cast U.mul_star_eq_one_of_mem_roots_of_dvd γ' φ hγ' (dvd_P q) hx
  -- `θ q` is evaluation at the root of `q`, an adele of `L q`; it presents the adeles of `L q` as
  -- the adelic polynomials modulo `q`
  let θ (q : primeFactors P) : (𝔸f E')[X] →ₐ[𝔸f E'] 𝔸f (AdjoinRoot q.val) :=
    aeval (root q.val : 𝔸f (AdjoinRoot q.val))
  have h_presentation (q : primeFactors P) : ∃ _ : IsCMField (AdjoinRoot q.val),
      root q.val * star (root q.val) = ((1 : ℚ) : AdjoinRoot q.val) ∧
      IsFinAdelePresentation q.val (θ q) :=
    adjoinRoot_cm_presentation (monic q) (unit_root q)
  choose isCM root_star θ_presents using h_presentation
  have surj (q : primeFactors P) : Surjective (θ q) := (θ_presents q).surjective
  have ker (q : primeFactors P) (f : (𝔸f E')[X]) : θ q f = 0 ↔ q.val.map k ∣ f :=
    (θ_presents q).eq_zero_iff f
  have θ_rat (q : primeFactors P) (f : E'[X]) : θ q (f.map k) = mk q.val f :=
    (θ_presents q).apply_map f
  have θ_comp_v_eq_star (q : primeFactors P) (f : (𝔸f E')[X]) :
      θ q ((f.map conj).comp (v.map k)) = star (θ q f) := by
    have h_bezout : mk q.val (v' * P + v * X) = 1 := by rw [hv, map_one]
    have h_inv : mk q.val v * root q.val = 1 := by
      simpa [mk_eq_zero.mpr (dvd_P q)] using h_bezout
    have h_star : root q.val * star (root q.val) = 1 := by simpa using root_star q
    exact (θ_presents q).apply_map_conj_comp (left_inv_eq_right_inv h_inv h_star) f
  -- `θ q z` is an idele of `L q` whose norm to the ideles of `E'` lies in `kerCompNorm E' μ`
  have z_norm (q : primeFactors P) :
      ∃ d ∈ kerCompNorm E' μ, d.val = Algebra.norm (𝔸f E') (θ q z) := by
    obtain ⟨-, hz_roots⟩ := hz
    obtain ⟨h_det, -⟩ := hz_roots γ₀ hγ₀
    exact exists_mem_coe_eq_norm_aeval_of_forall_det_aeval_mem h_det
      ((ker q _).mpr (map_dvd k (dvd_P q)))
  have z_unit (q : primeFactors P) : IsUnit (θ q z) := by
    obtain ⟨d, -, hd_norm⟩ := z_norm q
    exact lmul_isUnit_iff.mp ((LinearMap.isUnit_iff_isUnit_det _).mpr ⟨d, hd_norm⟩)
  -- the Hasse principle at `q`, for `T` iterated once round the orbit of `q`
  have hasse (q : primeFactors P) : ∃ (y : (AdjoinRoot q.val)ˣ) (c : (𝔸f E')[X]), IsUnit (θ q c) ∧
      IsSelfAdjoint (star (θ q c) * ((principalIdele y).val * θ q (T^[minimalPeriod τ q] c))) := by
    have τ_pow : (τ ^ p) q = q := by simp [τ, ← toPermHom_apply, ← map_pow, hσ_pow]
    have h_period : σ • q.val = q.val ∧ minimalPeriod τ q = 1 ∨ minimalPeriod τ q = p := by
      obtain h_fix | h_move := eq_or_ne (τ q) q
      · exact .inl ⟨congrArg Subtype.val h_fix, minimalPeriod_eq_one_iff_isFixedPt.mpr h_fix⟩
      · exact .inr (minimalPeriod_eq_prime τ_pow h_move)
    exact IsStep.exists_isSelfAdjoint_principalIdele_of_dvd_pow hp hσ_pow hσ rfl (surj q)
      (fun f hf ↦ (ker q f).mpr hf) (θ_comp_v_eq_star q) (z_unit q) (z_norm q) rfl
      ((map_dvd k (dvd_P q)).trans norm_dvd) h_period
  -- transport along the orbits of `τ`, and glue by the Chinese remainder theorem
  exact exists_isUnit_aeval_and_isRootQuotient_of_isSelfAdjoint (n := n) hv θ (fun _ ↦ rfl) surj
    ker θ_rat θ_comp_v_eq_star τ (fun _ ↦ rfl) z_unit T rfl hasse

end GlobalRoot
