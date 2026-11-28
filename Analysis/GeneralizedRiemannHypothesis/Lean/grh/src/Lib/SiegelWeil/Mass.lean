import Lib.Adelic.Reduction.DefiniteClassSums
import Lib.ClassField.HeckeL.EulerProduct
import Lib.Weil.Construction.FiniteMultiplier

/-!
# Masses of definite hermitian lattices and ideal zeta bounds for adelic Gauss sums

The mass `New.mass E l` is the sum of `1 / #Aut` over the double cosets `Γ \ G_f / K₀` of the
definite space `New.stdSpace E (Fin l)`. Here `G_f` is the unitary group over the finite adeles, `Γ`
(`New.stdRatPoints`) its rational points, `K₀` (`New.stdLevel`) the stabiliser of the standard
lattice, and `New.classSum` the weighted sum over these double cosets. If `E` is stably unramified,
the class sum in rank `j + 1` of the number of vectors of norm `1` is the mass in rank `j`. The file
also bounds adelic Gauss sums, integrated over the characters, by a value of the ideal zeta function
of a ring.

## Main definitions and results

* `New.classSum_card_norm_one_eq_mass`: let `E` be stably unramified (`New.HasPrimitiveRoot5040`:
  `E` contains a primitive root of unity of order `5040`, so it is unramified over its maximal real
  subfield at all finite places). Then the class sum in rank `j + 1` of the number of lattice
  vectors of norm `1` is the mass in rank `j`.
* `New.idealZeta`: the sum ζ_R(s) of [R : I]^(−s) over the ideals I of finite index of a ring R.
* `New.lintegral_le_idealZeta_mul`: let ζ_R(μ) ≤ 2. An integral is at most ζ_R(μ)·V if almost every
  point x of the domain lies in some set S(I), for an ideal I of finite index, with
  [R : I]^μ · f(x) · (measure of S(I)) ≤ V, for the integrand f.
* `New.lintegral_gauss_sum_le_idealZeta`: if ζ_Ô(μ) ≤ 2 and 2(μ + 1) ≤ n, the integral over b of
  |∫_{Ô^n} ψ_f(b(w*w − Γ)/2) dw| is at most ζ_Ô(μ)·vol(Ô^n).

Notions from other files:
* `New.stdSpace`: the definite space `I_n`, the sum of `n` norms with its standard lattice.

## Relation to the literature

Part of a known result, the mass formula for unimodular hermitian lattices: masses in consecutive
ranks are compared through the class sums of norm one vectors. See
`Lib.SiegelWeil.OneVector.SiegelClassSum`.

Part of a known result, Siegel's formula for representing a number by a hermitian form, with
bounds on the local densities: the Gauss sums are bounded at all finite places at once, by sorting
the characters by their conductor ideal. See `Lib.SiegelWeil.OneVector.SiegelClassSum`.
-/

/-!
## Positivity of masses and class sums of norm one vectors

Both class sums are computed by `New.classSum_card_orbit`, the second with Witt's theorem.
-/

section MassBasic

open Matrix New.U Fintype Function

namespace New

variable {E : Type*} [Field E] [CMType E] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- An element `g` of the finite adelic unitary group lies in `stdRatPoints`, the image of the
unitary group over `E`, if and only if all its matrix entries come from `E`. -/
lemma mem_stdRatPoints_iff {g : Gf E κ} :
    g ∈ (stdRatPoints : Subgroup (Gf E κ)) ↔
      ∀ i j : κ, g.val i j ∈ (algebraMap E (𝔸f E)).range := by
  refine ⟨?_, fun h_entries ↦ ?_⟩
  · rintro ⟨γ, rfl⟩ i j
    simp [stdSpace_embFin]
  · -- The matrix `M` of rational preimages of the entries is unitary, as its image `g` is.
    choose M hM using h_entries
    obtain ⟨γ, -, hγ⟩ := mem_range_map (J := 1) (g := g) (by simp)
      (algebraMap E (𝔸f E)).injective isUnit_one (by simp) (M := .of M) (ext hM)
    exact ⟨γ, (Subtype.ext (stdSpace_embFin γ)).trans hγ⟩

variable (E κ)

open Pointwise in
/-- For a finite type `κ`, the class sum of `1` over the rational points of the standard definite
space of basis `κ` and the stabiliser `stdLevel E κ` of its standard lattice is the mass in rank
`card κ`, the class sum of `1` for the basis `Fin (card κ)`. -/
lemma classSum_stdRatPoints_eq_mass :
    classSum stdRatPoints (stdLevel E κ) (1 : Gf E κ → ℝ) = mass E (card κ) := by
  -- Renumbering the basis is an isomorphism that matches both pairs of subgroups. We apply the
  -- orbit count to the action on a single point.
  let ι : Gf E (Fin (card κ)) ≃* Gf E κ :=
    reindex (equivFin κ).symm (submatrix_one_equiv (equivFin κ))
  have ι_apply (g : Gf E (Fin (card κ))) (i j : κ) :
      (ι g).val i j = g.val (equivFin κ i) (equivFin κ j) := rfl
  have h_rat : stdRatPoints = stdRatPoints.comap ι.toMonoidHom := Subgroup.ext fun g ↦ by
    rw [Subgroup.mem_comap, mem_stdRatPoints_iff, mem_stdRatPoints_iff]
    simp [ι_apply, reindex_equiv (equivFin κ)]
  have h_int : stdLevel E (Fin (card κ)) = (stdLevel E κ).comap ι.toMonoidHom := by
    simp [SetLike.ext_iff, mem_stdLevel, ι_apply, reindex_equiv (equivFin κ)]
  have h_stab : MulAction.stabilizer (Gf E κ) () = ι.toMonoidHom.range := by simp [SetLike.ext_iff]
  -- Both orbits of the point are the whole one-point set.
  have h_count : (1 : Gf E κ → ℝ) = fun g : Gf E κ ↦
      ((MulAction.orbit (stdRatPoints : Subgroup (Gf E κ)) () ∩
        g • MulAction.orbit (stdLevel E κ) ()).ncard : ℝ) := by
    simp [funext_iff, MulAction.orbit, Set.range_const]
  rw [mass, h_count]
  exact classSum_card_orbit _ _ () ι.toMonoidHom ι.injective h_stab h_rat h_int

/-- For a CM field `E` and every `l`, the mass `mass E l` of the genus of `O_E^l` is positive. This
mass is the sum of `1/#(Γ ∩ g K₀ g⁻¹)` over the classes `Γ g K₀` in the finite adelic unitary group
of rank `l`, where `Γ` is the image of `U_l(E)` and `K₀` the stabiliser of `Ô^l`. -/
lemma mass_pos (l : ℕ) : 0 < mass E l := classSum_one_pos

variable {E κ}
/-- The vectors of norm `1` in the lattice of `g`: the `y` in `E^κ` with `star y ⬝ᵥ y = 1` that
`g⁻¹` maps into the integral lattice `Ô^κ`, for a finite adelic unitary matrix `g`. -/
def normOneLatticeVectors (g : Gf E κ) : Set (κ → E) :=
  {y : κ → E | star y ⬝ᵥ y = 1 ∧ ∀ i : κ, (g⁻¹.val.val *ᵥ algebraMap E (𝔸f E) ∘ y) i ∈ Ô E}

/-- A vector of norm `1` is a column with Gram matrix `1` for the standard form. -/
private lemma replicateCol_gram_eq_one {R : Type*} [CommRing R] [StarRing R] {x : κ → R}
    (hx : star x ⬝ᵥ x = 1) :
    (replicateCol Unit x)ᴴ * (1 : Matrix κ κ R) * replicateCol Unit x = 1 := by
  simpa [← ext_iff, mul_apply, dotProduct] using hx

/-- Witt's theorem for vectors: the unitary group over `E` moves any vector of norm `1` to any
other. -/
private lemma exists_mulVec_eq_of_star_dotProduct_eq_one {x y : κ → E} (hx : star x ⬝ᵥ x = 1)
    (hy : star y ⬝ᵥ y = 1) : ∃ γ : U (1 : Matrix κ κ E), γ.val.val *ᵥ x = y := by
  obtain ⟨γ, hγ⟩ := witt exists_isUnit_sub_star (by simp) isUnit_one
    ⟨_, replicateCol_gram_eq_one hx⟩ ⟨_, replicateCol_gram_eq_one hy⟩
    ((replicateCol_gram_eq_one hx).trans (replicateCol_gram_eq_one hy).symm)
  exact ⟨γ, congrFun (congrArg transpose hγ) ()⟩

/-- Witt's theorem for integral vectors, with `E` stably unramified: the stabiliser `stdLevel E κ`
of the standard lattice moves any integral vector of norm `1` to any other. -/
private lemma exists_mem_stdLevel_mulVec_eq_of_norm_one [HasPrimitiveRoot5040 E] {x y : κ → 𝔸f E}
    (hx : star x ⬝ᵥ x = 1) (hy : star y ⬝ᵥ y = 1) (hx_int : ∀ i : κ, x i ∈ Ô E)
    (hy_int : ∀ i : κ, y i ∈ Ô E) : ∃ k ∈ stdLevel E κ, k.val.val *ᵥ x = y := by
  obtain ⟨k, hk, hkxy⟩ := witt_Ô_of_orthonormal (replicateCol_gram_eq_one hx)
    (replicateCol_gram_eq_one hy) (fun i _ ↦ hx_int i) fun i _ ↦ hy_int i
  exact ⟨k, hk, congrFun (congrArg transpose hkxy) ()⟩

variable (E)

open MulAction Pointwise in
/-- Let `e` be the last basis vector of `E^(j+1)` and `g` a finite adelic unitary matrix, with `E`
containing a primitive root of unity of order `5040` (`HasPrimitiveRoot5040`). The vectors of norm
`1` in the lattice of `g` (`normOneLatticeVectors`) have as image in the adelic vectors
`Γ e ∩ g K₀ e`, for the rational points `Γ` and the stabiliser `K₀` of the standard lattice. -/
lemma image_normOneLatticeVectors_eq_orbit_inter [HasPrimitiveRoot5040 E] {j : ℕ}
    (g : Gf E (Fin j ⊕ Unit)) :
    (fun y : Fin j ⊕ Unit → E ↦ algebraMap E (𝔸f E) ∘ y) '' normOneLatticeVectors g =
      orbit (stdRatPoints : Subgroup (Gf E (Fin j ⊕ Unit)))
          (Pi.single (.inr ()) 1 : Fin j ⊕ Unit → 𝔸f E) ∩
        g • orbit (stdLevel E (Fin j ⊕ Unit)) (Pi.single (.inr ()) 1 : Fin j ⊕ Unit → 𝔸f E) := by
  let e {R : Type _} [CommRing R] : Fin j ⊕ Unit → R := Pi.single (.inr ()) 1
  have norm_col {R : Type _} [CommRing R] [StarRing R] (u : U (1 : Matrix (Fin j ⊕ Unit) _ R)) :
      star (u.val.val *ᵥ e) ⬝ᵥ u.val.val *ᵥ e = 1 := by simpa [e] using U.form_mulVec_mulVec u e e
  let emb : U (stdSpace E (Fin j ⊕ Unit)).J →* Gf E _ := (stdSpace E (Fin j ⊕ Unit)).embFin
  have embFin_smul (γ : U (stdSpace E (Fin j ⊕ Unit)).J) :
      emb γ • e = algebraMap E (𝔸f E) ∘ (γ.val.val *ᵥ e) :=
    show _ *ᵥ e = _ by simp [funext_iff, e, emb]
  ext y
  rw [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · -- Witt's theorem over `E` moves `e` to `y`, and over `Ô E` it moves `e` to `g⁻¹ • y`.
    rintro ⟨y, ⟨h_norm, h_int⟩, rfl⟩
    obtain ⟨γ, rfl⟩ := exists_mulVec_eq_of_star_dotProduct_eq_one (x := e) (by simp [e]) h_norm
    -- `g⁻¹ y` is the image of `e` under a unitary matrix, so it has norm `1`.
    have h_norm' : star ((g⁻¹ * emb γ) • e) ⬝ᵥ (g⁻¹ * emb γ) • e = (1 : 𝔸f E) := norm_col _
    rw [mul_smul, embFin_smul γ] at h_norm'
    obtain ⟨k, hk, hke⟩ := exists_mem_stdLevel_mulVec_eq_of_norm_one (x := e) (by simp [e]) h_norm'
      (by simp [e, Pi.single_apply, apply_ite]) h_int
    exact ⟨⟨⟨_, γ, rfl⟩, embFin_smul γ⟩, ⟨k, hk⟩, hke⟩
  · -- Conversely `y` is the last column of `γ`, so of norm `1`, and `g⁻¹ • y` is the last
    -- column of `k`, so integral.
    rintro ⟨⟨⟨_, γ, rfl⟩, hγ⟩, ⟨k, hk_mem⟩, hk : k.val.val *ᵥ e = g⁻¹.val.val *ᵥ y⟩
    obtain rfl : algebraMap E (𝔸f E) ∘ (γ.val.val *ᵥ e) = y := (embFin_smul γ).symm.trans hγ
    refine ⟨γ.val.val *ᵥ e, ⟨norm_col γ, fun i ↦ ?_⟩, rfl⟩
    rw [← hk]
    simpa [e] using mem_stdLevel.1 hk_mem i (.inr ())

open MulAction Pointwise in
/-- Let `E` be a CM field containing a primitive root of unity of order `5040`
(`HasPrimitiveRoot5040`). Let `Γ` be the image of the rational unitary group `U_{j+1}(E)` in the
finite adelic unitary group `G_f`, and let `K₀ = stdLevel` be the stabiliser of the standard lattice
`Ô^(j+1)`. Summing over the double cosets `Γ g K₀`, with weights `1 / #(Γ ∩ g K₀ g⁻¹)`, the number
of `y` in `E^(j+1)` with `star y ⬝ᵥ y = 1` and `g⁻¹ y ∈ Ô^(j+1)` (`normOneLatticeVectors`) gives
`mass E j`, the same weighted count of classes in rank `j`. -/
lemma classSum_card_norm_one_eq_mass [HasPrimitiveRoot5040 E] (j : ℕ) :
    classSum stdRatPoints (stdLevel E (Fin j ⊕ Unit))
        (fun g : Gf E (Fin j ⊕ Unit) ↦ ((normOneLatticeVectors g).ncard : ℝ)) =
      mass E j := by
  -- The vectors counted form `Γ e ∩ g K₀ e` for the last basis vector `e`, whose stabiliser is the
  -- group of rank `j`.
  let e : Fin j ⊕ Unit → 𝔸f E := Pi.single (.inr ()) 1
  have h_count (g : Gf E (Fin j ⊕ Unit)) : (normOneLatticeVectors g).ncard =
      (orbit (stdRatPoints : Subgroup (Gf E (Fin j ⊕ Unit))) e ∩
        g • orbit (stdLevel E (Fin j ⊕ Unit)) e).ncard := by
    rw [← image_normOneLatticeVectors_eq_orbit_inter,
      (algebraMap E (𝔸f E)).injective.comp_left.injOn.ncard_image]
  -- The embedding `a ↦ diag(a, 1)` of the group of rank `j`.
  let ι : Gf E (Fin j) →* Gf E (Fin j ⊕ Unit) := blockSumOne.comp (.inl _ (Gf E Unit))
  -- A unitary matrix fixes `e` if and only if it is a block sum with `1`.
  have h_stab : stabilizer (Gf E (Fin j ⊕ Unit)) e = ι.range := by
    ext g
    rw [show g ∈ ι.range ↔ g.val.val.toCols₂ = fromRows 0 1 from
      mem_range_sum_left (fromBlocks_one (l := Fin j) (m := Unit)) isUnit_one]
    change g.val.val *ᵥ e = e ↔ _
    -- Both sides prescribe the entries of the last column of `g`.
    simp [e, funext_iff, ← ext_iff, Unique.forall_iff]
  -- `diag(a, 1)` is rational, or integral, exactly when `a` is.
  have h_rat : stdRatPoints = stdRatPoints.comap ι := Subgroup.ext fun g ↦ by
    rw [Subgroup.mem_comap, mem_stdRatPoints_iff, mem_stdRatPoints_iff]
    simp [ι, sum]
  have h_int : stdLevel E (Fin j) = (stdLevel E (Fin j ⊕ Unit)).comap ι := by
    simp [ι, mem_stdLevel, sum, SetLike.ext_iff]
  simpa only [h_count, mass] using classSum_card_orbit (Gf E (Fin j ⊕ Unit)) (Gf E (Fin j)) e ι
    (by simp [ι, sum, Injective, Gf, Units.ext_iff]) h_stab h_rat h_int

end New

end MassBasic

/-!
## Ideal zeta functions and integrals of adelic Gauss sums

`New.Ô` is the ring of integral finite adeles, `New.stdLattice` the lattice Ô^n, `New.ψf` the
standard additive character, and `New.volÔ` the volume of Ô.
-/

namespace New

open MeasureTheory Measure ENNReal Fintype AddSubgroup Set NumberField AddChar Circle stdLattice

variable {A n : Type} [CommRing A] {R : Subring A} {μ e : ℕ} {E : Type _} [Field E] [NumberField E]

/-- The ideal zeta sum ∑ [R : I]^(−s) over the ideals I of finite index in R, for a natural
number s, with values in [0, ∞]. -/
noncomputable def idealZeta (R : Subring A) (s : ℕ) : ℝ≥0∞ :=
  ∑' I : {I : Ideal R // I.cardQuot ≠ 0}, (I.val.cardQuot : ℝ≥0∞)⁻¹ ^ s

/-- A number whose positive power is at most `1 + 2⁻¹ ^ e` is at most `2`. -/
lemma le_two_of_pow_le_ofReal {x : ℝ≥0∞}
    (h_pow : x ^ (μ + 1) ≤ ENNReal.ofReal (1 + 2⁻¹ ^ e)) : x ≤ 2 := by
  rw [← ENNReal.pow_le_pow_left_iff μ.succ_ne_zero]
  calc x ^ (μ + 1) ≤ ENNReal.ofReal (1 + 1) := by grw [h_pow, pow_le_one₀ (by simp) (by norm_num)]
    _ ≤ 2 ^ (μ + 1) := by simpa [one_add_one_eq_two] using le_self_pow₀ one_le_two μ.succ_ne_zero

/-- Summation over ideals: let `idealZeta R μ ≤ 2`. If almost every `x` in `s` lies in a set
`S I`, `I` an ideal of finite index, with `[R : I] ^ μ * f x * ρ (S I) ≤ V`, then the integral of
`f` over `s` is at most `idealZeta R μ * V`. -/
lemma lintegral_le_idealZeta_mul (hμ : idealZeta R μ ≤ 2) {α : Type*} [MeasurableSpace α]
    {ρ : Measure α} {f : α → ℝ≥0∞} {V : ℝ≥0∞} {s : Set α} (S : Ideal R → Set α)
    (h_cover : ∀ᵐ x : α ∂ρ, x ∈ s → ∃ I : Ideal R,
      I.cardQuot ≠ 0 ∧ x ∈ S I ∧ I.cardQuot ^ μ * (f x * ρ (S I)) ≤ V) :
    ∫⁻ x : α in s, f x ∂ρ ≤ idealZeta R μ * V := by
  -- A series of nonzero terms with finite sum has countably many terms.
  have countable : Countable {I : Ideal R // I.cardQuot ≠ 0} := countable_univ_iff.1
    ((Summable.countable_support_ennreal (hμ.trans_lt ofNat_lt_top).ne).mono fun I _ ↦ by simp)
  -- `T I` is the part of `S I` on which the bound holds; these sets cover almost all of `s`.
  let T (I : {I : Ideal R // I.cardQuot ≠ 0}) : Set α :=
    {x : α | x ∈ S I ∧ I.val.cardQuot ^ μ * (f x * ρ (S I)) ≤ V}
  have cover : ∀ᵐ x : α ∂ρ, x ∈ s → x ∈ ⋃ I, T I := by simpa [T, and_left_comm] using h_cover
  have piece (I : {I : Ideal R // I.cardQuot ≠ 0}) :
      ∫⁻ x : α in T I, f x ∂ρ ≤ (I.val.cardQuot : ℝ≥0∞)⁻¹ ^ μ * V := by
    have sup_bound : ∫⁻ x : α in T I, f x ∂ρ ≤ (⨆ x ∈ T I, f x) * ρ (S I) := by
      grw [setLIntegral_mono measurable_const fun _ ↦ le_biSup f, setLIntegral_const,
        measure_mono fun _ hx ↦ hx.1]
    grw [sup_bound]
    simp_rw [ENNReal.iSup_mul, iSup_le_iff, ← ENNReal.inv_pow]
    exact fun x hx ↦ (ENNReal.mul_le_iff_le_inv (by simp [I.2]) (by simp)).1 hx.2
  refine (lintegral_mono_set' cover).trans ((lintegral_iUnion_le T f).trans ?_)
  grw [piece, ENNReal.tsum_mul_right, idealZeta]

lemma coe_stdLattice :
    (stdLattice E n : Set (n → 𝔸f E)) = univ.pi fun _ : n ↦ (Ô E : Set (𝔸f E)) :=
  Set.ext fun _ ↦ Set.mem_univ_pi.symm

section GaussSums

variable {E : Type _} [Field E] [CMType E]

/-- The group of finite adeles `r` such that the character `v ↦ ψ_f(b r v)` of `Ô` is trivial. -/
noncomputable def characterKernel {E : Type*} [Field E] [NumberField E] (b : 𝔸f E) :
    AddSubgroup (𝔸f E) where
  carrier := {r : 𝔸f E | ∀ v : Ô E, ψf E (b * r * v) = 1}
  zero_mem' := by simp
  add_mem' := by simp +contextual [mul_add, add_mul, map_add_eq_mul]
  neg_mem' := by simp +contextual [map_neg_eq_inv]

/-- The group `characterKernel b` of the `r` for which `v ↦ ψ_f(b r v)` is trivial on `Ô` is open:
it contains the preimage of `Ô` under multiplication by `b`. -/
lemma isOpen_characterKernel (b : 𝔸f E) : IsOpen (characterKernel b : Set (𝔸f E)) :=
  (characterKernel b).isOpen_of_mem_nhds (g := 0) <| Filter.mem_of_superset
    ((isOpen_Ô.preimage (continuous_const_mul b)).mem_nhds (by simp))
    fun _ hr v ↦ ψf_eq_one_of_mem (mul_mem hr v.2)

/-- The largest ideal of `Ô` on which the character `v ↦ ψ_f(b v)` is trivial. -/
noncomputable def conductorIdeal {E : Type*} [Field E] [NumberField E] (b : 𝔸f E) :
    Ideal (Ô E) where
  toAddSubmonoid := ((characterKernel b).addSubgroupOf (Ô E).toAddSubgroup).toAddSubmonoid
  smul_mem' c r hr v := by simpa [mul_assoc, mul_left_comm] using hr (c * v)

/-- The conductor ideal of a finite adele `b`, the largest ideal of `Ô` on which `v ↦ ψ_f(b v)` is
trivial, has finite index. -/
lemma cardQuot_conductorIdeal_ne_zero (b : 𝔸f E) : (conductorIdeal b).cardQuot ≠ 0 :=
  isCompact_Ô.relIndex_ne_zero_add (isOpen_characterKernel b)

/-- Let `E` be a CM field. Take a self-adjoint finite adele `b`, a finite adele `Γ`, and
`I = conductorIdeal b`, the largest ideal of `Ô` on which `v ↦ ψ_f(b v)` is trivial. Then the Gauss
sum `G = ∫_{Ô^n} ψ_f(b (w* w - Γ) / 2) dw` satisfies
`[Ô : I] ^ card n * |G| ^ 2 ≤ (volÔ ^ card n) ^ 2`, where `ψ_f` is the standard additive character
of the finite adeles and `volÔ = 2^{r₂}/√|disc E|`. -/
lemma gauss_sum_sq_le [Fintype n] (b : selfAdjoint (𝔸f E)) (Γ : 𝔸f E) :
    (conductorIdeal b.val).cardQuot ^ card n *
        ‖∫ w : n → 𝔸f E in (stdLattice E n : Set (n → 𝔸f E)),
          (ψf E ((2⁻¹ : E) * (b.val * (star w ⬝ᵥ w - Γ))) : ℂ)‖ₑ ^ 2 ≤
      (volÔ E ^ card n) ^ 2 := by
  classical
  let K : AddSubgroup (𝔸f E) := characterKernel b.1
  have K_open : IsOpen (K : Set (𝔸f E)) := isOpen_characterKernel b.1
  -- Weyl differencing: the squared modulus of `∫ F` is the integral of the autocorrelation `corr`.
  let L : Set (n → 𝔸f E) := ↑(stdLattice E n)
  let F (w : n → 𝔸f E) : ℂ := ψf E ((2⁻¹ : E) * (b.1 * (star w ⬝ᵥ w - Γ)))
  have F_cont : Continuous F := continuous_ψf.subtype_val.comp (by fun_prop)
  let corr (d : n → 𝔸f E) : ℂ := ∫ w in L, starRingEnd ℂ (F w) * F (w + d)
  -- Translating `w` by `star v` in the entry `i` multiplies `corr d` by `ψf E (b * d i * v)`
  -- and keeps `L`; so `corr d = 0` unless all `d i` are in `K`.
  let Kn : Set (n → 𝔸f E) := univ.pi fun _ : n ↦ (K : Set (𝔸f E))
  have corr_eq_zero (d : n → 𝔸f E) (hdK : d ∉ Kn) : corr d = 0 := by
    by_contra h_ne
    refine hdK fun i _ v ↦ ?_
    suffices (ψf E (b * d i * v) : ℂ) * corr d = corr d from
      Circle.ext ((mul_eq_right₀ h_ne).1 this)
    let t : n → 𝔸f E := star (v : 𝔸f E) • Pi.single i 1
    have integrand_eq (w : n → 𝔸f E) :
        (ψf E (b * d i * v) : ℂ) * (starRingEnd ℂ (F w) * F (w + d)) =
          starRingEnd ℂ (F (t + w)) * F (t + w + d) := by
      rw [← ψf_inv_two_mul_add_star]
      simp [t, F, ← coe_inv_eq_conj, ← Circle.coe_mul, ← map_neg_eq_inv, ← map_add_eq_mul]
      ring_nf
    simp only [corr, ← integral_const_mul, integrand_eq]
    exact setIntegral_add_left_eq_self_of_mem (fun w ↦ starRingEnd ℂ (F w) * F (w + d))
      (smul_mem_stdLattice (star_mem_Ô v.2) (single_mem_intVectors i))
  have sq_eq : starRingEnd ℂ (∫ w in L, F w) * ∫ w in L, F w = ∫ d in L, corr d := by
    -- Fubini, and translation by `w ∈ L` in the inner integral
    rw [← integral_conj, ← integral_mul_const, ← integral_integral_swap]
    · exact setIntegral_congr_fun isOpen_stdLattice.measurableSet fun w hw ↦ by
        rw [integral_const_mul, setIntegral_add_left_eq_self_of_mem F hw]
    · rw [prod_restrict]
      exact (isCompact_stdLattice.prod isCompact_stdLattice).integrableOn _
  have vol_K : (conductorIdeal b.1).cardQuot * volume (K ∩ Ô E : Set (𝔸f E)) = volÔ E :=
    (relIndex_add_measure_inf (K := (Ô E).toAddSubgroup) isCompact_Ô K_open _).trans volume_Ô
  -- As `‖F‖ = 1` and `corr` vanishes off `K ^ n`, the square is at most a product of volumes.
  have h_sq : ‖∫ w in L, F w‖ₑ ^ 2 ≤ (volume (K ∩ Ô E : Set (𝔸f E)) * volÔ E) ^ card n := calc
      _ = ‖∫ d in Kn, corr d ∂volume.restrict L‖ₑ := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero corr_eq_zero, ← sq_eq, enorm_mul,
          RCLike.enorm_conj, sq]
      _ ≤ ∫⁻ d in Kn, (∫⁻ w in L, ‖starRingEnd ℂ (F w) * F (w + d)‖ₑ) ∂volume.restrict L :=
        (enorm_integral_le_lintegral_enorm _).trans
          (lintegral_mono fun _ ↦ enorm_integral_le_lintegral_enorm _)
      _ = volume (Kn ∩ L) * volume L := by
        simp [Kn, F, ← ofReal_norm, Circle.norm_coe, MeasurableSet.univ_pi, K_open.measurableSet,
          mul_comm]
      _ = _ := by simp [Kn, L, coe_stdLattice, ← pi_inter_distrib, volume_pi_pi, mul_pow]
  grw [h_sq, ← mul_pow, ← mul_assoc, vol_K, ← sq, pow_right_comm]

/-- Let `E` be a CM field, and let `ζ_Ô(μ) = idealZeta (Ô E) μ = Σ_I [Ô : I]^(−μ)`, summed over the
ideals `I` of finite index in `Ô`. If `ζ_Ô(μ) ≤ 2` and the rank `card n` is at least `2 (μ + 1)`,
then for every finite adele `Γ` the lower integral over the self-adjoint finite adeles `b` (for the
volume under which each coset of `selfAdjointCodifferent E 1` has measure one) of
`|∫_{Ô^n} ψ_f(b (w* w - Γ) / 2) dw|` is at most `ζ_Ô(μ) · volÔ ^ card n`. Here `ψ_f` is the standard
additive character and `volÔ = 2^{r₂}/√|disc E|`. This is the convergence bound for the finite part
of the singular series. -/
lemma lintegral_gauss_sum_le_idealZeta (hμ : idealZeta (Ô E) μ ≤ 2) [Fintype n]
    (hd : 2 * (μ + 1) ≤ card n) (Γ : 𝔸f E) :
    ∫⁻ b : selfAdjoint (𝔸f E), ‖∫ w : n → 𝔸f E in (stdLattice E n : Set (n → 𝔸f E)),
        (ψf E ((2⁻¹ : E) * (b.val * (star w ⬝ᵥ w - Γ))) : ℂ)‖ₑ ≤
      idealZeta (Ô E) μ * volÔ E ^ card n := by
  -- Sort the `b` by their conductor ideal `I`. The `b` with a given `I` of index `y` lie in at most
  -- `y` cosets of `selfAdjointCodifferent E 1`, one for each character of `Ô ⧸ I`.
  let ξ (a : selfAdjoint (𝔸f E)) (v : Ô E) : ℂ := ψf E (a.1 * v)
  -- `S I` has, for each character `χ` of `Ô ⧸ I`, a coset that holds all `b` with `ξ b = χ`.
  let S (I : Ideal (Ô E)) : Set (selfAdjoint (𝔸f E)) := ⋃ χ : AddChar (Ô E ⧸ I.toAddSubgroup) ℂ,
    (fun b ↦ -Function.invFun ξ (fun v ↦ χ v) + b) ⁻¹' selfAdjointCodifferent E 1
  refine (setLIntegral_univ _).ge.trans (lintegral_le_idealZeta_mul hμ S (.of_forall fun b _ ↦ ?_))
  let I : Ideal (Ô E) := conductorIdeal b.1
  have index_ne : I.cardQuot ≠ 0 := cardQuot_conductorIdeal_ne_zero b.1
  have : Fintype (Ô E ⧸ I.toAddSubgroup) := fintypeOfIndexNeZero index_ne
  have mem_S : b ∈ S I := by
    -- `ξ b` is trivial on `I`, so it descends to a character of `Ô ⧸ I`
    let ξb : Ô E →+ Additive ℂ := (coeHom.compAddChar (ψf E)).toAddMonoidHom.comp
      ((AddMonoidHom.mulLeft b.1).comp (Ô E).subtype.toAddMonoidHom)
    have h_trivial (r : Ô E) (hr : r ∈ I.toAddSubgroup) : ξb r = 0 := by
      simp [ξb, show ψf E (b.1 * r) = 1 by simpa using hr 1]

    let χ : AddChar (Ô E ⧸ I.toAddSubgroup) ℂ :=
      toAddMonoidHomEquiv.symm (QuotientAddGroup.lift I.toAddSubgroup ξb h_trivial)
    -- The chosen representative `a` of that character differs from `b` by the codifferent.
    let a : selfAdjoint (𝔸f E) := Function.invFun ξ (ξ b)
    have h_eq (x : Ô E) : ψf E (a.1 * x) = ψf E (b.1 * x) :=
      Circle.ext (congrFun (Function.invFun_eq ⟨b, rfl⟩ : ξ a = ξ b) x)
    have h_codiff : -a + b ∈ selfAdjointCodifferent E 1 := fun x hx ↦ by
      simp [add_mul, map_add_eq_mul, map_neg_eq_inv, h_eq ⟨x, hx⟩]
    exact mem_iUnion.2 ⟨χ, h_codiff⟩
  have measure_S : volume (S I) ≤ I.cardQuot := by
    -- there are as many characters of `Ô ⧸ I` as elements, and each coset has mass one
    grw [measure_iUnion_le]
    simp [show card (Ô E ⧸ I.toAddSubgroup) = I.cardQuot from card_eq_nat_card]
  -- As `2 * (μ + 1) ≤ card n`, the Gauss sum saves `[Ô : I] ^ (μ + 1)`; one factor `[Ô : I]` pays
  -- for the cosets.
  set gauss : ℝ≥0∞ := ‖∫ w in (stdLattice E n : Set (n → 𝔸f E)),
    (ψf E ((2⁻¹ : E) * (b.1 * (star w ⬝ᵥ w - Γ))) : ℂ)‖ₑ
  have gauss_le : I.cardQuot ^ (μ + 1) * gauss ≤ volÔ E ^ card n := by
    rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, mul_pow, ← pow_mul']
    calc
      _ ≤ I.cardQuot ^ card n * gauss ^ 2 := by
        gcongr
        simp [index_ne.pos.nat_succ_le]
      _ ≤ (volÔ E ^ card n) ^ 2 := gauss_sum_sq_le b Γ
  refine ⟨I, index_ne, mem_S, ?_⟩
  grw [measure_S, ← gauss_le, pow_succ, mul_comm gauss, mul_assoc]

end GaussSums

open Ideal Nat Real Complex

/-- For a number field `E` and natural numbers `u, v, n` with `n · [E : ℚ] ≤ 2^v`, the `n`-th power
of the ideal zeta sum `idealZeta (Ô E) (u + v + 4) = Σ_I [Ô : I]^(−(u+v+4))` is at most
`1 + 2^(−u)`. The sum runs over the ideals `I` of finite index in the integral finite adeles `Ô` of
`E`. -/
lemma idealZeta_intAdeles_pow_le (u : ℕ) {v n : ℕ} (h_le : n * Module.finrank ℚ E ≤ 2 ^ v) :
    idealZeta (Ô E) (u + v + 4) ^ n ≤ ENNReal.ofReal (1 + 2⁻¹ ^ u) := by
  -- Contraction to `𝓞 E` is injective on ideals of finite index and keeps the index, so `idealZeta`
  -- is at most the Dedekind zeta value, an Euler product whose logarithm is small.
  have index_mem (I : Ideal (Ô E)) : ↑I.cardQuot ∈ I.under (𝓞 E) := by
    simpa [Ideal.mem_comap, Submodule.cardQuot] using nsmul_index_mem I.toAddSubgroup 1
  set σ : ℕ := u + v + 4
  let term (J : Ideal (𝓞 E)) : ℝ := (J.absNorm : ℝ)⁻¹ ^ σ
  let P : ℂ := eulerProd (K := E) (fun _ ↦ 1) σ
  have euler : HasSum term P.re :=
    (hasSum_re (hasSum_eulerProd (s := σ) 1 (by simp) (mod_cast by lia))).congr_fun fun J ↦
      (ofReal_re (term J)).symm.trans (by simp [term, cpow_neg])
  let contract (I : {I : Ideal (Ô E) // I.cardQuot ≠ 0}) : Ideal (𝓞 E) := I.val.under (𝓞 E)
  have inj : contract.Injective :=
    (LeftInvOn.injOn fun I hI ↦ map_under_Ô (by simpa) (index_mem I)).injective
  have same_index (I) : absNorm (contract I) = I.val.cardQuot :=
    card_eq_of_bijective _ (bijective_quot_Ô (by aesop) rfl (index_mem I))
  have zeta_le_euler : idealZeta (Ô E) σ ≤ ENNReal.ofReal P.re := calc
      _ = ∑' I, ENNReal.ofReal (term (contract I)) := tsum_congr fun I ↦ by
        simp [term, same_index, ofReal_inv_of_pos, I.2.pos, ENNReal.inv_pow]
      _ ≤ ∑' J, ENNReal.ofReal (term J) :=
        tsum_comp_le_tsum_of_injective inj fun J ↦ ENNReal.ofReal (term J)
      _ = _ := by rw [← ofReal_tsum_of_nonneg (by simp [term]) euler.summable, euler.tsum_eq]
  have log_le : ‖P‖.log ≤ 2 * Module.finrank ℚ E * 2 ^ (2 - σ : ℝ) :=
    le_of_abs_le (eulerProd_ne_zero_and_abs_log_norm_le (by simp) (by grind) le_rfl).2
  -- With `x = 2⁻¹ ^ u`: `n` times the bound is at most `2 x / (x + 2) ≤ log (1 + x)`.
  have exponent_le : n * (2 * Module.finrank ℚ E * 2 ^ (2 - σ : ℝ)) ≤ (1 + 2⁻¹ ^ u : ℝ).log := by
    have cleared : n * 2 ^ 2 * Module.finrank ℚ E * (1 + 2 * 2 ^ u) ≤ 2 ^ σ := by
      grw [mul_right_comm n, h_le, u.one_le_two_pow]
      lia
    -- The bound `n · 2 [E : ℚ] · 2 ^ (2 - σ) ≤ 2 x / (x + 2)` is `cleared` without denominators.
    grw [← le_log_one_add_of_nonneg (by positivity)]
    simpa [Real.rpow_sub, field] using mod_cast cleared
  calc
    idealZeta (Ô E) σ ^ n ≤ ENNReal.ofReal ‖P‖ ^ n := by grw [zeta_le_euler, re_le_norm]
    _ ≤ ENNReal.ofReal (Real.exp (n * (2 * Module.finrank ℚ E * 2 ^ (2 - σ : ℝ)))) := by
      grw [le_exp_log ‖P‖, log_le, ← ENNReal.ofReal_pow (by positivity), ← Real.exp_nat_mul]
    _ ≤ ENNReal.ofReal (1 + 2⁻¹ ^ u) := by grw [exponent_le, Real.exp_log (by positivity)]

end New
