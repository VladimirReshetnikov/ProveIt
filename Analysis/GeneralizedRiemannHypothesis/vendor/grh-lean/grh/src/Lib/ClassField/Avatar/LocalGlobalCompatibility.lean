import Lib.GaloisRep.Main.OddRank

/-!
# Local-global compatibility for the ℓ-adic avatar of an algebraic Hecke character

Local-global compatibility, including the places above `ℓ`, for the ℓ-adic avatar of an algebraic
Hecke character `θ` of a CM field `E` satisfying `New.HasPrimitiveRoot5040`.

* `New.GaloisRep.avatarCompatAt_of_hasPrimitiveRoot5040`: the statement
  `New.GaloisRep.AvatarCompatAt w θ` at every finite place `w`.

A base change reduces to a split place `w`, one with `star w ≠ w`. There
(`New.GaloisRep.avatarCompatAt_of_isSplit`) `θ = θ₁ (θ / θ₁)`, with `θ₁` the character of a rank one
eigenform (`New.GaloisRep.sphericalCompat_of_odd`, `New.GaloisRep.Attached.exists_det_eq_avatar`)
and `θ / θ₁` of type `0` at the embeddings inducing `w`
(`New.GaloisRep.avatarCompatAt_of_type_eq_zero`).

Notions from other files:
* `New.AlgHeckeChar`: pairs of a character of the finite ideles and its infinity type.
* `New.AlgHeckeChar.avatar`: the ℓ-adic character of `Gal(Ω/E)` attached to such a pair.
* `New.GaloisRep.AvatarCompatAt`: at each place of `Ω` over `w` the avatar has finite type
  (`IsFiniteTypeAt`), its jumps are minus the type of `θ`, and inertia and geometric Frobenius
  elements act through `θ` and local class field theory.
* `New.IsEigenform`, `New.HasHeckePolyAt`: `f ≠ 0` has Hecke polynomial `P u` at almost all places
  `u` of prime norm; `f` is spherical at a split place with the given Hecke polynomial.

## Relation to the literature

Known result: the existence of the ℓ-adic avatar of an algebraic Hecke character and its local
behaviour. The avatar is constructed over totally complex fields (in an imported file). For the CM
fields used here, the behaviour at places above ℓ is read from the rank-one case of the Galois
representations of `Lib.GaloisRep.Main.OddRank` rather than from Lubin–Tate theory. Source: J.-P.
Serre, Abelian ℓ-adic representations and elliptic curves, 1968, II–III (locally algebraic =
Hodge–Tate, Tate's theorem); B. Conrad, Lifting global representations with local properties,
App. B (crystalline case).
-/

open NumberField Polynomial New.AlgHeckeChar Filter New.Variety Submodule AlgEquiv

/-- Let `E` be a totally complex number field and `L ⊇ E` a CM field, both inside the fixed
algebraic closure `Ω` of `ℚ`. For an algebraic Hecke character `θ` of `E`, the ℓ-adic avatar (the
character of the Galois group attached to it) of the base change `θ ∘ N_{L/E}` is the restriction
to `Gal(Ω/L)` of the avatar of `θ`. -/
lemma New.GaloisRep.avatar_baseChange {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E L : Type} [Field E]
    [EmbeddedNumberField E] [IsTotallyComplex E] [Field L] [EmbeddedNumberField L] [IsCMField L]
    [Algebra E L] [IsScalarTower E L Ω] (θ : AlgHeckeChar E) (g : Gal(Ω/L)) :
    (θ.baseChange (E := L)).avatar g = θ.avatar (restrictScalarsHom E g) := by
  -- Both sides are continuous, so it suffices to compare them on the Frobenius elements at
  -- places not above `ℓ`, which are dense. On Artin symbols an avatar is `ιℓ ∘ θ` away from `ℓ`.
  have h_res : Continuous (restrictScalarsHom E : Gal(Ω/L) →* Gal(Ω/E)) :=
    (isOpenEmbedding_galois_restrict _ fun _ _ ↦ rfl).continuous
  suffices h_at_frob : ∀ y : FrobeniusDatum L, (ℓ : 𝓞 L) ∉ y.place.asIdeal →
      (θ.baseChange (E := L)).avatar y.frob = θ.avatar (restrictScalarsHom E y.frob) by
    have h_dense : Dense {g : Gal(Ω/L) |
        θ.baseChange.avatar g = θ.avatar (restrictScalarsHom E g)} :=
      -- Almost all places have prime outside `ℓ`.
      dense_of_mostFrobenii (eventually_mostFrobenii (eventually_notMem_star_notMem (E := L) ℓ ∅)
        fun y ⟨_, _, hℓ⟩ ↦ h_at_frob y hℓ)
    exact congrFun (Continuous.ext_on h_dense (by fun_prop) (by fun_prop) fun _ hg ↦ hg) g

  intro y hℓ
  obtain ⟨x, -, hx⟩ := y.isPlaceOver.exists_localArtin_eq y.isFrob_inv 1
  -- `y.frob` is the Artin symbol of `x` and its restriction is that of the norm of `x`.
  have h_norm := (y.isPlaceOver.localArtin_localNorm (restrictScalarsHom E)
    (hj := IsScalarTower.algebraMap_apply E L Ω)).1 hx
  ext
  calc ((θ.baseChange (E := L)).avatar y.frob).val
      = ιℓ (θ.val.1 (Units.map (adeleNorm E L) (locIdele y.place x))) :=
        avatar_localArtin _ y.isPlaceOver (.inl hℓ) hx
    _ = (θ.avatar (restrictScalarsHom E y.frob)).val := by
      rw [θ.avatar_localArtin y.isPlaceOver.isPlaceOver_below (.inl (by simp [hℓ])) h_norm,
        ← adeleNorm_locIdele]

/-- Let `E` be a CM field, with CM type `Φ` (`CMType E`: one embedding from each conjugate pair),
with a primitive root of unity of order `5040`, `w` a split finite place and `κ` a weight. Then
there is an eigenform `f` of weight `κ` on the definite unitary group of rank one
(`stdSpace E (Fin 1)`), with system `P` of Hecke polynomials, that is spherical at `w` with Hecke
polynomial `P w`. -/
lemma New.GaloisRep.exists_eigenform_rank_one {E : Type} [Field E] [CMType E]
    [HasPrimitiveRoot5040 E] {w : FinPlace E} (hw : w.IsSplit) (κ : Weight E) :
    ∃ f ∈ (stdSpace E (Fin 1)).forms κ, ∃ P : FinPlace E → ℂ[X],
      IsEigenform f P ∧ HasHeckePolyAt f w hw (P w) := by
  -- Take principal level at one place `v` of large norm, away from `w` and `star w`.
  obtain ⟨v, hv_star, hv_ne, hv_norm⟩ :
      ∃ v : FinPlace E, v ≠ star w ∧ v ≠ w ∧ 2 ^ Module.finrank ℚ E < v.q := by
    simpa using (((Northcott.finite_le (h := FinPlace.q (E := E)) (2 ^ Module.finrank ℚ E)).insert
      w).insert (star w)).exists_notMem
  let M : Submodule ℂ ((stdSpace E (Fin 1)).forms κ) :=
    levelSpace ((stdSpace E (Fin 1)).formTranslation κ) (levelOf ![v] ⊥)
  -- The level is free because `v.q > 2 ^ [E : ℚ]` (`classAut_eq_bot`), so a form of this level is
  -- an arbitrary family of values on the double cosets: `M` is finite-dimensional and nonzero.
  have h_free (g : Gf E (Fin 1)) : classAut (stdSpace E (Fin 1)).Γf (levelOf ![v] ⊥) g = ⊥ :=
    classAut_eq_bot (w := ![v]) (Function.injective_of_subsingleton _) (by simp [hv_norm]) le_rfl g
  let e : M ≃ₗ[ℂ] (DoubleCosets (stdSpace E (Fin 1)).embFin.range (levelOf ![v] ⊥) →
      WeylIndex (Fin 1) κ.1 → ℂ) := freeLevelEquiv _ _ _ h_free Quot.out_eq
  have : FiniteDimensional ℂ M := e.symm.finiteDimensional
  -- `M` is stable under the Hecke operators off `v`, hence spanned by eigenforms.
  have h_sph : M ≤ levelSpace ((stdSpace E (Fin 1)).formTranslation κ)
      (stdLevel E (Fin 1) ⊓ Gf.trivialOn (Fin 1) ({v} : Finset (FinPlace E))) :=
    levelSpace_anti (.trans (by simp) inf_trivialOn_le_levelOf)
  have h_span : M ≤ span ℂ {f ∈ M | ∃ P : FinPlace E → ℂ[X], IsSphericalOff {v} f.val P} :=
    le_span_isSphericalOff M h_sph fun u _ hu hu' j _ h ↦ heckeSplit_mem_levelSpace _ j
      (levelSpace_le_sphericalAt hu hu' (h_sph h)) levelOf_le_stdLevel h
  obtain ⟨f, ⟨-, P, hf_ne, hf_fix, hf_poly⟩, -⟩ :
      ∃ f ∈ {f ∈ M | ∃ P : FinPlace E → ℂ[X], IsSphericalOff {v} f.val P}, f ≠ 0 := by
    simpa only [ne_eq, span_eq_bot, not_forall, exists_prop] using
      ne_bot_of_le_ne_bot (nontrivial_iff_ne_bot.mp e.nontrivial) h_span
  -- `f` has the Hecke polynomial `P u` at each split `u` with `u, star u ≠ v`; places of prime
  -- norm are split.
  refine ⟨f, f.prop, P, ⟨hf_ne, ?_⟩, hf_poly w hw (by simp [hv_ne.symm]) (by simp [hv_star.symm])⟩
  filter_upwards [eventually_notMem_star_notMem 1 {v}] with u ⟨hu, hu_star, _⟩ hq
  exact ⟨isSplit_of_q_prime hq, hf_poly u _ hu hu_star⟩

/-- Let `E` be a CM field containing a primitive root of unity of order `5040`, `θ` an algebraic
Hecke character of `E` with infinity type `n`, and `w` a finite place of `E` that is split
(`star w ≠ w`). Then the ℓ-adic avatar `r` of `θ`, taken through the chosen isomorphism
`ι : ℂ ≃ ℚ̄_ℓ`, satisfies `New.GaloisRep.AvatarCompatAt` at `w`. That is, at every `A` over `w`: (a)
`r` is of finite type at `A`; (b) its jump at each `τ` coming from a chart at `A` is `−n(τ)`; (c)
for `m = 0` or `1` and every `s` whose inverse is a Frobenius for `q^m`, with `q` the norm of `w`,
there is `x ∈ E_w^×` of order `m` whose local Artin symbol is the class of `s`, and `X − ι(θ(x))`
kills `s`. -/
lemma New.GaloisRep.avatarCompatAt_of_isSplit {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E : Type}
    [Field E] [EmbeddedNumberField E] [IsCMField E] [HasPrimitiveRoot5040 E] {w : FinPlace E}
    (hw : w.IsSplit) (θ : AlgHeckeChar E) :
    AvatarCompatAt w θ := by
  classical
  -- Write `θ = θ₁ (θ / θ₁)`, where `θ₁` belongs to an eigenform of rank one and `θ / θ₁` has type
  -- `0` over `w`. The weight is chosen so that `θ₁` has the type of `θ` at the embeddings that
  -- induce `w`.
  intro A hA
  have : CMType E := {}
  let k (σ : E →+* ℂ) : ℤ :=
    if inducedPrime σ = w then θ.val.2.toAdd σ else -θ.val.2.toAdd (star σ)
  obtain ⟨f, hf, P, h_eig, hP⟩ := exists_eigenform_rank_one hw (0, k ∘ Φ)
  obtain ⟨⟨r, hr⟩, h_local⟩ := sphericalCompat_of_odd odd_one w hf h_eig
  obtain ⟨h_good, h_jump, h_frob⟩ : IsCompatibleAt (κ := (0, k ∘ Φ)) f 1 w r A :=
    h_local hr hP.1 A hA
  obtain ⟨h_fin, h_inertia⟩ :
      IsFiniteTypeAt r A ∧ ∀ s ∈ inertiaGroup Gal(Ω/E) A, PolyKillsAt r A s (X - 1) :=
    isGoodAt_iff.1 h_good
  -- `det r` is the avatar of a character `θ₁` whose type at `Φ v` and its conjugate is `± k (Φ v)`
  -- and whose values at `w` are read off from `f`.
  obtain ⟨θ₁, hθ₁, h_det⟩ : ∃ θ₁ : AlgHeckeChar E, IsRankOneCharacter (k ∘ Φ) f θ₁ ∧
      ∀ g : Gal(Ω/E), (r g).val.det = θ₁.avatar g :=
    hr.exists_det_eq_avatar hf h_eig
  have h_zero (σ : E →+* ℂ) (hσ : inducedPrime σ = w) : (θ / θ₁).val.2.toAdd σ = 0 := by
    -- `σ` is `Φ (.mk σ)` or `star (Φ (.mk σ))`, and these induce different places since `w` is
    -- split.
    have h_conj : inducedPrime (star (Φ (.mk σ))) = star (inducedPrime (Φ (.mk σ))) :=
      (congrArg inducedPrime (IsCMField.isConj_complexConj E _)).trans
        (placeOfEmb_comp_star (ιℓ.toRingHom.comp _))
    suffices h_eq : θ₁.val.2.toAdd σ = θ.val.2.toAdd σ by simp [h_eq]
    rw [hθ₁.type_eq, Function.comp_apply]
    grind [Φ_mk_eq_or_star_eq σ]
  obtain ⟨quot_fin, quot_jump, quot_poly⟩ := avatarCompatAt_of_type_eq_zero (θ / θ₁) h_zero hA
  -- The avatar of `θ` is the twist of `r = det r`, the avatar of `θ₁`, by that of `θ / θ₁`.
  have h_twist (g : Gal(Ω/E)) : ((Matrix.GeneralLinearGroup.scalar (Fin 1)).comp θ.avatar g).val =
      ((θ / θ₁).avatar g).val • (r g).val := by
    simp [← Matrix.ext_iff, show (r g).val 0 0 = θ₁.avatar g by simpa using h_det g]
  obtain ⟨twist_fin, -, twist_jump, twist_poly⟩ := localConditions_twist A h_twist
  refine ⟨twist_fin h_fin quot_fin, ?_, fun s m hm hs ↦ ?_⟩
  · -- The jumps add: `-type θ = -type θ₁ - type (θ / θ₁)`.
    have h_add (τ : E →+* ℂ) : ({-θ.val.2.toAdd τ} : Multiset ℤ) =
        (jumps (0, k ∘ Φ) 1 τ).map fun v : ℤ ↦ v + -(θ / θ₁).val.2.toAdd τ := by
      have h_jumps : jumps (0, k ∘ Φ) 1 τ = {-θ₁.val.2.toAdd τ} := by
        simp [jumps, Multiset.range, hθ₁.type_eq, neg_ite]
      simp [h_jumps, sub_eq_add_neg]
    simpa only [HasJumpsAt, h_add] using twist_jump h_jump quot_jump
  obtain ⟨x, hx_val, hx_art, hx_poly⟩ := quot_poly s m hm hs
  suffices h_kill : PolyKillsAt r A s (X - C (ιℓ (θ₁.val.1 (locIdele w x)))) from
    ⟨x, hx_val, hx_art, twist_poly
      (h_kill.of_dvd (by simp [dvd_iff_isRoot, AlgHeckeChar.character])) hx_poly⟩
  interval_cases m
  · -- `s` is in the inertia group and the unit `x` fixes the spherical form `f`.
    have hx_mem : ofSplitPlace hw (Matrix.GeneralLinearGroup.scalar (Fin 1) x) ∈
        maxCompactAt (Fin 1) w := by simp [mem_intGL, mem_LocInt, hx_val]
    simpa [hθ₁.apply_locIdele hw x (hP.1 ⟨_, hx_mem⟩)] using h_inertia s (inv_mem_iff.1 hs)
  · -- `s` is a geometric Frobenius and `θ₁ x = -t` is the root of the Hecke polynomial `X + t`.
    obtain ⟨t, ht⟩ : ∃ t : ℂ, P w = X + C t :=
      isMonicOfDegree_one_iff.1 (by simpa using hP.isMonicOfDegree h_eig.1)
    simpa [hθ₁.apply_uniformizer hw x hx_val hP, ht] using
      h_frob hw (P w) hP s (by rwa [pow_one] at hs)

/-- Let `E` be a CM field containing a primitive root of unity of order `5040`, and `θ` an algebraic
Hecke character of `E` with infinity type `n`. Then at every finite place `w` the ℓ-adic avatar `r`
of `θ`, taken through the chosen isomorphism `ι : ℂ ≃ ℚ̄_ℓ`, satisfies
`New.GaloisRep.AvatarCompatAt`. That is, at every `A` over `w`: (a) `r` is of finite type at `A`;
(b) its jump at each `τ` coming from a chart at `A` is `−n(τ)`; (c) for `m = 0` or `1` and every `s`
whose inverse is a Frobenius for `q^m`, with `q` the norm of `w`, there is `x ∈ E_w^×` of order `m`
whose local Artin symbol is the class of `s`, and `X − ι(θ(x))` kills `s`. -/
lemma New.GaloisRep.avatarCompatAt_of_hasPrimitiveRoot5040 {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ]
    {E : Type} [Field E] [EmbeddedNumberField E] {w : FinPlace E} [IsCMField E]
    [HasPrimitiveRoot5040 E] (θ : AlgHeckeChar E) :
    AvatarCompatAt w θ := by
  intro A hA
  -- The field `L` of `exists_isStep_hasQuadSubfield` for `n = w.q` is fixed by the decomposition
  -- group of `A` (`h_dec`), so the place `u` of `L` under `A` has the norm of `w`; and `u` lies
  -- over a split place of an imaginary quadratic subfield (`h_spl`), so it is split.
  obtain ⟨χ, D, _, _, -, h_spl, h_dec⟩ := exists_isStep_hasQuadSubfield E w.q w.one_lt_q.ne_bot
  let L : IntermediateField E Ω := QZChar.stepField χ
  let j : Gal(Ω/L) →* Gal(Ω/E) := restrictScalarsHom E
  have h_fix : decompGroup Gal(Ω/E) A ≤ QZChar.ker (QZChar.symmetrise χ) :=
    (h_dec hA w.1.absNorm_mem).1
  obtain ⟨u, hu, rfl⟩ : ∃ u : FinPlace L, IsPlaceOver A u ∧ u.below E = w := hA.exists_above
  have hq : u.q = (u.below E).q := (hA.q_eq_and_comap_ne_self_of_decompGroup_le h_fix u rfl).1
  have hu_split : u.IsSplit := (h_spl u (by simpa [← hq] using u.1.absNorm_mem)).isSplit_of_below
  obtain ⟨h_fin, h_jump, h_poly⟩ := avatarCompatAt_of_isSplit hu_split θ.baseChange hu
  -- The three clauses descend from `L` to `E`, as the avatar over `L` is the restriction of the
  -- avatar over `E`.
  let r : GalRep ℓ E (Fin 1) := (Matrix.GeneralLinearGroup.scalar (Fin 1)).comp θ.avatar
  let r' : GalRep ℓ L (Fin 1) := (Matrix.GeneralLinearGroup.scalar _).comp θ.baseChange.avatar
  have h_res (g : Gal(Ω/L)) : r' g = r (j g) :=
    congrArg (Matrix.GeneralLinearGroup.scalar _) (avatar_baseChange θ g)
  obtain ⟨desc_fin, desc_jump, desc_poly⟩ := local_clauses_of_retract (A := A) (P := 1) (P' := 1)
    (r := r) (r' := r') (c := 1) (i := algebraMap E L) (hi := fun _ ↦ rfl) (hφ := fun _ _ ↦ rfl)
    (isOpenEmbedding_galois_restrict j fun _ _ ↦ rfl) (hS := univ_mem) (h_comm := by simp [h_res])
    (hP := one_mul 1)
  refine ⟨desc_fin h_fin, desc_jump (by simp) h_jump, fun s m hm hs ↦ ?_⟩
  -- `s` fixes `L`, so it is the image of an `s'` in `Gal(Ω/L)`; take the norm of the element `y`
  -- that belongs to `s'`.
  let s' : Gal(Ω/L) := .ofRingEquiv (f := s) fun x ↦ x.2 ⟨s, h_fix (inv_mem_iff.1 hs.1)⟩
  obtain ⟨y, hy_val, hy_art, hy_poly⟩ := h_poly s' m hm (by rwa [hq])
  refine ⟨localNorm E u y, by simp [v_localNorm (f := 1), hq, hy_val],
    (hu.localArtin_localNorm j).1 hy_art, ?_⟩
  rw [← adeleNorm_locIdele]
  exact desc_poly s' (Set.mem_univ s') hy_poly
