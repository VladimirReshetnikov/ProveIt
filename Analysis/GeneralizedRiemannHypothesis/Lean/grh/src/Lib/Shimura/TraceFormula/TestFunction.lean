import Lib.LocalGL.Iwahori.QuadraticRelation
import Lib.Shimura.HeckeTower.Model

/-!
# Test vectors, and the regular Hecke element that does not kill them

A test vector has a cuspidal type at one split place and is spherical at another.

* `New.Variety.exists_local_hecke_element`: a Hecke element that averages against a character at one
  place.
* `New.Variety.exists_test_function`: the test function `b₁ b₀`, with `b₀` averaging against the
  type at `w₀` and `b₁` acting as a central translate of an injective operator `U_t` at `w₁`.

Conventions: `New.Variety.levelGU` is the principal level `K(𝔑)`, `New.Variety.conjAtSplit` embeds
`GL(E_w)` at a split place `w` into the adelic group, `New.Variety.GU` is the group of similitudes
of the standard form, `New.proIwahori` is the pro-p Iwahori subgroup, and `New.Variety.heckeAlgebra`
is the Hecke algebra inside the group ring, acting through `asAlgebraHom`.

Notions from other files:
* `New.Variety.SplitFinPlace`: The finite places w of E with w̄ ≠ w, that is, those split over the
  maximal real subfield.
* `New.Variety.IsRegularHecke`: f is regular if f(x⁻¹y⁻¹x) ≠ 0, with y in GL_n(E) and x adelic,
  forces the characteristic polynomial of y to be separable.
* `New.Variety.dualComponent`: The inverse transpose of the component at a split place; a left
  inverse of `New.Variety.conjAtSplit`.
* `New.iwahoriHeckeHom`: t ↦ U_t, the mean over `New.proIwahori` composed with the action of a
  dominant diagonal t, on the vectors fixed by `New.proIwahori`.
* `New.Variety.GUPlus`: The monoid of similitudes `g` whose inverse has integral entries, that is,
  which enlarge the standard lattice.

## Relation to the literature

Known; see `Lib.Shimura.TraceFormula.MarkedDefiniteSums` for sources.
-/

open NumberField Matrix Polynomial Submodule Set Subgroup Valued

namespace New.Variety

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {𝔑 : 𝓞 E}
  {W : Type} [AddCommGroup W] [Module ℂ W]

/-- `v` is a test vector for `π` at the split places `w₀` and `w₁`: it is nonzero, has the
cuspidal type `(J, χ)` at `w₀` and is spherical at `w₁`. The local groups act through
`conjAtSplit`, and the level at `w` is the preimage of `levelGU (Fin a) 𝔑` under
`conjAtSplit w`. -/
structure IsTestVector (𝔑 : 𝓞 E) (π : Representation ℂ (GL (Fin a) (𝔸f E)) W) (v : W)
    (w₀ w₁ : SplitFinPlace E) {J : Subgroup (GL (Fin a) (LocField w₀.val))} (χ : J →* ℂ) :
    Prop where
  /-- The two places are distinct. -/
  place_ne : w₀.val ≠ w₁.val
  /-- `𝔑` does not lie in the conjugate of `w₀`. -/
  notMem_star_fst : 𝔑 ∉ (star w₀.val).asIdeal
  /-- `𝔑` lies in `w₁`. -/
  mem_snd : 𝔑 ∈ w₁.val.asIdeal
  /-- `𝔑` does not lie in the conjugate of `w₁`. -/
  notMem_star_snd : 𝔑 ∉ (star w₁.val).asIdeal
  /-- The level at `w₀` lies in `J`. -/
  level_le : (levelGU (Fin a) 𝔑).comap (conjAtSplit w₀) ≤ J
  /-- `J` lies in the maximal compact subgroup at `w₀`. -/
  le_localIntGL : J ≤ localIntGL (Fin a) w₀.val
  /-- `χ` is non-trivial on the part of `J` in every unipotent radical. -/
  isCuspidalType : IsCuspidalType J χ
  /-- The level at `w₁` lies in the pro-`p` Iwahori subgroup. -/
  level_le_proIwahori : (levelGU (Fin a) 𝔑).comap (conjAtSplit w₁) ≤ proIwahori
  /-- The vector is nonzero. -/
  ne_zero : v ≠ 0
  /-- `J` acts on `v` by `χ`. -/
  isEigenvector : v ∈ levelSpace (π.comp (conjAtSplit w₀)) J χ
  /-- The maximal compact subgroup at `w₁` fixes `v`. -/
  fixed : v ∈ levelSpace (π.comp (conjAtSplit w₁)) (localIntGL (Fin a) w₁.val)

/-- Averaging at one split place `w` of the CM field `E` whose conjugate does not contain `𝔑`, for a
representation `π` of `GL_a(𝔸f E)` on `W`, with the local group `GL_a(E_w)` acting through
`conjAtSplit w`. Let `J ≤ GL_a(O_w)` contain the local level, let `χ` be a character of `J` trivial
on it, let `t ∈ GL_a(E_w)`, and let `z` be central with `z · conjAtSplit w t` in `GUPlus`. Then some
Hecke element `b` is supported on the elements `conjAtSplit w j * z * conjAtSplit w t` for `j ∈ J`,
sends vectors of level `𝔑` to vectors on which `J` acts by `χ`, and satisfies `(T * π z⁻¹)(b x) = y`
for every endomorphism `T` of `W` and all `x`, `y` with `T(π(conjAtSplit w (j t)) x) = χ j • y` for
all `j ∈ J`. -/
lemma exists_local_hecke_element (π : Representation ℂ (GL (Fin a) (𝔸f E)) W)
    {w : SplitFinPlace E} {J : Subgroup (GL (Fin a) (LocField w.val))} {z : GL (Fin a) (𝔸f E)}
    (hJ : J ≤ localIntGL (Fin a) w.val) (χ : J →* ℂ)
    (hχ : ∀ g : GL (Fin a) (LocField w.val), conjAtSplit w g ∈ levelGU (Fin a) 𝔑 →
      ∃ hg : g ∈ J, χ ⟨g, hg⟩ = 1)
    (hw : 𝔑 ∉ (star w.val).asIdeal) (t : GL (Fin a) (LocField w.val))
    (hz : ∀ g : GL (Fin a) (𝔸f E), Commute g z) (hzt : z * conjAtSplit w t ∈ GUPlus E (Fin a)) :
    ∃ b : heckeAlgebra (Fin a) ℂ 𝔑,
      b.val ∈ spanOn ℂ (range fun j : J ↦ conjAtSplit w j * (z * conjAtSplit w t)) ∧
      b.val ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w) J χ ∧
      ∀ {x : W} (T : Module.End ℂ W) (y : W),
        (∀ j : J, T (π (conjAtSplit w (j.val * t)) x) = χ j • y) →
          (T * π z⁻¹) (π.asAlgebraHom b x) = y := by
  -- Let `U ≤ J` be the open subgroup of the `j` with `j` and `t⁻¹ j t` both of level `𝔑`. The
  -- element `b` is the average of `(χ j)⁻¹ • [r j]` over representatives `j` of `J ⧸ U`.
  let r (j : J) : GL (Fin a) (𝔸f E) := conjAtSplit w j * (z * conjAtSplit w t)
  have hχ_ne (j : J) : χ j ≠ 0 := (χ.toHomUnits j).ne_zero
  have h𝔑_ne : 𝔑 ≠ 0 := (ne_of_mem_of_not_mem (zero_mem _) hw).symm
  let L : OpenSubgroup (GL (Fin a) (LocField w.val)) :=
    ⟨(levelGU (Fin a) 𝔑).comap (conjAtSplit w), isOpen_comap_conjAtSplit h𝔑_ne⟩
  let L' : OpenSubgroup (GL (Fin a) (LocField w.val)) :=
    L ⊓ L.comap (MulAut.conj t⁻¹) (IsTopologicalGroup.continuous_conj _)
  let U : Subgroup J := L'.subgroupOf J
  -- An open subgroup has finite index in the compact group `localIntGL`, hence in `J`.
  have h_fin : Fintype (J ⧸ U) := U.fintypeOfIndexNeZero fun h_index ↦
    (isCompact_localIntGL _).relIndex_ne_zero L'.isOpen' (relIndex_eq_zero_of_le_right hJ h_index)
  let f (j : J) : ℂ := (χ j * Fintype.card (J ⧸ U))⁻¹
  let b : MonoidAlgebra ℂ (GL (Fin a) (𝔸f E)) := ∑ q : J ⧸ U, f q.out • .single (r q.out) 1
  have h_supp : b ∈ spanOn ℂ (range r) :=
    sum_smul_mem _ _ fun q _ ↦ subset_span ⟨r q.out, mem_range_self q.out, rfl⟩
  -- On a vector `x` of level `𝔑` of any representation `ρ`, `b` acts as the operator `heckeFun`
  -- of `f` on `J` applied to `ρ (r 1) x`, which `U` fixes because `z` is central and `t⁻¹ U t`
  -- has level `𝔑`.
  have h_eigen : b ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w) J χ := by
    intro V _ _ ρ x hx
    have h_fix : ρ (r 1) x ∈ levelSpace (ρ.comp ((conjAtSplit w).domRestrict J)) U := by
      refine mem_levelSpace.mpr fun k ↦ ?_
      -- `t⁻¹ k t` has level `𝔑`, so it fixes `x`
      have h_fix_k :
          ρ (conjAtSplit w (MulAut.conj t⁻¹ ((k : J) : GL (Fin a) (LocField w.val)))) x = x := by
        simpa using mem_levelSpace.mp hx ⟨_, k.property.right⟩
      simpa [r, ← Module.End.mul_apply, ← map_mul, mul_assoc, (hz _).left_comm] using
        congrArg (ρ (r 1)) h_fix_k
    have h_right (j : J) (k : U) : f (j * k) = f j := by
      obtain ⟨hk_J, hχ_k⟩ := hχ _ k.property.left
      simp [f, show χ k = 1 from hχ_k]
    have h_left (j : J) (k : (⊤ : Subgroup J)) : χ.domRestrict ⊤ k * f (k * j) = f j := by
      have hk_ne : χ k ≠ 0 := hχ_ne k
      simp [f, field]
    simpa [b, r, heckeFun, finsum_eq_sum_of_fintype] using
      heckeFun_mem_levelSpace (toFinite _) h_right h_left h_fix
  -- `b` is in the Hecke algebra by `mem_heckeAlgebra_of_mem_fixedToEigen`. Each `r j` lies in
  -- `GUPlus` (from `hJ` and `hzt`) and commutes with every `d` that commutes with the image of
  -- `conjAtSplit w` (from `hz`). Invariance under the level at `w` is `h_eigen`, since `χ` is
  -- trivial on that level.
  have h_terms : ∀ g ∈ range r, g ∈ GUPlus E (Fin a) ∧
      ∀ d : GL (Fin a) (𝔸f E), (∀ m : GL (Fin a) (LocField w.val), Commute d (conjAtSplit w m)) →
        Commute d g := by
    rintro _ ⟨j, rfl⟩
    refine ⟨mul_mem ⟨by simp, ?_⟩ hzt, fun d hd ↦ by simp [r, hd _, hz]⟩
    exact (conjAtSplit_mem_intGL_iff.mpr (hJ j.property)).isIntMatrix_inv
  have h_hecke : b ∈ heckeAlgebra (Fin a) ℂ 𝔑 := by
    refine mem_heckeAlgebra_of_mem_fixedToEigen hw h_supp h_terms fun V _ _ ρ x hx l ↦ ?_
    obtain ⟨hl, hχl⟩ := hχ _ l.property
    simpa [hχl] using h_eigen hx ⟨l, hl⟩
  refine ⟨⟨b, h_hecke⟩, h_supp, h_eigen, fun {x} T y hT ↦ ?_⟩
  -- The central `z` cancels, and each term of the average contributes `y / #(J ⧸ U)`.
  have h_card : (Fintype.card (J ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have h_term (j : J) :
      f j • T (π z⁻¹ (π (r j) x)) = (Fintype.card (J ⧸ U) : ℂ)⁻¹ • y := by
    have h_cancel : z⁻¹ * r j = conjAtSplit w (j.val * t) := by simp [r, (hz _).left_comm]
    have h_act : π z⁻¹ (π (r j) x) = π (conjAtSplit w (j.val * t)) x := by
      rw [← h_cancel, map_mul π z⁻¹ (r j), Module.End.mul_apply]
    have h_coeff : f j * χ j = (Fintype.card (J ⧸ U) : ℂ)⁻¹ := by simp [f, hχ_ne]
    rw [h_act, hT j, smul_smul, h_coeff]
  calc (T * π z⁻¹) (π.asAlgebraHom (⟨b, h_hecke⟩ : heckeAlgebra (Fin a) ℂ 𝔑) x)
      = ∑ q : J ⧸ U, f q.out • T (π z⁻¹ (π (r q.out) x)) := by simp [b]
    _ = ∑ _q : J ⧸ U, (Fintype.card (J ⧸ U) : ℂ)⁻¹ • y :=
        Finset.sum_congr rfl fun q _ ↦ h_term q.out
    _ = y := by simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, h_card]

/-- `I t I · I s I ⊆ I (t s) I` for the pro-`p` Iwahori subgroup `I = proIwahori` and dominant
diagonal `t`, `s`. -/
lemma dominant_doubleCoset_mul {w : SplitFinPlace E} {t s : Fin a → (LocField w.val)ˣ}
    (ht : t ∈ dominantTorus) (hs : s ∈ dominantTorus) (k l k' l' : proIwahori) :
    ∃ k'' l'' : proIwahori,
      k.val * diagGL t * l.val * (k'.val * diagGL s * l'.val) =
        k''.val * diagGL (t * s) * l''.val := by
  -- Write `l k' = u · (u⁻¹ l k')`, move `u` left across `t` and the rest right across `s`.
  obtain ⟨u, hu, h_rest⟩ : ∃ u ∈ unitriangular id (LocField w.val) ⊓ proIwahori,
      (diagGL s)⁻¹ * (u⁻¹ * (l * k').val) * diagGL s ∈ proIwahori :=
    exists_unipotent_conj_mem_proIwahori hs (l * k').property
  refine ⟨k * ⟨_, conj_unitriangular_mem_proIwahori ht hu⟩, ⟨_, h_rest⟩ * l', ?_⟩
  simp [mul_assoc]

/-- The adelic elements `g` such that `dualComponent w g`, the inverse transpose of the component
of `g` at `w`, lies in a double coset `I s I`, where `I = proIwahori` and `s` is diagonal and
strictly dominant. -/
def strictlyDominantAt (w : SplitFinPlace E) : Set (GL (Fin a) (𝔸f E)) :=
  {g : GL (Fin a) (𝔸f E) | ∃ s : Fin a → (LocField w.val)ˣ, StrictMono (fun i ↦ v (s i).val) ∧
    ∃ k l : proIwahori, dualComponent w g = k.val * diagGL s * l.val}

/-- The set `New.Variety.strictlyDominantAt w` is closed under products. -/
lemma mul_mem_strictlyDominantAt {w : SplitFinPlace E} {g g' : GL (Fin a) (𝔸f E)}
    (hg : g ∈ strictlyDominantAt w) (hg' : g' ∈ strictlyDominantAt w) :
    g * g' ∈ strictlyDominantAt w := by
  obtain ⟨s, hs, k, l, hg⟩ := hg
  obtain ⟨s', hs', k', l', hg'⟩ := hg'
  refine ⟨s * s', by simpa [Pi.mul_def] using hs.mul hs', ?_⟩
  simpa only [map_mul, hg, hg'] using dominant_doubleCoset_mul hs.monotone hs'.monotone k l k' l'

/-- Let `f` be a Hecke element of level `𝔑` that is a combination of basis elements [g] with
`dualComponent w g` in some `I s I`, for `I = proIwahori` and `s` diagonal strictly dominant.
Suppose `𝔑 ∉ w̄` and the pullback of `levelGU` under `conjAtSplit w` lies in `I`. Then `f` is
regular: for `y ∈ GL_a(E)` and adelic `x`, if f(x⁻¹y⁻¹x) ≠ 0 then the characteristic polynomial of
`y` is separable. -/
lemma isRegularHecke_of_strictlyDominantAt {w : SplitFinPlace E} (hw : 𝔑 ∉ (star w.val).asIdeal)
    (h_lev : (levelGU (Fin a) 𝔑).comap (conjAtSplit w) ≤ proIwahori) {f : heckeAlgebra (Fin a) ℂ 𝔑}
    (hf : f.val ∈ spanOn ℂ (strictlyDominantAt w)) :
    IsRegularHecke f := by
  intro y x hy
  obtain ⟨g, ⟨s, hs, k, l, hg⟩, h_coset⟩ := spanOn.exists_mem_of_cosetFn_ne_zero hf hy
  -- `x⁻¹ y⁻¹ x` differs from `g` by an element of the level, so at `w` it lies in the same double
  -- coset of `proIwahori` as `s`.
  obtain ⟨h_loc, -⟩ := conjAtSplit_dualComponent hw (QuotientGroup.eq.mp h_coset)
  -- As `s` is strictly dominant, such a point is conjugate to a diagonal `s d` with `d` in
  -- `proIwahori`.
  have h_double : k.val * diagGL s * (l.val * dualComponent w (g⁻¹ * (x⁻¹ * toFinGL y⁻¹ * x))) ∈
      iwahoriDoubleCoset s :=
    mul_mem_mul (mul_mem_mul k.prop rfl) (mul_mem l.prop (h_lev h_loc))
  have h_map_one (c : GL (Fin a) (LocField w.val)) :
      GeneralLinearGroup.map (1 : LocField w.val →+* LocField w.val) c = c := rfl
  obtain ⟨c, -, d, hd, h_conj⟩ := exists_inv_mul_mul_map_eq_diagGL_mul hs 1 (by simp) continuous_id
    (fun g ↦ ⟨g, h_map_one g⟩) h_double
  have h_diag :
      (dualComponent w x * c)⁻¹ * dualComponent w (toFinGL y⁻¹) * (dualComponent w x * c) =
        diagGL (s * d) := by
    simpa [← mul_assoc, ← hg, h_map_one] using h_conj
  -- `dualComponent w (toFinGL y⁻¹)` is by definition the transpose of `y` over `LocField w`.
  have h_charpoly : y.val.charpoly.map (algebraMap E (LocField w.val)) =
      ∏ i : Fin a, (X - C ((s * d) i).val) := by
    rw [← charpoly_map, ← charpoly_transpose,
      show (y.val.map (algebraMap E (LocField w.val)))ᵀ = (dualComponent w (toFinGL y⁻¹)).val
        from rfl,
      ← charpoly_units_conj' (dualComponent w x * c), ← charpoly_diagonal]
    congr 1
    simpa [Matrix.mul_inv_rev] using congrArg Units.val h_diag
  rw [← separable_map (algebraMap E (LocField w.val)), h_charpoly, separable_prod_X_sub_C_iff]
  have h_val_eq : (v ∘ fun i ↦ ((s * d) i).val) = fun i ↦ v (s i).val :=
    funext fun i ↦ by simpa using v_diag_eq_one_of_mem_proIwahori hd i
  exact .of_comp (f := v) (by simpa only [h_val_eq] using hs.injective)

/-- The positive powers of a Hecke element whose terms are strictly dominant at `w` are regular, if
the level at `w` lies in `proIwahori` and `𝔑` does not lie in the conjugate of `w`. -/
lemma isRegularHecke_pow_succ_of_strictlyDominantAt {w : SplitFinPlace E}
    (hw : 𝔑 ∉ (star w.val).asIdeal)
    (h_lev : (levelGU (Fin a) 𝔑).comap (conjAtSplit w) ≤ proIwahori) {f : heckeAlgebra (Fin a) ℂ 𝔑}
    (hf : f.val ∈ spanOn ℂ (strictlyDominantAt w)) (m : ℕ) :
    IsRegularHecke (f ^ (m + 1)) := by
  refine isRegularHecke_of_strictlyDominantAt hw h_lev ?_
  rw [SubmonoidClass.coe_pow]
  induction m with
  | zero => rwa [zero_add, pow_one]
  | succ m ih => exact spanOn.mul ih hf fun _ hg _ hg' ↦ mul_mem_strictlyDominantAt hg hg'

/-- Let the level at `w` lie in `proIwahori` and let `𝔑` not lie in the conjugate of `w`. Then some
Hecke element `b` sends vectors of level `𝔑` to vectors fixed by `proIwahori`, kills no nonzero
vector fixed by `proIwahori`, and commutes with every `c` whose terms are similitudes trivial at
`w`; the terms of `b * c` are strictly dominant at `w`. -/
lemma exists_iwahori_hecke_element (π : Representation ℂ (GL (Fin a) (𝔸f E)) W)
    {w : SplitFinPlace E} (hw : 𝔑 ∉ (star w.val).asIdeal)
    (h_lev : (levelGU (Fin a) 𝔑).comap (conjAtSplit w) ≤ proIwahori) :
    ∃ b : heckeAlgebra (Fin a) ℂ 𝔑,
      b.val ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w) proIwahori 1 ∧
      (∀ x ∈ levelSpace (π.comp (conjAtSplit w)) proIwahori, x ≠ 0 → π.asAlgebraHom b x ≠ 0) ∧
      ∀ c ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w).ker).carrier,
        Commute c b.val ∧ b.val * c ∈ spanOn ℂ (strictlyDominantAt w) := by
  -- On `proIwahori`-fixed vectors `b` is a central translate of an injective operator `U_t`.
  -- `ρ` is the local group at `w` on the smooth vectors of `π`; `t` is strictly dominant (`ht`).
  let ρ : Rep ℂ (GL (Fin a) (LocField w.val)) := Rep.of (smoothVectorRep (π.comp (conjAtSplit w)))
  obtain ⟨t, ht, hU_inj⟩ := exists_iwahoriHeckeHom_injective ρ (v_uniformizer _)
  -- A central `z = N⁻¹` makes the inverse of `z t` integral.
  obtain ⟨N, hN, h_int⟩ := exists_forall_mul_mem_Ô (conjAtSplit w (diagGL t)).inv.uncurry
  let z : GL (Fin a) (𝔸f E) :=
    (GeneralLinearGroup.scalar _ (principalIdele (.mk0 N (mod_cast hN))))⁻¹
  have z_central (g : GL (Fin a) (𝔸f E)) : Commute g z := (commute_scalar_GL _ g).inv_right
  -- `z` is a similitude, since its inverse, the scalar `N`, scales the standard form by `N * N`
  have hz : z ∈ GU E (Fin a) := by
    refine ⟨N * N, by simpa, 1, gram_inv_of_gram_eq ?_⟩
    simp [smul_one_eq_diagonal, ← Matrix.diagonal_natCast, Matrix.diagonal_mul_diagonal]
  have h_int_ij (i j : Fin a) : (N : 𝔸f E) * (conjAtSplit w (diagGL t))⁻¹ i j ∈ Ô E := h_int (i, j)
  have hzt : z * conjAtSplit w (diagGL t) ∈ GUPlus E (Fin a) :=
    ⟨mul_mem hz (by simp), fun i j ↦ by simpa [z, ← nsmul_eq_mul'] using h_int_ij i j⟩
  obtain ⟨b, hb_supp, hb_type, hb⟩ := exists_local_hecke_element π (J := proIwahori)
    (sep_subset _ _) 1 (fun _ hg ↦ ⟨h_lev hg, rfl⟩) hw (diagGL t) z_central hzt
  refine ⟨b, hb_type, fun x hx hx_ne h_zero ↦ ?_, fun c hc ↦ ⟨?_, ?_⟩⟩
  · have hx_fix (g : GL (Fin a) (LocField w.val)) (hg : g ∈ proIwahori) :
        π (conjAtSplit w g) x = x := by simpa using hx ⟨g, hg⟩
    let x' : levelSpace ρ.ρ proIwahori :=
      ⟨⟨x, .mono (residuePreimage ..).mem_nhds_one hx_fix⟩, fun k ↦ Subtype.ext (hx k)⟩
    -- Extend the `proIwahori`-average to a linear map `T` on `W`; then `T z⁻¹ b x = U_t x ≠ 0`.
    obtain ⟨T, hT⟩ := (Submodule.subtype _ ∘ₗ compactMean ρ.ρ proIwahori).exists_extend
    -- `ρ` acts on the smooth vectors of `π` through `conjAtSplit w`, and `U_t` is the mean
    -- over `proIwahori` of the action of `t`.
    have h_smooth (g : GL (Fin a) (LocField w.val)) (y : ρ) :
        ((ρ.ρ g y : ρ) : W) = π (conjAtSplit w g) y := rfl
    have hU_def : (iwahoriHeckeHom ρ ⟨t, ht.monotone⟩ x' : ρ) =
        compactMean ρ.ρ proIwahori (ρ.ρ (diagGL t) (x' : ρ)) := rfl
    have h_eq : (T * π z⁻¹) (π.asAlgebraHom b x) =
        ((iwahoriHeckeHom ρ ⟨t, ht.monotone⟩ x' : ρ) : W) :=
      hb T _ fun j ↦ by
        simpa [x', h_smooth, hU_def] using LinearMap.congr_fun hT (ρ.ρ (j * diagGL t) x')
    have hU : iwahoriHeckeHom ρ ⟨t, ht.monotone⟩ x' = 0 :=
      Subtype.ext (Subtype.ext (by simpa [h_zero] using h_eq.symm))
    have hx'_zero : x' = 0 := (injective_iff_map_eq_zero _).mp hU_inj x' hU
    -- `x` is the vector underlying `x'`
    exact hx_ne (congrArg (fun u : levelSpace ρ.ρ proIwahori ↦ ((u : ρ) : W)) hx'_zero)
  · refine Commute.span_left (forall_mem_image.mpr fun g hg ↦ .span_right ?_ _ hb_supp) _ hc
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    have h_comm : Commute g (conjAtSplit w j * (z * conjAtSplit w (diagGL t))) := by
      simp [commute_conjAtSplit hg, z_central]
    exact h_comm.map _
  · refine spanOn.mul hb_supp hc (forall_mem_range.mpr fun j g hg ↦ ?_)
    have hg_one : dualComponent w g = 1 := MonoidHom.mem_ker.mp hg.2
    -- `dualComponent w (j z t g)` is `j · N t`, since `dualComponent` inverts the scalar `z`; `N t`
    -- is strictly dominant like `t`
    refine ⟨fun i ↦ .mk0 N (mod_cast hN) * t i, by simpa [StrictMono, zero_lt_iff, hN], j, 1, ?_⟩
    rw [map_mul, map_mul, map_mul, dualComponent_conjAtSplit, dualComponent_conjAtSplit, hg_one]
    simp [z, dualComponent, invTransposeGL, Equiv.symm, Units.ext_iff, Matrix.map_natCast,
      map_zero]

/-- An element of the Hecke algebra of level `𝔑` sends vectors of level `𝔑` to vectors of level
`𝔑`. -/
private lemma asAlgebraHom_mem_levelSpace_of_mem_levelSpace
    {π : Representation ℂ (GL (Fin a) (𝔸f E)) W} (f : heckeAlgebra (Fin a) ℂ 𝔑) {x : W}
    (hx : x ∈ levelSpace π (levelGU (Fin a) 𝔑)) :
    π.asAlgebraHom f.val x ∈ levelSpace π (levelGU (Fin a) 𝔑) :=
  f.property.2 hx

/-- The test function. Let `π` be a representation of `GL_a(𝔸f E)` on `W`, and let `φ` be a test
vector of level `𝔑` (nonzero, of cuspidal type `(J, χ)` at `w₀` and spherical at `w₁`). Suppose `φ`
is fixed by a Hecke element `c` supported on unitary similitudes whose component at `w₁` is `1`.
Then there is a Hecke element `b` such that no power of `b * c` kills `φ`, and every positive power
is regular (nonzero at `x⁻¹y⁻¹x`, `y ∈ GL_a(E)`, only if `y` has separable characteristic
polynomial). Every positive power also sends vectors of level `𝔑` to vectors on which `J`, through
`conjAtSplit w₀`, acts by `χ`. -/
theorem exists_test_function {w₀ w₁ : SplitFinPlace E}
    {J : Subgroup (GL (Fin a) (LocField w₀.val))} {χ : J →* ℂ}
    {π : Representation ℂ (GL (Fin a) (𝔸f E)) W} {φ : W}
    (hφ_lev : φ ∈ levelSpace π (levelGU (Fin a) 𝔑)) (hφ_test : IsTestVector 𝔑 π φ w₀ w₁ χ)
    {c : heckeAlgebra (Fin a) ℂ 𝔑}
    (hc : c.val ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w₁).ker).carrier)
    (hcφ : π.asAlgebraHom c φ = φ) :
    ∃ b : heckeAlgebra (Fin a) ℂ 𝔑, ∀ m : ℕ,
      π.asAlgebraHom ((b * c) ^ m).val φ ≠ 0 ∧
      IsRegularHecke ((b * c) ^ (m + 1)) ∧
      ((b * c) ^ (m + 1)).val ∈ fixedToEigen (levelGU (Fin a) 𝔑) (conjAtSplit w₀) J χ := by
  -- Take `b = b₁ b₀`, where `b₀` averages against `χ` over `J` at `w₀` and `b₁` is the element
  -- of `exists_iwahori_hecke_element` at `w₁`.
  -- `χ` is trivial on the level, because the level fixes `φ ≠ 0`.
  have hχ (g : GL (Fin a) (LocField w₀.val)) (hg : conjAtSplit w₀ g ∈ levelGU (Fin a) 𝔑) :
      ∃ h : g ∈ J, χ ⟨g, h⟩ = 1 := by
    refine ⟨hφ_test.level_le hg, smul_left_injective ℂ hφ_test.ne_zero ?_⟩
    -- both `χ ⟨g, _⟩ • φ` and `1 • φ` are the image of `φ` under `conjAtSplit w₀ g`
    exact (mem_levelSpace.mp hφ_test.isEigenvector ⟨g, _⟩).symm.trans
      (mem_levelSpace.mp hφ_lev ⟨_, hg⟩)
  obtain ⟨b₀, hb₀_supp, hb₀_type, hb₀⟩ := exists_local_hecke_element π hφ_test.le_localIntGL χ hχ
    hφ_test.notMem_star_fst 1 Commute.one_right (by simp)
  obtain ⟨b₁, hb₁_type, hb₁_ne, hb₁⟩ :=
    exists_iwahori_hecke_element π hφ_test.notMem_star_snd hφ_test.level_le_proIwahori
  -- `w₁` is neither `w₀` nor its conjugate, so the terms of `b₀ c` are trivial at `w₁`.
  have hw_star : star w₁.val ≠ w₀.val := fun h_eq ↦
    hφ_test.notMem_star_fst (by simpa [← h_eq] using hφ_test.mem_snd)
  have h_term_mem (j : J) :
      conjAtSplit w₀ j * (1 * conjAtSplit w₀ 1) ∈ GU E (Fin a) ⊓ (dualComponent w₁).ker := by
    simp [dualComponent, evalAt_conjAtSplit_of_ne _ hφ_test.place_ne.symm hw_star]
  have hb₀c : b₀.val * c.val ∈ spanOn ℂ (GU E (Fin a) ⊓ (dualComponent w₁).ker).carrier :=
    spanOn.mul hb₀_supp hc (forall_mem_range.mpr fun j g hg ↦ Subgroup.mul_mem _ (h_term_mem j) hg)
  obtain ⟨h_comm_val, h_supp⟩ := hb₁ _ hb₀c
  have h_comm : Commute (b₀ * c) b₁ := Subtype.ext h_comm_val
  have hb₀φ : π.asAlgebraHom b₀ φ = φ := by
    simpa using hb₀ 1 φ (by simpa using hφ_test.isEigenvector)
  -- By induction every power of `b₁ b₀ c` sends `φ` to a nonzero `proIwahori`-fixed vector.
  have h_vec (m : ℕ) :
      π.asAlgebraHom ((b₁ * (b₀ * c)) ^ m).val φ ∈
          levelSpace (π.comp (conjAtSplit w₁)) proIwahori ∧
        π.asAlgebraHom ((b₁ * (b₀ * c)) ^ m).val φ ≠ 0 := by
    induction m with
    | zero => simpa [hφ_test.ne_zero] using fun g hg ↦ hφ_test.fixed ⟨g, hg.1⟩
    | succ m ih =>
      -- `b₀ c` commutes past the power and fixes `φ`.
      have h_succ : π.asAlgebraHom ((b₁ * (b₀ * c)) ^ (m + 1)).val φ =
          π.asAlgebraHom b₁ (π.asAlgebraHom ((b₁ * (b₀ * c)) ^ m).val φ) := by
        simp [pow_succ', ((h_comm.mul_right rfl).pow_right m).right_comm, hcφ, hb₀φ]
      rw [h_succ]
      exact ⟨hb₁_type (asAlgebraHom_mem_levelSpace_of_mem_levelSpace _ hφ_lev), hb₁_ne _ ih.1 ih.2⟩
  refine ⟨b₁ * b₀, fun m ↦ ?_⟩
  rw [mul_assoc]
  refine ⟨(h_vec m).right, isRegularHecke_pow_succ_of_strictlyDominantAt hφ_test.notMem_star_snd
    hφ_test.level_le_proIwahori h_supp m, ?_⟩
  -- The power begins with `b₀`, which produces `χ`-eigenvectors.
  intro V _ _ ρ x hx
  have h_begin : (b₁ * (b₀ * c)) ^ (m + 1) = b₀ * (c * (b₁ * (b₁ * (b₀ * c)) ^ m)) := by
    rw [pow_succ', ← h_comm, mul_assoc, mul_assoc]
  rw [h_begin, MulMemClass.coe_mul, map_mul]
  exact hb₀_type (asAlgebraHom_mem_levelSpace_of_mem_levelSpace _ hx)

end New.Variety
