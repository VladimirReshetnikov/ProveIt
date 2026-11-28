import Lib.GaloisRep.BaseChange.CommutingHeckeFamilies

/-!
# Hecke-stable matching pairs for a step E'/E at split matched places

This file constructs sets of matching pairs of test functions (`New.IsMatchingPairAbove`) for a
step `E'/E` that are stable under Hecke operators. It works at places of `E` that are split over
`E⁺` and matched (`New.IsMatched`: `μ` is trivial there and the places above are permuted freely
by the Galois group). The pairs come from functions that are bi-invariant under the elements
integral at a set `V` of places of `E'` with one place above each pair `{w, star w}`. This file
also gives a criterion, `New.IsStep.isNormRoot_of_one_side`, for a root (`New.IsNormRoot`) that
is `1` outside the places above a set `T` of places of `E` containing no two conjugate ones.

## Main definitions and results

* `New.biInvariantPairs`, `New.isMatchingPairAbove_of_mem_biInvariantPairs`: the pairs
  `(F ∘ baseChangeGf, 1_K * F)`, where `F` is bi-invariant at `V`; they are matching pairs above
  the places below `V`.
* `New.exists_isHeckeStableMatching`: a set of matching pairs that contains the pair of indicator
  functions of the level and is stable under the Hecke operators `(T_{w,j}, T_{u,j})`.

Notions from other files:
* `New.Gf.supportedOn`, `New.Gf.trivialOn`: the elements with component `1` at every place outside
  `S ∪ S̄`, and those with component `1` at every place of `S`.
* `New.localLevel`: the elements whose component at each `w ∈ S` lies in `K w`; by default `K w` is
  `New.localIntGL`, the integral matrices with integral inverse.
* `New.IsStep`: the extension `E'/E` with a character `μ` of the finite ideles of `E` that detects
  norms.
* `New.IsMatched`: the places of `E` that split completely in `E'` and at which `μ` is trivial.
* `New.IsMatchingPairAbove`: matching pairs of functions at the places of `E'` above `S ∪ S̄`.

## Relation to the literature

Known; see `Lib.GaloisRep.BaseChange.PrimeDegreeTransfer` and `Lib.Adelic.Hecke.ClassSums` for
sources.
-/

namespace New

section MatchedPlacePairs

open Set Matrix RingHom Polynomial Gf Variety Module

variable {E E' n W : Type _} [Field E] [CMType E] [Field E'] [CMType E'] [Algebra E E'] [Fintype n]
  [DecidableEq n] {σ : Gal(E'/E)} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Gf E' n) W} {u : FinPlace E'}

attribute [-simp] evalAt_apply in
/-- Let `E'/E` be a step for `μ` and `σ` an element of `Gal(E'/E)`. Let `T` be a set of places of
`E` at which `μ` is trivial and which contains no place together with its conjugate, and let `B`
be the set of places of `E'` above `T` and its conjugates. Let `z` be a polynomial over the finite
adeles of `E'` that is `1` at every place not above `T`, and whose twisted norm along `σ`, with
`p` factors, is `X` modulo `P` at every place above `T`. Then:
* `z` is a norm root for `P` on `B` (`New.IsNormRoot`, for the ideles killed by `μ` after the
  norm);
* if unitary `γ` and `a` satisfy `a * ((idem B • z)(γ))ᴴ = (idem B • z)(γ)`, then at each place
  `u` above `T` the component of `a` is `z_u(γ_u)`. -/
lemma IsStep.isNormRoot_of_one_side {μ : (𝔸f E)ˣ →* ℂˣ} (hμ : IsStep E' μ)
    {B : Set (FinPlace E')} {T : Set (FinPlace E)} (hB : B = placesAbove E' T)
    (hμ_loc : ∀ w ∈ T, ∀ x : (LocField w)ˣ, μ (locIdele w x) = 1) (hT : ∀ w ∈ T, star w ∉ T)
    {p : ℕ} {P z : (𝔸f E')[X]} [NeZero p]
    (hz : ∀ u : FinPlace E', u.below E ∉ T → z.map (evalAt u) = 1)
    (hP : ∀ u : FinPlace E', u.below E ∈ T →
      P.map (evalAt u) ∣ (twistedNorm (Polynomial.map (adeleMap σ)) p z).map (evalAt u) - X) :
    IsNormRoot n (adeleMap σ) p (idem B) (kerCompNorm E' μ) P z ∧
      ∀ γ a : Gf E' n, IsRootQuotient γ (idem B • z) a → ∀ u : FinPlace E', u.below E ∈ T →
        (a.atPlace u : Matrix n n (LocField u)) =
          aeval (γ.atPlace u : Matrix n n (LocField u)) (z.map (evalAt u)) := by
  classical
  -- The norm of `z`, evaluated at a unitary `g` with characteristic polynomial `P`, is `g` at the
  -- places above `T` and `1` elsewhere. So it is invertible, which makes `z` prime to `P`.
  have ev_idem (u : FinPlace E') (S : Set (FinPlace E')) :
      evalAt u (idem S) = if u ∈ S then 1 else 0 := idem_apply S u
  have mem_B (u : FinPlace E') : u ∈ B ↔ u.below E ∈ T ∨ star (u.below E) ∈ T := by
    rw [hB]
    rfl
  refine ⟨⟨?_, ?_⟩, fun γ a ha u hu ↦ ?_⟩
  · -- off `B` the polynomial `z` is `1`
    ext i u
    by_cases huB : u ∈ B
    · simp [← evalAt_apply, ev_idem, huB]
    · have hz_u : z.map (evalAt u) = 1 := hz u fun hu ↦ huB ((mem_B u).2 (.inl hu))
      simp [← evalAt_apply, ← coeff_map, ev_idem, huB, hz_u]
  · rintro g rfl
    have h_norm : (twistedNorm (Polynomial.map (adeleMap σ)) p z).aeval g.val.val =
        cutGL (idem_mul_self (FinPlace.below E ⁻¹' T)) g.val := by
      refine matrix_ext_evalAt fun u ↦ ?_
      by_cases hu : u.below E ∈ T
      · -- the norm is `X` modulo the characteristic polynomial; use Cayley–Hamilton
        obtain ⟨q, hq⟩ := hP u hu
        have h_norm_u : (twistedNorm (Polynomial.map (adeleMap σ)) p z).map (evalAt u) =
            g.val.val.charpoly.map (evalAt u) * q + X := sub_eq_iff_eq_add.1 hq
        rw [map_aeval_matrix, h_norm_u]
        simp [ev_idem, hu, aeval_self_charpoly, ← charpoly_map, cutGL, Matrix.map_add, map_smul']
      · -- no conjugate of `u` lies above `T`, so every factor of the norm is `1` at `u`
        have h_conj (f : E' →+* E') : (z.map (adeleMap f)).map (evalAt u) =
            (z.map (evalAt (u.comap f))).map (locMap f rfl) :=
          (z.map_map (adeleMap f) (evalAt u)).trans
            (z.map_map (evalAt (u.comap f)) (locMap f rfl)).symm
        simp [h_conj, hz, hu, ev_idem, twistedNorm_map_eq_prod, adeleMap_gal_pow, map_aeval_matrix,
          Polynomial.map_prod, cutGL, Matrix.map_add, map_smul']
    have h_coprime :
        IsCoprime g.val.val.charpoly (∏ i ∈ .range p, z.map (adeleMap σ ^ i)) := by
      rw [← twistedNorm_map_eq_prod, ← isUnit_aeval_iff_isCoprime, h_norm]
      exact Units.isUnit _
    -- `z` is the factor `i = 0` of its norm
    have h_coprime_z : IsCoprime g.val.val.charpoly (z.map (adeleMap σ ^ 0)) :=
      h_coprime.of_prod_right 0 (Finset.mem_range.2 (NeZero.pos p))
    obtain ⟨c, b, hb⟩ := h_coprime_z
    refine ⟨fun m M hM ↦ ?_, matrix_ext_evalAt fun u ↦ ?_⟩
    · -- `det z(M)` is an idele `d`; above `T` use `hμ_loc`, elsewhere its component is `1`
      have h_eval : aeval M (c * g.val.val.charpoly + b * z.map (adeleMap σ ^ 0)) = 1 := by
        rw [hb, map_one]
      have h_inv : aeval M b * aeval M z = 1 := by simpa [hM, one_def] using h_eval
      obtain ⟨d, hd⟩ : IsUnit (aeval M z).det := isUnit_det_of_left_inverse h_inv
      refine ⟨d, mem_of_locIdele_mem hμ.isClopen_kerCompNorm.isClosed fun u ↦ ?_, hd⟩
      by_cases hu : u.below E ∈ T
      · simp [adeleNorm_locIdele, hμ_loc _ hu]
      · have hd_val : (ideleAt u d : LocField u) = 1 := by
          simp [ideleAt, map_det, hd, hz u hu, map_aeval_matrix]
        simp [Units.val_eq_one.1 hd_val]
    · -- above `T` this reads `g * 1 = g`, at the conjugate places `g * g⁻¹ = 1`, and at the
      -- other places `1 * 1 = 1`
      rw [h_norm]
      by_cases hu : u.below E ∈ T
      · simp [← U.inv_val_eq_conjTranspose, Matrix.map_sub, ev_idem, mem_B, hu, hT _ hu, cutGL,
          star_idem, Matrix.map_add, map_smul', below_star]
      · by_cases hu' : star (u.below E) ∈ T <;>
          simp [← U.inv_val_eq_conjTranspose, Matrix.map_sub, ev_idem, mem_B, hu, hu', cutGL,
            star_idem, Matrix.map_add, map_smul', below_star]
  · -- take `ha` at `u`: the adjoint factor comes from `star u`, not above `T`, where `z = 1`
    have h_adj (M : Matrix n n (𝔸f E')) :
        Mᴴ.map (evalAt u) = (M.map (evalAt (star u)))ᵀ.map (conjLoc (star_star u)) := rfl
    have ha_u : ((a : Matrix n n (𝔸f E')) * (aeval (γ : Matrix n n (𝔸f E')) (idem B • z))ᴴ).map
          (evalAt u) = (aeval (γ : Matrix n n (𝔸f E')) (idem B • z)).map (evalAt u) :=
      congrArg (Matrix.map · (evalAt u)) ha
    show (a : Matrix n n (𝔸f E')).map (evalAt u) =
      aeval ((γ : Matrix n n (𝔸f E')).map (evalAt u)) (z.map (evalAt u))
    simpa [hB, mem_B, ev_idem, hz, hT, hu, h_adj, placesAbove, star_idem, map_smul', below_star,
      map_aeval_matrix] using ha_u

/-- Let `π` be a representation of the unitary group over `E'`, let `u` be a split place of `E'`
whose place `w` below is split, and let `E_w → E'_u` be onto. Let `x` be spherical at `u` (fixed by
the elements supported at `u` and integral there) and fixed by the elements supported at the other
places above `w` and their conjugates. Then the Hecke operator `T_{w,j}` of `π ∘ baseChangeGf` and
the Hecke operator `T_{u,j}` of `π` agree on `x`. -/
lemma heckeSplit_comp_baseChangeGf (hu : u.IsSplit) (hw : (u.below E).IsSplit)
    (h_surj : Function.Surjective (locMap (algebraMap E E') (Eq.refl (u.below E)))) {j : ℕ}
    {x : W} (hx : x ∈ sphericalAt π u)
    (h_fix : ∀ k ∈ supportedOn n (FinPlace.below E ⁻¹' {u.below E} \ {u}), π k x = x) :
    heckeSplit (π.comp baseChangeGf) hw j x = heckeSplit π hu j x := by
  -- Transport the Hecke operator along `φ : GL n (E_w) → GL n (E'_u)`, `w` the place below `u`.
  -- It is onto since `E_w → E'_u` is, and the preimage of `localIntGL n u` is `localIntGL n w`.
  let φ : GL n (LocField (u.below E)) →* GL n (LocField u) := GeneralLinearGroup.map (locMap _ rfl)
  have h_right_inv (g : GL n (LocField u)) (k : localIntGL n u) :
      (basicDoubleCoset n u j).indicator (1 : GL n (LocField u) → ℂ) (g * k) =
        (basicDoubleCoset n u j).indicator 1 g := by
    simp
  have h_finite : HasFiniteCosets (localIntGL n (u.below E))
      ((basicDoubleCoset n (u.below E) j).indicator (1 : GL n (LocField (u.below E)) → ℂ)) := by
    simp
  have h_preimage (g : GL n (LocField (u.below E))) :
    φ g ∈ localIntGL n u ↔ g ∈ localIntGL n (u.below E) :=
    map_locMap_mem_intGL_iff rfl
  refine heckeFun_comp φ h_right_inv ((mem_sphericalAt_iff _).1 hx) h_finite
    (GL_map_surjective _ h_surj) h_preimage (fun g ↦ ?_) fun g ↦ ?_
  · -- the two elements differ by one supported at the other places above `w` and their
    -- conjugates, and such an element fixes `x`
    show π (baseChangeGf (ofSplitPlace hw g)) x = π (ofSplitPlace hu (φ g)) x
    have h_supp : (ofSplitPlace hu (φ g))⁻¹ * baseChangeGf (ofSplitPlace hw g) ∈
        supportedOn n (FinPlace.below E ⁻¹' {u.below E} \ {u}) := by
      -- the two elements have the same component at `u`
      have h_at_u : ((ofSplitPlace hu (φ g))⁻¹ * baseChangeGf (ofSplitPlace hw g)).atPlace u =
        1 := by
        simp [φ, atPlace_baseChangeGf]
      refine mem_supportedOn.2 fun v hv hv_star ↦ ?_
      by_cases h_star : star v = u
      · subst h_star
        exact atPlace_star_eq_one_iff.1 h_at_u
      by_cases h_eq : v = u
      · rwa [h_eq]
      -- both are `1` at a place that lies above neither `w` nor `star w`
      have h_below : v.below E ≠ u.below E := fun h ↦ hv ⟨h, h_eq⟩
      have h_below_star : star (v.below E) ≠ u.below E :=
        fun h ↦ hv_star ⟨(below_star v).trans h, h_star⟩
      simp [h_eq, h_star, h_below, h_below_star, atPlace_ofSplitPlace_of_ne, atPlace_baseChangeGf]
    calc π (baseChangeGf (ofSplitPlace hw g)) x
        = π (ofSplitPlace hu (φ g) * ((ofSplitPlace hu (φ g))⁻¹ * baseChangeGf (ofSplitPlace hw g)))
          x := by
          rw [mul_inv_cancel_left]
      _ = π (ofSplitPlace hu (φ g)) (π ((ofSplitPlace hu (φ g))⁻¹ * baseChangeGf
        (ofSplitPlace hw g)) x) := by
          rw [map_mul, Module.End.mul_apply]
      _ = π (ofSplitPlace hu (φ g)) x := by rw [h_fix _ h_supp]
  · -- a uniformiser of `E'_u` comes from `E_w`, so valuations and `basicDoubleCoset` are preserved
    have h_unit : ∃ ϖ : LocField (u.below E),
        IsUnit (Valued.v (locMap (algebraMap E E') rfl ϖ)).log := by
      refine (h_surj (uniformizer u)).imp fun ϖ hϖ ↦ ?_
      rw [hϖ]
      simp
    have h_val (y : LocField (u.below E)) :
        Valued.v (locMap (algebraMap E E') rfl y) = Valued.v y :=
      v_locMap_eq_of_isUnit_log _ rfl h_unit y
    -- `-coe_units_inv` keeps `↑(g⁻¹)` whole, so that `← map_inv` moves the map past the inverse
    simp [φ, basicDoubleCoset, indicator_apply, ← map_inv, -coe_units_inv, ← map_det,
      ← mapMatrix_apply, h_val]

/-- A set `St` of pairs `(f, φ)` of functions on the finite adelic unitary groups over `E` and `E'`
is stable under the Hecke operators `(T_{w,j}, T_{u,j})` for every `j`: for each pair, the pair
`(T_{w,j} f, T_{u,j} φ)` lies in `St`, the groups acting by left translation; `T_{u,j}` is
`heckeSplit`, the Hecke operator of the indicator of `basicDoubleCoset n u j` at level
`localIntGL n u`. The condition is empty unless `w` and `u` are both split. -/
def IsHeckeStableAt (St : Set ((Gf E n → ℂ) × (Gf E' n → ℂ))) (w : FinPlace E)
    (u : FinPlace E') : Prop :=
  ∀ x ∈ St, ∀ (hw : w.IsSplit) (hu : u.IsSplit) (j : ℕ),
    (heckeSplit leftTranslation hw j x.1, heckeSplit leftTranslation hu j x.2) ∈ St

/-- A set `St` of pairs of functions on the finite adelic unitary groups over `E` and `E'`, all of
them matching pairs of level `B` above `S` for `σ` and `μ` (`New.IsMatchingPairAbove`). It contains
the indicator function of `B`, paired with its composition with `baseChangeGf`, and for each
place `w` of `S` it is stable under the Hecke operators at `w` and at some place above `w`. -/
structure IsHeckeStableMatching (σ : Gal(E'/E)) (μ : (𝔸f E)ˣ →* ℂˣ) (S : Set (FinPlace E))
    (B : Subgroup (Gf E' n)) (St : Set ((Gf E n → ℂ) × (Gf E' n → ℂ))) : Prop where
  /-- `St` contains the indicator function of `B`, paired with its composition with
  `baseChangeGf`. -/
  indicator_mem :
    ((B : Set (Gf E' n)).indicator 1 ∘ baseChangeGf, (B : Set (Gf E' n)).indicator 1) ∈ St
  /-- Every member of `St` is a matching pair of level `B` above `S`. -/
  isMatchingPairAbove : ∀ x ∈ St, IsMatchingPairAbove σ μ S B x.1 x.2
  /-- Above each `w` in `S` there is a place `u` such that `St` is stable under
  `(T_{w,j}, T_{u,j})`. -/
  exists_isHeckeStableAt : ∀ w ∈ S, ∃ u : FinPlace E', u.below E = w ∧ IsHeckeStableAt St w u

variable (E) in
/-- The unordered pair made of the place of `E` below `u` and its conjugate. -/
private noncomputable def belowPair (u : FinPlace E') : Sym2 (FinPlace E) :=
  s(u.below E, star (u.below E))

omit [CMType E'] in
/-- Let `S` be a set of split places of `E`. There is a set `V` of places of `E'` with exactly one
place above each pair `{w, star w}` with `w ∈ S`. In detail:
* every place of `V` lies above a place of `S`;
* no two places of `V` lie above the same place of `E`;
* the places below `V` include no place together with its conjugate;
* `S` and the places below `V` have the same closure under conjugation. -/
lemma exists_places_above_one_side {S : Set (FinPlace E)} (h_split : ∀ w ∈ S, w.IsSplit) :
    ∃ V : Set (FinPlace E'),
      (∀ u ∈ V, u.below E ∈ S) ∧
      InjOn (FinPlace.below E) V ∧
      (∀ w ∈ FinPlace.below E '' V, star w ∉ FinPlace.below E '' V) ∧
      S.conjClosure = (FinPlace.below E '' V).conjClosure := by
  -- Choose `V` among the places above `S` such that `belowPair` is a bijection from `V` onto the
  -- pairs `{w, star w}` with `w ∈ S`.
  obtain ⟨V, hV, h_bij⟩ := exists_subset_bijOn (FinPlace.below (L := E') E ⁻¹' S) (belowPair E)
  have hV_inj_pair : InjOn (belowPair E) V := h_bij.injOn
  have hV_surj_pair :
      SurjOn (belowPair E) V (belowPair E '' (FinPlace.below (L := E') E ⁻¹' S)) :=
    h_bij.surjOn
  have h_cover (w : FinPlace E) (hw : w ∈ S) :
      ∃ v ∈ V, v.below E = w ∨ v.below E = star w := by
    obtain ⟨u, rfl⟩ := FinPlace.comap_surjective (algebraMap E E') w
    obtain ⟨v, hv, h_pair⟩ : ∃ v ∈ V, belowPair E v = belowPair E u :=
      hV_surj_pair (mem_image_of_mem _ hw)
    rcases Sym2.eq_iff.1 h_pair with ⟨h_eq, -⟩ | ⟨h_eq, -⟩
    · exact ⟨v, hv, .inl h_eq⟩
    · exact ⟨v, hv, .inr h_eq⟩
  have hV_inj : InjOn (FinPlace.below E) V := by
    intro u hu v hv h_below
    have h_pair_eq : belowPair E u = belowPair E v := by simp [belowPair, h_below]
    exact hV_inj_pair hu hv h_pair_eq
  refine ⟨V, hV, hV_inj, ?_, subset_antisymm ?_ ?_⟩
  · rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, hvu⟩
    have h_pair_eq : belowPair E u = belowPair E v := by simp [belowPair, hvu, Sym2.eq_swap]
    obtain rfl : u = v := hV_inj_pair hu hv h_pair_eq
    exact h_split _ (hV hu) hvu.symm
  · rintro w (hw | hw)
    · obtain ⟨v, hv, hvw | hvw⟩ := h_cover w hw
      exacts [.inl ⟨v, hv, hvw⟩, .inr ⟨v, hv, hvw⟩]
    · obtain ⟨v, hv, hvw | hvw⟩ := h_cover (star w) hw
      exacts [.inr ⟨v, hv, hvw⟩, .inl ⟨v, hv, hvw.trans (star_star w)⟩]
  · have h_sub : FinPlace.below E '' V ⊆ S := image_subset_iff.2 hV
    exact union_subset_union h_sub (preimage_mono h_sub)

/-- Let `u` and `v` be places of `E'` above the same place of `E`. If the base change of `g` is
integral at `v` (its component lies in `localIntGL`, the integral matrices with integral inverse),
then it is integral at `u`. -/
lemma atPlace_baseChangeGf_mem_localIntGL {v : FinPlace E'} (h_below : v.below E = u.below E)
    {g : Gf E n} (hg : (baseChangeGf g).atPlace v ∈ localIntGL n v) :
    (baseChangeGf g).atPlace u ∈ localIntGL n u := by
  have h_down : g.atPlace (v.below E) ∈ localIntGL n (v.below E) :=
    (map_locMap_mem_intGL_iff rfl).1 hg
  rw [h_below] at h_down
  exact (map_locMap_mem_intGL_iff rfl).2 h_down

omit [CMType E] in
/-- Let `galoisGf σ` be the action of `σ` on the finite adelic unitary group, entry by entry. If
`k` is integral at the place `u.comap (σ ^ i)`, then its `i`-th image under `galoisGf σ` is
integral at `u`. -/
lemma atPlace_iterate_galoisGf_mem_localIntGL (i : ℕ) {k : Gf E' n}
    (hk : k.atPlace (u.comap ↑(σ ^ i)) ∈ localIntGL n (u.comap ↑(σ ^ i))) :
    ((galoisGf σ)^[i] k).atPlace u ∈ localIntGL n u := by
  induction i generalizing k with
  | zero => exact hk
  | succ i ih => exact ih ((map_locMap_mem_intGL_iff _).2 hk)

/-- If every `g ≠ 1` in the Galois group moves `u`, then `E_w → E'_u` is onto, where `w` is the
place below `u`. -/
lemma locMap_surjective_of_comap_ne [IsGalois E E']
    (h_moved : ∀ g ≠ (1 : Gal(E'/E)), u.comap g ≠ u) :
    Function.Surjective (locMap (algebraMap E E') (Eq.refl (u.below E))) := by
  -- The norm of the adele that is `y` at `u` and `1` elsewhere has component `y` at `u`.
  intro y
  have h_norm : finAdeleIncl E E' (adeleNorm E E' (1 + singleAdele u (y - 1))) =
      ∏ g : Gal(E'/E), adeleMap g (1 + singleAdele u (y - 1)) :=
    finAdeleIncl_adeleNorm E E' (1 + singleAdele u (y - 1))
  have h_prod :
      evalAt u (∏ g : Gal(E'/E), adeleMap g (1 + singleAdele u (y - 1))) = y := by
    have h_coe_one : ((1 : Gal(E'/E)) : E' →+* E') = RingHom.id E' := rfl
    rw [map_prod, Fintype.prod_eq_single 1, h_coe_one, adeleMap_id]
    · simp
    · simp +contextual [h_moved, adeleMap_apply]
  exact ⟨_, (congrArg (evalAt u) h_norm).trans h_prod⟩

variable (E) in
/-- The places of `E'` outside `V` that lie above the same place of `E` as a place of `V`. -/
def otherConjugates (V : Set (FinPlace E')) : Set (FinPlace E') :=
  FinPlace.below E ⁻¹' FinPlace.below E '' V \ V

/-- `F` is invariant on both sides under the elements `k` that are integral at `V`:
`F (k⁻¹ * g) = F g` (left translation) and `F (g * k) = F g` for every `g`. -/
def IsBiInvariantAt (V : Set (FinPlace E')) (F : Gf E' n → ℂ) : Prop :=
  ∀ k ∈ localLevel n V, leftTranslation k F = F ∧ ∀ g : Gf E' n, F (g * k) = F g

variable (E n) in
/-- The pairs `(F ∘ baseChangeGf, 1_K * F)`, where `F` is bi-invariant at `V` and `K` is the
group of elements integral at `otherConjugates E V`. -/
noncomputable def biInvariantPairs (V : Set (FinPlace E')) :
    Set ((Gf E n → ℂ) × (Gf E' n → ℂ)) :=
  {(F ∘ baseChangeGf, indicator (localLevel n (otherConjugates E V)) 1 * F) |
    (F : Gf E' n → ℂ) (_ : IsBiInvariantAt V F)}

/-- An element is integral at every place above the places below `V` and their conjugates if
and only if it is integral at the places of `V` and at the other places above the same places of
`E` (`New.otherConjugates`). -/
lemma mem_localLevel_placesAbove_image {V : Set (FinPlace E')} {g : Gf E' n} :
    g ∈ localLevel n (placesAbove E' (FinPlace.below E '' V)) ↔
      g ∈ localLevel n V ∧ g ∈ localLevel n (otherConjugates E V) := by
  -- A unitary element is integral at `star u` iff it is integral at `u`.
  constructor
  · -- the places of `V` and the other conjugates all lie above the places below `V`
    intro hg
    refine ⟨fun u hu ↦ hg u (.inl ⟨u, hu, rfl⟩), ?_⟩
    rintro u ⟨hu_below, -⟩
    exact hg u (.inl hu_below)
  rintro ⟨hgV, hgA⟩
  have h_fibre (u : FinPlace E') (hu : u.below E ∈ FinPlace.below E '' V) :
      g.atPlace u ∈ localIntGL n u := by
    by_cases huV : u ∈ V
    · exact hgV u huV
    · exact hgA u ⟨hu, huV⟩
  rintro u (hu | hu)
  · exact h_fibre u hu
  · have h_star_below : (star u).below E ∈ FinPlace.below E '' V := by rwa [below_star]
    exact atPlace_star_mem_iff.1 (h_fibre (star u) h_star_below)

/-- Let `E'/E` be a step for `μ` and `σ ≠ 1`. Let `V` be a set of places of `E'` above matched
places of `E` (`New.IsMatched`), with at most one place above each place of `E`, and such that the
places below `V` include no place together with its conjugate. Then every pair in
`biInvariantPairs E n V` is a matching pair above the places below `V`, of level the group of
elements integral at the places above them and their conjugates. These pairs are
`(F ∘ baseChangeGf, 1_K * F)`, with `F` bi-invariant at `V` and `K` the elements integral at
`otherConjugates E V`. -/
lemma isMatchingPairAbove_of_mem_biInvariantPairs {μ : (𝔸f E)ˣ →* ℂˣ} (hσ : σ ≠ 1)
    [hμ : IsStep E' μ] {V : Set (FinPlace E')} (h_matched : ∀ v ∈ V, IsMatched E' μ (v.below E))
    (hV_inj : InjOn (FinPlace.below E) V)
    (hV_side : ∀ w ∈ FinPlace.below E '' V, star w ∉ FinPlace.below E '' V)
    {x : (Gf E n → ℂ) × (Gf E' n → ℂ)} (hx : x ∈ biInvariantPairs E n V) :
    IsMatchingPairAbove σ μ (FinPlace.below E '' V)
      (localLevel n (placesAbove E' (FinPlace.below E '' V))) x.1 x.2 := by
  classical
  -- The root is `X` at `V` and `1` elsewhere. Write `A` for the other conjugates.
  obtain ⟨F, hF, rfl⟩ := hx
  set B := localLevel n (placesAbove E' (FinPlace.below E '' V))
  set A := otherConjugates E V with hA
  have hB {g : Gf E' n} : g ∈ B ↔ g ∈ localLevel n V ∧ g ∈ localLevel n A :=
    mem_localLevel_placesAbove_image
  have h_bij : Function.Bijective (fun i : Fin (finrank E E') ↦ σ ^ i.val) :=
    bijective_pow_of_ne_one_of_prime_finrank hσ
  obtain ⟨h_inj, h_surj⟩ := h_bij
  -- the Galois group acts freely above matched places, and an orbit meets `V` at most once
  have h_unique {u : FinPlace E'} {g d : Gal(E'/E)} (hg : u.comap g ∈ V) :
      u.comap d ∈ V ↔ d = g := by
    obtain ⟨d, rfl⟩ := mul_left_surjective g d
    refine ⟨fun hd ↦ mul_eq_left.2 ?_, fun hdg ↦ by rwa [hdg]⟩
    have h_fixed : ((u.comap g : FinPlace E').comap d : FinPlace E') = u.comap g :=
      hV_inj hd hg ((below_comap _ u).trans (below_comap _ u).symm)
    -- by `IsMatched`, only `d = 1` fixes the place `u.comap g`
    exact (((h_matched _ hg).2 _ rfl).2 d).mtr h_fixed
  refine ⟨fun k hk ↦ ?_, fun P _hP_char _hP_fixed ↦ ⟨1 + idem V • (X - 1), ?_⟩⟩
  · -- twisted invariance under `B`, which is stable under `σ`
    have hσk : galoisGf σ k ∈ B := by
      intro u hu
      have hu_comap : u.comap ↑(σ ^ 1) ∈ placesAbove E' (FinPlace.below E '' V) := by
        simpa [placesAbove] using hu
      exact atPlace_iterate_galoisGf_mem_localIntGL 1 (hk _ hu_comap)
    intro δ
    show ((localLevel n A : Set (Gf E' n)).indicator 1 * F : Gf E' n → ℂ) (k⁻¹ * δ * galoisGf σ k) =
      ((localLevel n A : Set (Gf E' n)).indicator 1 * F : Gf E' n → ℂ) δ
    simp_all [IsBiInvariantAt, indicator, leftTranslation, funext_iff, mul_mem_cancel_left,
      mul_mem_cancel_right]
  have hμ_loc : ∀ w ∈ FinPlace.below E '' V, ∀ x : (LocField w)ˣ, μ (locIdele w x) = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨h_trivial, -⟩ := h_matched v hv
    exact h_trivial
  have h_one (u : FinPlace E') (hu : u.below E ∉ FinPlace.below E '' V) :
      (1 + idem V • (X - 1) : (𝔸f E')[X]).map (evalAt u) = 1 := by
    have huV : u ∉ V := fun huV ↦ hu ⟨u, huV, rfl⟩
    simp [huV]
  -- at a Galois conjugate of a place of `V` one factor of the norm is `X`, the others are `1`
  have h_dvd (u : FinPlace E') (hu : u.below E ∈ FinPlace.below E '' V) :
      P.map (evalAt u) ∣ (twistedNorm (Polynomial.map (adeleMap σ)) (finrank E E')
        (1 + idem V • (X - 1))).map (evalAt u) - X := by
    obtain ⟨v, hv, h_below⟩ := hu
    obtain ⟨i, rfl⟩ := h_surj.exists.1 (FinPlace.exists_gal_comap_eq h_below.symm)
    simp [Finset.prod_range, add_ite, h_unique hv, h_inj.eq_iff, twistedNorm_map_eq_prod,
      adeleMap_gal_pow, Polynomial.map_prod, adeleMap_apply, idem_apply]
  obtain ⟨h_root, h_at⟩ :=
    hμ.isNormRoot_of_one_side (n := n) rfl hμ_loc hV_side h_one h_dvd
  refine ⟨h_root, fun (γ a : Gf E' n) _ ha ↦ ?_⟩
  -- `a` is `γ` at `V` and `1` at `A`
  have h_off : a ∈ trivialOn n A ∧ γ⁻¹ * a ∈ trivialOn n V := by
    -- `↓` makes the membership lemmas fire first
    simp +contextual [↓mem_trivialOn, Units.ext_iff, h_at _ _ ha, ↓mem_image_of_mem,
      hA, otherConjugates]
  obtain ⟨haA_triv, haV_triv⟩ := h_off
  have haA : a ∈ localLevel n A := trivialOn_le_localLevel haA_triv
  have haV : γ⁻¹ * a ∈ localLevel n V := trivialOn_le_localLevel haV_triv
  -- write the degree as a successor, so that `twistedNorm δ` splits off its first factor `δ`
  rw [← Nat.succ_pred_prime hμ.out] at *
  refine ⟨?_, ?_⟩
  · -- first clause: `F γ = F a`, by invariance of `F` under `γ⁻¹ * a`
    obtain ⟨-, hF_right⟩ := hF _ haV
    simp +contextual [← hF_right γ, haA]
  rintro δ rfl hδ_ne
  have hδ : δ ∈ localLevel n A := by
    by_contra h_not
    simp [h_not] at hδ_ne
  -- the conjugates `σ ^ (i + 1) δ` in `twistedNorm δ` are integral at `V`, as `δ` is at `A`
  have h_rest :
      ((List.range (finrank E E').pred).map fun i ↦ (galoisGf σ)^[i + 1] δ).prod ∈
        localLevel n V := by
    refine list_prod_mem (List.forall_mem_map.2 fun i hi u hu ↦ ?_)
    refine atPlace_iterate_galoisGf_mem_localIntGL _ (hδ _ ⟨⟨u, hu, (below_comap _ u).symm⟩, ?_⟩)
    intro h_mem
    exact h_inj.ne (Fin.succ_ne_zero ⟨i, List.mem_range.1 hi⟩) ((h_unique (g := 1) hu).1 h_mem)
  -- second clause, `a⁻¹ * δ ∈ B`: at `A` both factors are integral; at `V` it is `(γ⁻¹ * a)⁻¹`
  -- divided by the product of those conjugates, as `γ` is `δ` times that product
  have h_at_V : a⁻¹ * δ ∈ localLevel n V := by
    simpa [twistedNorm, mul_div_assoc] using div_mem (inv_mem haV) h_rest
  have h_at_A : a⁻¹ * δ ∈ localLevel n A := mul_mem (inv_mem haA) hδ
  exact hB.2 ⟨h_at_V, h_at_A⟩

/-- Let `V` be a set of places of `E'` with at most one place above each place of `E`, such that the
places below `V` include no place together with its conjugate. Let `u` lie in `V` or be conjugate to
a place of `V`, with `E_w → E'_u` onto for the place `w` below `u`. Then the set
`biInvariantPairs E n V` is stable under the Hecke operators at `(w, u)`: this set consists of the
pairs `(f, φ) = (F ∘ baseChangeGf, 1_K * F)`, with `F` bi-invariant at `V` and `K` the group of
elements integral at `otherConjugates E V`, and for every such pair and every `j` the pair
`(T_{w,j} f, T_{u,j} φ)` of Hecke operators for left translation again lies in the set. -/
lemma isHeckeStableAt_biInvariantPairs {V : Set (FinPlace E')}
    (hV_inj : InjOn (FinPlace.below E) V)
    (hV_side : ∀ w ∈ FinPlace.below E '' V, star w ∉ FinPlace.below E '' V)
    (hu_conj : u ∈ V.conjClosure)
    (h_onto : Function.Surjective (locMap (algebraMap E E') (Eq.refl (u.below E)))) :
    IsHeckeStableAt (biInvariantPairs E n V) (u.below E) u := by
  rintro _ ⟨F, hF, rfl⟩ hw_split hu j
  -- an element of `localLevel V` is integral at `u`, which lies in `V` or is conjugate to it
  have h_at_u {k : Gf E' n} (hk : k ∈ localLevel n V) : k.atPlace u ∈ localIntGL n u :=
    hu_conj.elim (hk u) fun h_star ↦ atPlace_star_mem_iff.1 (hk _ h_star)
  have hF_sph : F ∈ sphericalAt leftTranslation u := by
    have hF_left (k : Gf E' n) (hk : k ∈ localLevel n V) (g : Gf E' n) : F (k⁻¹ * g) = F g := by
      obtain ⟨hF_k, -⟩ := hF k hk
      simpa [leftTranslation] using congrFun hF_k g
    simp +contextual [hF_left, mem_localLevel, mem_stdLevel_iff, leftTranslation, funext_iff]
  -- `u` is the only place above `w` in `V` or conjugate to a place of `V`
  have h_only (v : FinPlace E') (hv : v ∈ V.conjClosure) (h_below : v.below E = u.below E) :
      v = u := by
    match hv, hu_conj with
    | .inl hv, .inl huV => exact hV_inj hv huV h_below
    | .inr hv, .inr huV =>
      have h_below_star : (star v).below E = (star u).below E := by
        rw [below_star, below_star, h_below]
      exact star_injective (hV_inj hv huV h_below_star)
    | .inl hv, .inr huV =>
      have h_below_star : (star u).below E = star (v.below E) := by rw [below_star, h_below]
      exact absurd ⟨star u, huV, h_below_star⟩ (hV_side _ ⟨v, hv, rfl⟩)
    | .inr hv, .inl huV =>
      have h_below_star : (star v).below E = star (u.below E) := by rw [below_star, h_below]
      exact absurd ⟨star v, hv, h_below_star⟩ (hV_side _ ⟨u, huV, rfl⟩)
  have h_star_mem {v : FinPlace E'} (hv : v ∈ V) : star v ∈ V.conjClosure := by
    have h_star_star : star (star v) ∈ V := by rwa [star_star]
    exact .inr h_star_star
  refine ⟨heckeSplit leftTranslation hu j F, fun k hk ↦ ⟨?_, fun g ↦ ?_⟩, Prod.ext ?_ ?_⟩
  · obtain ⟨hF_left_k, -⟩ := hF k hk
    rw [← heckeSplit_comm_of_atPlace_mem hu j hF_sph (h_at_u hk), hF_left_k]
  · obtain ⟨-, hF_right_k⟩ := hF k hk
    simp [heckeSplit, heckeGL, heckeFun_eq_sum_toFinset, ← mul_assoc, hF_right_k, leftTranslation]
  · -- the other places above `w` and their conjugates lie outside `V`
    have h_other : supportedOn n (FinPlace.below E ⁻¹' {u.below E} \ {u}) ≤ trivialOn n V :=
      supportedOn_le_trivialOn fun v hv ↦
        ⟨fun ⟨h_below, h_ne⟩ ↦ h_ne (h_only v (.inl hv) h_below),
          fun ⟨h_below, h_ne⟩ ↦ h_ne (h_only (star v) (h_star_mem hv) h_below)⟩
    have h_fix (k : Gf E' n) (hk : k ∈ supportedOn n (FinPlace.below E ⁻¹' {u.below E} \ {u})) :
        leftTranslation k F = F := (hF k (trivialOn_le_localLevel (h_other hk))).left
    rw [← heckeSplit_comp_baseChangeGf hu hw_split h_onto hF_sph h_fix]
    simp [heckeSplit, heckeGL, heckeFun_eq_sum_toFinset, leftTranslation, funext_iff]
  · -- translations at `u` are trivial at the other conjugates, so they fix the indicator
    have h_away : supportedOn n {u} ≤ trivialOn n (otherConjugates E V) := by
      refine supportedOn_le_trivialOn ?_
      rintro v ⟨⟨v', hv', h_below⟩, hvV⟩
      -- `u` is the only place above `w` in `V` or conjugate to it, and `v' ∈ V` but `v ∉ V`
      have h_ne : v' ≠ v := by
        rintro rfl
        exact hvV hv'
      constructor
      · intro hv_u
        rw [mem_singleton_iff] at hv_u
        have h_below_u : v'.below E = u.below E := by rw [h_below, hv_u]
        exact h_ne ((h_only v' (.inl hv') h_below_u).trans hv_u.symm)
      · intro hv_u
        rw [mem_singleton_iff] at hv_u
        have h_below_star : (star v').below E = u.below E := by
          rw [← hv_u, below_star, below_star, h_below]
        have h_star_eq : star v' = u := h_only (star v') (h_star_mem hv') h_below_star
        exact h_ne (star_injective (h_star_eq.trans hv_u.symm))
    have h_off (g : GL n (LocField u)) : ofSplitPlace hu g ∈ localLevel n (otherConjugates E V) :=
      trivialOn_le_localLevel (h_away (ofSplitPlace_mem_supportedOn hu g))
    simp [heckeSplit, heckeGL, heckeFun_eq_sum_toFinset, Finset.mul_sum, h_off, leftTranslation,
      funext_iff,
      indicator_subgroup_mul_left]

/-- Let `E'/E` be a step for `μ` (`New.IsStep`: `E'` CM, Galois of prime degree over `E`, with
conditions on `μ`), `σ ≠ 1` in `Gal(E'/E)`, and `S` a set of split places of `E` that are matched
(`μ` trivial on `E_w^×`; places above `w` have residue degree 1 and are moved by `σ`). Then some set
of matching pairs of level `B` above `S` contains the indicator of `B` paired with its composition
with `baseChangeGf`, and is Hecke-stable at each `w ∈ S` and at some place above it. Here `B` is the
group of elements integral at the places above `S` and their conjugates. -/
lemma exists_isHeckeStableMatching {μ : (𝔸f E)ˣ →* ℂˣ} (hσ : σ ≠ 1) [hμ : IsStep E' μ]
    {S : Set (FinPlace E)} (h_split : ∀ w ∈ S, w.IsSplit)
    (h_matched : ∀ w ∈ S, IsMatched E' μ w) :
    ∃ St : Set ((Gf E n → ℂ) × (Gf E' n → ℂ)),
      IsHeckeStableMatching σ μ S (localLevel n (placesAbove E' S)) St := by
  classical
  -- Choose a set `V` with one place of `E'` above each pair `{w, star w}` with `w ∈ S`, and
  -- take the bi-invariant pairs at `V`.
  obtain ⟨V, hV, hV_inj, hV_side, hV_conj⟩ := exists_places_above_one_side (E' := E') h_split
  have h_above : placesAbove E' S = placesAbove E' (FinPlace.below E '' V) :=
    congrArg (preimage (FinPlace.below E)) hV_conj
  -- the indicator function of the level at `V` is bi-invariant at `V`
  have h_ind : IsBiInvariantAt V (indicator (localLevel n V) 1 : Gf E' n → ℂ) := by
    simp +contextual [IsBiInvariantAt, indicator, leftTranslation, funext_iff, mul_mem_cancel_left,
      mul_mem_cancel_right]
  refine ⟨biInvariantPairs E n V, ⟨indicator (localLevel n V) 1, h_ind, ?_⟩,
    fun x hx ↦ ?_, fun w hw ↦ ?_⟩
  · -- a point from `E` that is integral at `V` is integral at all conjugates
    have h_int (g : Gf E n) (hg : baseChangeGf g ∈ localLevel n V) :
        baseChangeGf g ∈ localLevel n (otherConjugates E V) := by
      rintro u ⟨⟨v, hv, h_below⟩, -⟩
      exact atPlace_baseChangeGf_mem_localIntGL h_below (hg v hv)
    rw [h_above]
    ext g
    · simp +contextual [indicator, mem_localLevel_placesAbove_image, ite_and, h_int]
    · simp [indicator, mem_localLevel_placesAbove_image, ite_and]
  · rw [IsMatchingPairAbove, h_above]
    exact isMatchingPairAbove_of_mem_biInvariantPairs hσ (fun v hv ↦ h_matched _ (hV v hv))
      hV_inj hV_side hx
  · obtain ⟨u, rfl, hu_conj⟩ : ∃ u : FinPlace E', u.below E = w ∧ u ∈ V.conjClosure := by
      obtain ⟨v, hv, hvw⟩ | ⟨v, hv, hvw⟩ := hV_conj.le (.inl hw)
      · exact ⟨v, hvw, .inl hv⟩
      · have h_below : (star v).below E = w := by rw [below_star, hvw, star_star]
        have h_star_star : star (star v) ∈ V := by rwa [star_star]
        exact ⟨star v, h_below, .inr h_star_star⟩
    obtain ⟨-, h_over⟩ := h_matched _ hw
    obtain ⟨-, h_moved⟩ := h_over u rfl
    exact ⟨u, rfl, isHeckeStableAt_biInvariantPairs hV_inj hV_side hu_conj
      (locMap_surjective_of_comap_ne h_moved)⟩

end MatchedPlacePairs

end New
