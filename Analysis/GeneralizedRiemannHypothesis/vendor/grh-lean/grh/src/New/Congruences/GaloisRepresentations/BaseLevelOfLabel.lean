import Lib.GaloisRep.TaylorWiles
import New.Congruences.GaloisRepresentations.RowsAndColumnsFromLabels
import New.OneLift.FalseLifts.BottomOfTower

/-!
# Base data whose forms contain those with given labels in a lift setting

Let `O` be a descent pair (`New.DescentPair`): hermitian spaces `W` and `V` with bases `r` and `n`,
with chosen places, twist places, weights and a character. Let `c` be a tuple of labels
(polynomials over the residue fields) at the chosen places, forming a lift setting with a twist `ϑ`
(`New.Selmer.IsLiftSetting`); `typeProjection O c` is the idempotent on forms that cuts out the
labels `c`.

* `New.Selmer.IsFormOfType`, `New.Selmer.IsFormOfType.isRepOfType_normalisedRep`: the eigenforms
  of type `c` with the level and character of `O` off a set of places, and their normalised
  representations as representations of a type.
* `New.Selmer.exists_baseLevel`: base data (`New.Patching.BaseLevel`) whose forms contain the image
  of the idempotent and whose eigensystems have normalised representations that are representations
  of a type with a quadratic relation on inertia, when the modulus of `ϑ` is auxiliary; also,
  `New.Data.chosenGroupOrder` times the idempotent keeps integral forms.
* `New.Selmer.normalisedJumps_eq_range_add_map`: the Hodge–Tate jumps of the normalised
  representations are, when the rank of the larger space is even, `0, …, t - 1` and the
  `(t - 1) / 2 ∓ (λ_c + κ')`, where `t` is the difference of the ranks, `λ` the parameter on the
  smaller space and `-κ'` the weight of the character.

Notions from other files:
* `New.levelSpace`: the vectors `v` of a representation `π` with `π k v = χ k • v` for all `k` in
  the subgroup `K`.
* `New.Gf.componentOn`: keeps the components of an element at the places of `S` and their
  conjugates, and replaces the others by 1.
* `New.DescentPair.columnCount`: the weight datum `(τ, i) ↦ k⁺(τ, i) + k⁻(τ, n − i)` of forms on the
  definite space of rank `n`, with `k⁺`, `k⁻` the two weights of the pair.
* `New.DescentPair.FormV`: the algebraic forms on the definite space of rank `n` with the weight
  `(O.columnCount, O.detExp)`, the level group and the level character `O.levelChar` of the pair
  `O`.
* `New.DescentPair.chosenGLRep`: the action of `∏ GL_r(k_w)`, over the chosen places `w`, on the
  vectors of `π` with the level and character of `O`, twisted by `∏ ψ_w (det g_w)`, where `ψ_w` is
  the character `O.tamePart w` of the residue field `k_w`.
* `New.levelOf`, `New.descentResidueLevel`, `New.DescentPair.levelChar`: the level of `O` is the
  group of integral elements whose reductions at its places lie in `descentResidueLevel`;
  `levelChar` is its character.
* `New.Data.chosenGroupOrder`: the order of a product of groups `GL` over the residue fields of the
  chosen places of `D`; `New.Patching.BaseLevel.ellIntegralForms`: the forms whose values at the
  points integral above `ℓ` are sent to `ℓ`-adic integers by `ιℓ : ℂ ≃ ℚ̄_ℓ`.
* `New.HasProductLabel`: a label of a form at a place, made from a polynomial and characters of
  blocks of given sizes; `New.faithfulChar`: the faithful character by which it is formed.
* `New.Selmer.IsRepOfType`: a conjugate self-dual representation of given jumps and level on which
  inertia at the chosen places acts through the roots of the labels; `New.Selmer.normalisedRep`: the
  twist of a representation by `normalizingAvatar O`; `ϑ.invAvatar`: the `ℓ`-adic avatar of `ϑ⁻¹`
  over `D.E`.
-/

namespace New.Selmer

open Patching Subgroup Representation MonoidAlgebra Gf stdLevel Set Matrix Polynomial Space

variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {P : Parameters} {D : Data P}
  {r n : Type} [Fintype r] [DecidableEq r] [Fintype n]

section

variable {O : DescentPair D.E r n} [DecidableEq n]

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
/-- Let `w = O.chosenPlace i` be a chosen place of the pair `O`, assumed split (`hw`), and write
`ψ_w` for the character `O.tamePart w` of its residue field `k_w`. The map `ofSplitPlace hw` places
`GL_n(E_w)` in the finite adelic group. Let `π` be a representation of that group on a space `S` of
functions, and `u` a vector of the level and character of `O`. Suppose that `π k u` is the right
translate of `f` by `k` for all `k` in `GL_n(E_w)`. Then `f` has a parahoric type at `w`: an
integral `k` whose reduction keeps the span of the indices `O.incl` and acts on it by `g` sends `f`
to `ψ_w⁻¹(det g)` times the image of `u` under `g`, placed at `i`, in the representation
`O.chosenGLRep π`; the one other block (`s := 1`) carries the trivial character. -/
theorem hasParahoricType_chosenGLRep {S : Submodule ℂ (Gf D.E n → WeylIndex n O.columnCount → ℂ)}
    {π : Representation ℂ (Gf D.E n) S}
    {u : levelSpace π (levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl)) O.levelChar}
    {i : O.ChosenIndex} {hw : (O.chosenPlace i).IsSplit}
      {f : Gf D.E n → WeylIndex n O.columnCount → ℂ}
    (h_loc : ∀ k : GL n (LocField (O.chosenPlace i)),
      (π (ofSplitPlace hw k) u.val).val = fun x : Gf D.E n ↦ f (x * ofSplitPlace hw k)) :
    HasParahoricType f hw O.incl (fun a : n ↦ if a ∈ Set.range O.incl then 0 else 1)
      (O.tamePart (O.chosenPlace i))⁻¹ (s := 1) 1 fun g : GL r (ResField (O.chosenPlace i)) ↦
        (O.chosenGLRep π (Pi.mulSingle i g) u).val.val := by
  refine ⟨by simp, fun k g h_parab h_block ↦ ?_⟩
  -- Let `c` be `k` placed at `i`: its reductions are `reduceGL k` at `i` and `1` elsewhere.
  let c : stdLevel D.E n := ⟨ofSplitPlace hw k, by simp⟩
  have h_red (j : O.ChosenIndex ⊕ O.TwistIndex) : stdLevel.reduceAt (O.placeAt j) c =
      Pi.mulSingle (M := fun j ↦ GL n (ResField (O.placeAt j))) (.inl i) (reduceGL k) j :=
    congrFun (reduceFamily_ofSplitPlace (w := O.placeAt) (.inl i) k) j
  -- These reductions are block triangular, with first block `g` at `i` and `1` elsewhere.
  let s : ∀ j : O.ChosenIndex ⊕ O.TwistIndex, GL r (ResField (O.placeAt j)) :=
    Sum.rec (Pi.mulSingle i g) 1
  have h_upper (j : O.ChosenIndex) :
      (stdLevel.reduceAt (O.placeAt (.inl j)) c).val *
          inclMatrix (ResField (O.placeAt (.inl j))) O.incl =
        inclMatrix (ResField (O.placeAt (.inl j))) O.incl * (s (.inl j)).val := by
    rw [h_red]
    obtain rfl | hj := eq_or_ne j i
    · simp only [s, Pi.mulSingle_eq_same]
      rw [← h_block, mul_inclMatrix]
      -- The columns of `reduceGL k` in `O.incl` vanish outside the block `g`, by `h_parab`.
      exact (eq_inclMatrix_mul_iff _).2 fun a ha b ↦ h_parab (by simp [ha])
    · simp [s, hj]
  have h_lower (j : O.TwistIndex) :
      (stdLevel.reduceAt (O.placeAt (.inr j)) c).valᵀ *
          inclMatrix (ResField (O.placeAt (.inr j))) O.incl =
        inclMatrix (ResField (O.placeAt (.inr j))) O.incl * (s (.inr j)).valᵀ := by
    simp [h_red, s, -Sum.elim_inr]
  -- So `c` acts as `chosenGLRep` times `∏ j, ψ⁻¹ (det (s j))`, where only `j = i` contributes.
  have h_act : (O.tamePart (O.chosenPlace i))⁻¹ g.val.det •
      (O.chosenGLRep π (Pi.mulSingle i g) u).val = π c u := by
    rw [← O.smul_chosenGLRep_eq_apply_of_triangular u c s h_upper h_lower]
    simp +contextual [s, Fintype.prod_eq_single i]
  refine (h_loc k).symm.trans ((congrArg Subtype.val h_act).symm.trans ?_)
  simp [MulChar.one_apply, GeneralLinearGroup.det_ne_zero]

/-- Let `v` have the level and character of the pair `O` under `π`, and let
`ψ_i = O.tamePart (O.chosenPlace i)`, a character of the residue field of the `i`-th chosen place.
The element `a` of the group algebra of `O.ChosenGL r = ∏ i, GL_r` of these residue fields acts on
`v` through `O.chosenGLRep π` as the sum over `g` of `a g` times `∏ i, ψ_i (det (g i))` times `π`
of the chosen lift of `diag (g, 1)`. -/
lemma coe_asAlgebraHom_chosenGLRep_apply {W : Type*} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Gf D.E n) W) (a : MonoidAlgebra ℂ (O.ChosenGL r))
    (v : levelSpace π (levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl))
      O.levelChar) :
    ((O.chosenGLRep π).asAlgebraHom a v).val = ∑ g ∈ a.coeff.support, a.coeff g •
        (∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) (g i).val.det) •
          π (liftResidue (firstBlockHom O.toLevelPlaces O.incl g)) v := by
  simp [DescentPair.chosenGLRep, levelRep, asAlgebraHom_def, lift_apply, Finsupp.sum]

open scoped Classical in
/-- An element of the finite adelic group that is supported at the places of `O` and their
conjugates equals its components there (`componentOn`). -/
lemma componentOn_places_eq_self {k : Gf D.E n} (hk : k ∈ supportedOn n O.places) :
    componentOn n O.places.toFinset k = k :=
  Gf.ext (by simp_all)

open scoped Classical in
/-- Let `π` be right translation (`formTranslation`) of forms of weight `(O.columnCount, O.detExp)`
by the components at the places of `O` and their conjugates (`componentOn`, which puts `1` at all
other places). A form `y` of `O` (`O.FormV`: a form of this weight with the level group and
character of `O`), regarded as a form of that weight (`y.toSmoothForm`), has this level and
character also under `π`. The reason is that taking components does not change the reductions at
the places of `O`, on which alone the level group and its character depend. -/
lemma toSmoothForm_mem_levelSpace_componentOn (y : O.FormV) :
    y.toSmoothForm ∈ levelSpace (((stdSpace D.E n).formTranslation (O.columnCount, O.detExp)).comp
        (componentOn n O.places.toFinset))
      (levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl)) O.levelChar := by
  intro k
  let k₀ : stdLevel D.E n :=
    ⟨componentOn n O.places.toFinset k, componentOn_mem_stdLevel (levelOf_le_stdLevel k.property)⟩
  -- It suffices that `k₀` and `k` have the same reduction at each place `O.placeAt j`.
  refine levelSpace_levelOf_apply y.property k₀ _ (funext fun j ↦ ?_)
  have h_eq : atPlace (O.placeAt j) (k₀ : Gf D.E n) = atPlace (O.placeAt j) (k : Gf D.E n) := by
    -- Splitting the range of `O.placeAt` would hide that `O.placeAt j` lies in it.
    simp [k₀, -Sum.elim_range]
  exact (stdLevel.reduceAt _).div_mem_ker_iff.1 (reduceAt_eq_one_of_atPlace (by simp [h_eq]))

open scoped Classical in
/-- Let `ψ_i = O.tamePart (O.chosenPlace i)`, a character of the residue field of the `i`-th chosen
place. For a form `y` of `O`, the projection `typeProjection O c y` is the sum over `g` of the
coefficient at `g` of the idempotent `tupleIdem r c` of the labels `c`, times
`∏ i, ψ_i (det (g i))`, times the right translate of `y` by the components at the places of `O` of
the chosen lift of `diag (g, 1)`. -/
lemma toSmoothForm_typeProjection (c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X])
    (y : O.FormV) : (typeProjection O c y).toSmoothForm =
      ∑ g ∈ (tupleIdem r c).coeff.support, (tupleIdem r c).coeff g •
        (∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) (g i).val.det) •
          (stdSpace D.E n).formTranslation (O.columnCount, O.detExp)
            (componentOn n O.places.toFinset
            (liftResidue (firstBlockHom O.toLevelPlaces O.incl g))) y.toSmoothForm := by
  -- The action of a single `g` on forms, by the definition of `O.formAction`.
  have h_action (g : O.ChosenGL r) : (O.formAction g y).toSmoothForm =
      (∏ i : O.ChosenIndex, O.tamePart (O.chosenPlace i) (g i).val.det) •
        (stdSpace D.E n).formTranslation (O.columnCount, O.detExp)
          (liftResidue (firstBlockHom O.toLevelPlaces O.incl g)) y.toSmoothForm := rfl
  -- The chosen lift is supported at the places of `O`, so it equals its components there.
  simp only [componentOn_places_eq_self, liftResidue_mem_supportedOn, ← h_action]
  simp [typeProjection, DescentPair.groupAlgAction, asAlgebraHom_def, lift_apply, Finsupp.sum]

/-- Let the labels `c` at the chosen places of `O` form a lift setting with the twist `ϑ`. Let the
form `y` of `O` be integral above `ℓ`: `ιℓ` sends its values at the points integral above `ℓ` to
`ℓ`-adic integers. Then so is `D.chosenGroupOrder` times the projection `typeProjection O c y` of
`y` by the idempotent of `c`. -/
lemma chosenGroupOrder_nsmul_typeProjection_mem_ellIntegralForms {ϑ : D.Twist}
    {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]} (h_lift : IsLiftSetting O c ϑ)
    (y : O.FormV) (hy : y.toSmoothForm ∈ BaseLevel.ellIntegralForms) :
    D.chosenGroupOrder • (typeProjection O c y).toSmoothForm ∈ BaseLevel.ellIntegralForms := by
  classical
  -- `D.chosenGroupOrder` clears the denominator `Nat.card (O.ChosenGL r)` of the idempotent. Each
  -- remaining term is a natural number times an algebraic integer, a root of unity and a value of
  -- `y` at a point that is integral above `ℓ`.
  intro x hx i
  obtain ⟨t, ht⟩ : Nat.card (O.ChosenGL r) ∣ D.chosenGroupOrder := by
    rw [h_lift.toLevelPlaces_eq]
    exact D.card_GL_dvd_chosenGroupOrder (h_lift.rank_le.left.trans D.nat_le_of_hasLogBound)
  have h_coef (g : O.ChosenGL r) : ‖ιℓ (Nat.card (O.ChosenGL r) * (tupleIdem r c).coeff g)‖ ≤ 1 :=
    norm_le_one_of_isIntegral ιℓ.toRingHom
      ((isCentralProj_tupleIdem c).isChar_card_mul_coeff.isIntegral g)
  have h_root (g : O.ChosenGL r) : ‖ιℓ (∏ j, O.tamePart (O.chosenPlace j) (g j).val.det)‖ ≤ 1 :=
    (ιℓ.toRingHom.isOfFinOrder (O.isOfFinOrder_prod_tamePart_det g)).norm_eq_one.le
  -- `val g` is the value at `x`, `i` of the translate of `y` by the components of `g`.
  let val (g : stdLevel D.E n) : ℂ := ((stdSpace D.E n).formTranslation (O.columnCount, O.detExp)
    (componentOn n O.places.toFinset g) y.toSmoothForm).val x i
  have h_val (g : stdLevel D.E n) : ‖ιℓ (val g)‖ ≤ 1 :=
    hy _ (mul_mem hx (stdLevel_le_localLevel (componentOn_mem_stdLevel g.property))) i
  have h_sum : ιℓ ((D.chosenGroupOrder • (typeProjection O c y).toSmoothForm).val x i) =
      ∑ g ∈ (tupleIdem r c).coeff.support,
        t * (ιℓ (Nat.card (O.ChosenGL r) * (tupleIdem r c).coeff g) *
          (ιℓ (∏ j : O.ChosenIndex, O.tamePart (O.chosenPlace j) (g j).val.det) *
            ιℓ (val (liftResidue (firstBlockHom O.toLevelPlaces O.incl g))))) := by
    simp [val, toSmoothForm_typeProjection, ht, Finset.mul_sum, mul_assoc, mul_left_comm _ (t : ℂ)]
  rw [h_sum]
  exact NormedField.valuation.integer.sum_mem fun g _ ↦
    mul_mem (natCast_mem _ t) (mul_mem (h_coef g) (mul_mem (h_root g) (h_val _)))

omit [DecidableEq n] [PadicIso ℓ] in
/-- Let the labels `c` form a lift setting for `O` and `ϑ`. Let `ϑ.Q` be auxiliary: its places have
prime norm, neither they nor their conjugates are bad, and the conjugates are not in `ϑ.Q`. Let `U`
be a family of places that are not bad. Suppose that neither `v` nor its conjugate is a chosen
place. Suppose also that `v` lies above `ℓ` or in `placesAboveM D`, or that neither `v` nor its
conjugate is in `ϑ.Q` or `range U`. Then `v` and its conjugate avoid `range U` and the places of
`O`. -/
lemma notMem_and_star_notMem_range_union_places {ϑ : D.Twist}
    {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]} (h_lift : IsLiftSetting O c ϑ)
    (hQ : IsAuxiliary (badPlaces D ℓ) ϑ.Q) {K : Type} {U : K → FinPlace D.E}
    (hU : ∀ k : K, U k ∉ badPlaces D ℓ) {v : FinPlace D.E}
    (h_exc : v ∉ ((ϑ.Q : Set (FinPlace D.E)).conjClosure ∪ (range U).conjClosure) \
      (placesDividing D.E ℓ ∪ placesAboveM D))
    (h_chosen : v ∉ (range O.chosenPlace).conjClosure) :
    v ∉ range U ∪ O.places ∧ star v ∉ range U ∪ O.places := by
  have h_range : range O.twistPlace = ϑ.Q := by
    rw [h_lift.toLevelPlaces_eq]
    exact Subtype.range_coe
  have h_places : O.places = range O.chosenPlace ∪ range O.twistPlace := Sum.elim_range ..
  -- `ϑ.Q` and `range U` avoid the bad places, so `v` and its conjugate avoid both.
  have h_off : v ∉ (ϑ.Q : Set (FinPlace D.E)).conjClosure ∪ (range U).conjClosure := by
    intro h_mem
    -- The places above `ℓ` or a level prime are bad, and they are stable under conjugation.
    have h_above : v ∈ placesDividing D.E ℓ ∪ placesAboveM D := by grind
    have hv_bad : v ∈ badPlaces D ℓ := placesDividing_union_subset_badPlaces D ℓ h_above
    have h_star_bad : star v ∈ badPlaces D ℓ := placesDividing_union_subset_badPlaces D ℓ
      (h_above.imp star_mem_placesDividing.2 star_mem_placesAboveM.2)
    obtain (hv_mem | h_star_mem) | ⟨k, rfl⟩ | ⟨k, hk⟩ := h_mem
    · exact (hQ v hv_mem).left hv_bad
    · exact (hQ (star v) h_star_mem).left h_star_bad
    · exact hU k hv_bad
    · exact hU k (by rwa [hk])
  simp only [h_places, h_range, mem_union, mem_preimage, not_or] at h_off h_chosen ⊢
  tauto

/-- The jumps of a normalised representation (`normalisedRep`) attached to a form of weight
`(O.columnCount, O.detExp)`: the jumps of the weight minus the infinity type of the algebraic Hecke
character whose `ℓ`-adic avatar is `normalizingAvatar O`. -/
noncomputable def normalisedJumps (O : DescentPair D.E r n) (σ : D.E →+* ℂ) : Multiset ℤ :=
  (jumps (O.columnCount, O.detExp) (Fintype.card n) σ).map fun u : ℤ ↦
    u + -((AutChar.HasWeight.inv (μ := O.charW)).toAlgebraic (-Fintype.card r) 0).val.2.toAdd σ

/-- Let the labels `c` form a lift setting for `O` and `ϑ`, and let `R` be attached to an eigenform
`f` of weight `(O.columnCount, O.detExp)`. Suppose that at the chosen places `f` has the labels
`scaledTypePoly O c i`, completed by the trivial character on further blocks of sizes `t`
(`HasProductLabel`). Suppose also that `f` is spherical at the places that are off `S`, above `ℓ` or
in `placesAboveM D` (above `p₀` or `p₁`), except the chosen places and their conjugates.

Then `normalisedRep O R`, the twist of `R` by `normalizingAvatar O`, satisfies `IsRepOfType`: it has
the jumps `normalisedJumps O` and the properties of a conjugate self-dual representation of level
`S`, and inertia at the chosen places acts through the roots of
`scaledTypePoly O c i * (X - 1) ^ t'`, with `t' = O.rankDiff = card n - card r`. -/
lemma isRepOfType_normalisedRep [Nonempty n] {ϑ : D.Twist}
    {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]} (h_lift : IsLiftSetting O c ϑ)
    {f : (stdSpace D.E n).forms (O.columnCount, O.detExp)} {H : FinPlace D.E → ℂ[X]}
      {R : GalRep ℓ D.E n}
    (h_eig : IsEigenform f.val H) (h_att : GaloisRep.Attached H R) {S : Set (FinPlace D.E)}
    (h_sph : ∀ v ∉ S \ (placesDividing D.E ℓ ∪ placesAboveM D),
      v ∉ (range O.chosenPlace).conjClosure →
        f.val ∈ sphericalAt (rightRegular ℂ (Gf D.E n) (WeylIndex n O.columnCount → ℂ)) v)
    {s : ℕ} {t : Fin s → ℕ} (h_lab : ∀ i : O.ChosenIndex,
      HasProductLabel f.val (O.isConjApart_chosenPlace.star_ne i i)
        (faithfulChar (ResField (O.chosenPlace i))) (Fintype.card r) (scaledTypePoly O c i) 1 t) :
    IsRepOfType O O.rankDiff (normalisedJumps O)
      (fun i : O.ChosenIndex ↦ scaledTypePoly O c i * (X - 1) ^ O.rankDiff) S
      (normalisedRep O R) := by
  have h_type_R : IsRepOfType O (Fintype.card n) (jumps (O.columnCount, O.detExp) (Fintype.card n))
      (fun i : O.ChosenIndex ↦ scaledTypePoly O c i * (X - 1) ^ O.rankDiff) S R :=
    isRepOfType_of_hasProductLabel h_lift f.property h_eig h_att h_sph h_lab
  -- `O.rankDiff` is `card n - card r`, and `card r < card n`.
  have h_rank : ((O.rankDiff - 1 : ℕ) : ℤ) + (2 * 0 - -Fintype.card r) =
      (Fintype.card n - 1 : ℕ) := by grind only [O.rank_lt]
  -- The tame part of the twist is trivial, so the roots of the labels are not scaled.
  unfold normalisedJumps normalisedRep normalizingAvatar
  simpa only [inv_one, Pi.one_apply, map_one, Units.val_one, scaleRoots_one] using
    h_type_R.twist_avatar (.inv (μ := O.charW)) (-Fintype.card r) 0 h_rank h_lift (by simp)

end

/-- The pair `O` has hermitian spaces `W` and `V` with bases indexed by `r` and `n`.
`normalisedJumps O` are the jumps of the weight `(O.columnCount, O.detExp)` of forms on `V`, shifted
by minus the infinity type of the algebraic Hecke character whose `ℓ`-adic avatar is
`normalizingAvatar O`. They are computed here from the parameter of that weight. Let `a p` be entry
`p` of twice its Harish-Chandra parameter at the place of the complex embedding `σ` (`hcParameter`).
Let `r₋ = Exchange.negCount O.signs` be the number of minus signs among the signs `O.signs` of the
hermitian form of `W`. Let `t = O.rankDiff = card n - card r`. The jumps at `σ` are the
`(t - 1 ∓ (a p - 2 r₋ + card r)) / 2` for `p < card n`. The upper sign is taken when `σ` is on the
CM type (`cmSign σ = 1`), and the lower sign otherwise; the division is exact. -/
lemma normalisedJumps_eq_map_hcParameter (O : DescentPair D.E r n) (σ : D.E →+* ℂ) :
    normalisedJumps O σ = (Multiset.range (Fintype.card n)).map fun p : ℕ ↦
        ((O.rankDiff : ℤ) - 1 - cmSign σ *
          (hcParameter O.columnCount O.detExp (Fintype.card n) (NumberField.InfinitePlace.mk σ) p -
            2 * Exchange.negCount O.signs + Fintype.card r)) / 2 := by
  classical
  have h_lt : Fintype.card r < Fintype.card n := O.rank_lt
  set v : NumberField.InfinitePlace D.E := NumberField.InfinitePlace.mk σ with hv
  -- The normalising character has exponent `card r - r₋` on the CM type and `r₋` off it.
  have h_type :
      ((AutChar.HasWeight.inv (μ := O.charW)).toAlgebraic (-Fintype.card r) 0).val.2.toAdd σ =
        if σ = Φ v then (Fintype.card r : ℤ) - Exchange.negCount O.signs
        else Exchange.negCount O.signs := by
    simp only [AutChar.HasWeight.toAlgebraic, IsHeckeOfType.toAlgebraic, toAdd_ofAdd, Pi.neg_apply]
    split_ifs <;> omega
  rw [normalisedJumps, jumps, Multiset.map_map, h_type]
  refine Multiset.map_congr rfl fun p _ ↦ ?_
  -- Entry `p` of the parameter is `2 μ_p + card n - 1 - 2 p`, with `μ` the highest weight.
  have h_param : hcParameter O.columnCount O.detExp (Fintype.card n) v p =
      2 * (O.detExp v + (∑ h ∈ Finset.Ioo p (Fintype.card n), O.columnCount v h : ℕ)) +
        Fintype.card n - 1 - 2 * p := by simp only [hcParameter, diagramWeight_apply]
  simp only [Function.comp_apply, h_param, cmSign, DescentPair.rankDiff, apply_ite Units.val,
    Units.val_neg, Units.val_one, ← hv]
  split_ifs <;> omega

/-- The Hodge–Tate jumps `normalisedJumps O` of the normalised representations, written out. The
pair `O` has hermitian spaces `W` and `V` with bases indexed by `r` and `n`; suppose that `card n`,
the rank of `V`, is even. Let `l = 2 λ` be the doubled parameter on `W` that fits `O`
(`DescentPair.FitsParams`), let `-κ'` be the weight `O.weight` of the character of `O`, and let
`t = O.rankDiff = card n - card r`. At a complex embedding `σ` with place `v` the jumps are
`0, 1, …, t - 1` and the `(t - 1) / 2 ∓ (λ v c + κ' v)` over the indices `c : r`, with the upper
sign on the CM type (`cmSign σ = 1`); the division in the statement is exact. -/
theorem normalisedJumps_eq_range_add_map (O : DescentPair D.E r n) (h_even : Even (Fintype.card n))
    {l : NumberField.InfinitePlace D.E → r → ℤ} (h_fits : O.FitsParams l) (σ : D.E →+* ℂ) :
    normalisedJumps O σ = (Multiset.range O.rankDiff).map (fun b : ℕ ↦ (b : ℤ)) +
        Finset.univ.val.map fun c : r ↦
          ((O.rankDiff : ℤ) - 1 - cmSign σ * (l (NumberField.InfinitePlace.mk σ) c -
            2 * O.weight (NumberField.InfinitePlace.mk σ))) / 2 := by
  -- The jumps are distinct and both sides have `card n` members, so an inclusion suffices.
  have h_lt : Fintype.card r < Fintype.card n := O.rank_lt
  have h_nodup : (normalisedJumps O σ).Nodup :=
    (Weight.nodup_jumps (O.columnCount, O.detExp) (Fintype.card n) σ).map (add_left_injective _)
  refine Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset h_nodup).2 fun u hu ↦ ?_) ?_
  · rw [normalisedJumps_eq_map_hcParameter] at hu
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hu
    set v : NumberField.InfinitePlace D.E := NumberField.InfinitePlace.mk σ
    set s : ℤ := hcParameter O.columnCount O.detExp (Fintype.card n) v p -
      2 * Exchange.negCount O.signs + Fintype.card r with hs
    -- By the block rule, `s` is a shifted entry of `l` or a member of the doubled block `[t]`.
    have h_rule : s ∈ Finset.univ.image
          (shiftedEntry ((Fintype.card n / 2 : ℕ) + O.weight v) (Fintype.card n) (l v)) ∪
        doubledBlock (Fintype.card n - Fintype.card r) := by
      rw [← (h_fits.paramsCorrespond v).entries_of_le h_lt.le]
      exact Finset.mem_image.2 ⟨(Fintype.equivFin n).symm ⟨p, Multiset.mem_range.1 hp⟩,
        Finset.mem_univ _, by simp [shiftedEntry, DescentPair.paramV, hs]⟩
    simp only [Multiset.mem_add, Multiset.mem_map, Multiset.mem_range]
    obtain h_entry | h_block := Finset.mem_union.1 h_rule
    · obtain ⟨c, -, hc⟩ := Finset.mem_image.1 h_entry
      have h_shift : s = l v c - 2 * O.weight v := by grind [shiftedEntry]
      exact .inr ⟨c, Finset.mem_univ_val c, by rw [h_shift]⟩
    · -- The member `t - 1 - 2 b` of the block gives the jump `b`, or `t - 1 - b` off the CM type.
      obtain ⟨b, hb, h_eq⟩ := Finset.mem_image.1 h_block
      rw [Finset.mem_range] at hb
      simp only [← h_eq, DescentPair.rankDiff]
      obtain hσ | hσ := Int.units_eq_one_or (cmSign σ) <;>
        simp only [hσ, Units.val_neg, Units.val_one]
      · exact .inl ⟨b, hb, by omega⟩
      · exact .inl ⟨_, Nat.sub_one_sub_lt hb, by omega⟩
  · simp [normalisedJumps, jumps, DescentPair.rankDiff, h_lt.le]

variable {O : DescentPair D.E r n} [DecidableEq n]

/-- If `π` agrees with the translation of forms on the elements supported at the places of `O`, then
it does so on the local group at each such place. -/
lemma apply_ofSplitPlace_eq_formTranslation
    {π : Representation ℂ (Gf D.E n) ((stdSpace D.E n).forms (O.columnCount, O.detExp))}
    (hπ : ∀ k ∈ supportedOn n O.places, π k = (stdSpace D.E n).formTranslation
      (O.columnCount, O.detExp) k)
    (j : O.ChosenIndex ⊕ O.TwistIndex) (k : GL n (LocField (O.placeAt j))) :
    π (ofSplitPlace (O.apart.star_ne j j) k) =
      (stdSpace D.E n).formTranslation (O.columnCount, O.detExp)
        (ofSplitPlace (O.apart.star_ne j j) k) :=
  hπ _ (supportedOn_mono (by simp [-Sum.elim_range]) (ofSplitPlace_mem_supportedOn _ k))

open scoped Classical in
/-- Let the labels `c` form a lift setting for `O` and `ϑ`. Let `π` be a representation on forms of
weight `(O.columnCount, O.detExp)` that agrees with right translation (`formTranslation`) on the
elements supported at the places of `O`, and let `u` have the level and character of `O` under `π`.
Suppose that the idempotent `tupleIdem r c` of the labels does not kill `u`. Then at each chosen
place `w = O.chosenPlace i`, which is not its own conjugate, the form `u` has a label with two
blocks. The first block has size `card r` and carries the class function of `scaledTypePoly O c i`,
formed with the injective character `faithfulChar k_w` of the algebraic closure of the residue field
`k_w`. The second block carries the trivial character `1`; its size, the last argument, is the
number of indices outside `range O.incl`. -/
lemma hasProductLabel_of_tupleIdem_apply_ne_zero
    {π : Representation ℂ (Gf D.E n) ((stdSpace D.E n).forms (O.columnCount, O.detExp))}
      {ϑ : D.Twist}
    {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]} (h_lift : IsLiftSetting O c ϑ)
    (hπ : ∀ k ∈ supportedOn n O.places, π k = (stdSpace D.E n).formTranslation
      (O.columnCount, O.detExp) k)
    {u : levelSpace π (levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl)) O.levelChar}
    (hu : (O.chosenGLRep π).asAlgebraHom (tupleIdem r c) u ≠ 0) (i : O.ChosenIndex) :
    HasProductLabel u.val.val (O.isConjApart_chosenPlace.star_ne i i)
      (faithfulChar (ResField (O.chosenPlace i))) (Fintype.card r) (scaledTypePoly O c i) 1
      fun l : Fin 1 ↦
        Fintype.card {a : n // (if a ∈ range O.incl then 0 else 1 : Fin 2) = l.succ} := by
  have hw : (O.placeAt (.inl i)).IsSplit := O.apart.star_ne (.inl i) (.inl i)
  have h_loc (k : GL n (LocField (O.chosenPlace i))) : (π (ofSplitPlace hw k) u.val).val =
      rightRegular ℂ (Gf D.E n) (WeylIndex n O.columnCount → ℂ) (ofSplitPlace hw k) u.val.val :=
    congrArg Subtype.val
      (LinearMap.congr_fun (apply_ofSplitPlace_eq_formTranslation hπ (.inl i) k) u.val)
  -- If the factor at `i` of the idempotent killed `u`, so would the whole idempotent.
  refine HasParahoricType.hasProductLabel ((forms _ _).subtype.domRestrict _) (by simp)
    (fun h_zero ↦ hu (piTensorElem_apply_eq_zero i h_zero)) (hasParahoricType_chosenGLRep h_loc)
    (Function.injective_of_subsingleton _) fun _ ↦ ?_
  -- `charName` sends the trivial character to `1`, which is not a root of the scaled type
  -- polynomial.
  simpa [scaledTypePoly] using h_lift.not_isRoot_scaledTypePoly i

/-- Let `π` be a representation on forms of weight `(O.columnCount, O.detExp)` that agrees with
right translation on the elements supported at the places of `O`, and let `u` have the level and
character of `O` under `π`. Let `w = O.twistPlace i` be one of the twist places of the pair, and
`ψ_w = O.tamePart w`, a character of its residue field. Then `u` satisfies
`New.Selmer.HasTwistParahoricType` at `i`: an integral matrix at `w` whose reduction keeps the span
of the indices outside `range O.incl` multiplies `u` by `ψ_w⁻¹` of the determinant of the block of
that reduction on `range O.incl`. -/
lemma hasTwistParahoricType_levelSpace
    {π : Representation ℂ (Gf D.E n) ((stdSpace D.E n).forms (O.columnCount, O.detExp))}
    (hπ : ∀ k ∈ supportedOn n O.places, π k = (stdSpace D.E n).formTranslation
      (O.columnCount, O.detExp) k)
    (u : levelSpace π (levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl)) O.levelChar)
    (i : O.TwistIndex) : HasTwistParahoricType O u.val.val i := by
  classical
  have hw : (O.placeAt (.inr i)).IsSplit := O.apart.star_ne (.inr i) (.inr i)
  let β : n → Fin 3 := fun a ↦ if a ∈ range O.incl then 2 else 1
  -- The twist place is `O.placeAt (.inr i)`.
  change HasParahoricType u.val.val hw (ρ := Empty) .ofIsEmpty β 1
    ![1, (O.tamePart (O.placeAt (.inr i)))⁻¹] fun _ : GL Empty (ResField (O.placeAt (.inr i))) ↦
      u.val.val
  refine ⟨by simp [β, ite_eq_iff], fun k _ hk _ ↦ ?_⟩
  -- The reduction of `k` lies in `descentResidueLevel`, so `k` acts by the value of
  -- `O.residueLevelChar`.
  have hk_mem : Pi.mulSingle (.inr i) (reduceGL k) ∈ descentResidueLevel O.toLevelPlaces O.incl :=
    (mulSingle_mem_pi ..).2 fun _ ↦
      (mem_rangeParabolic_iff _).2 fun a b hb ↦ hk (by simp_all [β])
  -- Only the place `i` contributes to the product that defines `O.residueLevelChar`.
  have h_char : O.residueLevelChar ⟨Pi.mulSingle (.inr i) (reduceGL k), hk_mem⟩ =
      (O.tamePart (O.placeAt (.inr i)))⁻¹ ((reduceGL k).val.submatrix O.incl O.incl).det := by
    refine (Fintype.prod_eq_single i fun j hj ↦ ?_).trans (by simp [-Sum.elim_inr])
    simp [Pi.mulSingle_eq_of_ne (Sum.inr_injective.ne hj), -Sum.elim_inr]
  have h_act : π (ofSplitPlace hw k.val) u.val =
      O.residueLevelChar ⟨Pi.mulSingle (.inr i) (reduceGL k), hk_mem⟩ • u.val :=
    levelSpace_levelOf_apply u.property _ ⟨_, hk_mem⟩
      (reduceFamily_ofSplitPlace (w := O.placeAt) (.inr i) k)
  rw [apply_ofSplitPlace_eq_formTranslation hπ, h_char] at h_act
  refine (congrArg Subtype.val h_act).trans ?_
  -- Block `2` of `reduceGL k` is the block on the range of `O.incl`, up to a renumbering.
  have h_det : ((reduceGL k).val.submatrix O.incl O.incl).det =
      (blockHom β 2 ⟨reduceGL k, hk⟩).val.det :=
    det_submatrix_equiv_self (O.incl.toEquivRange.trans (.subtypeEquivProp (by simp [β])))
      (blockHom β 2 ⟨reduceGL k, hk⟩).val
  simp [h_det, MulChar.one_apply, GeneralLinearGroup.det_ne_zero, -Sum.elim_inr]

open scoped Classical in
/-- Let `B` be base data at the places of `O`. The maximal level (`levelOf` of the empty family),
acting through its components off these places and their conjugates (`B.repOff`), fixes every form
of `O`. -/
lemma toSmoothForm_mem_levelSpace_repOff {m : ℕ}
    (B : BaseLevel (stdSpace D.E n) (O.columnCount, O.detExp) m)
    (hB : B.places = O.places.toFinset) (y : O.FormV) :
    y.toSmoothForm ∈ levelSpace B.repOff (levelOf (![] : Fin 0 → FinPlace D.E) ⊥) 1 := by
  intro k
  -- These components lie in the maximal level and are trivial at the places of `O`.
  have h_triv : componentOn n (Set.conjClosure B.places)ᶜ k ∈ trivialOn n (range O.placeAt) := by
    simp_all [-Sum.elim_range]
  rw [MonoidHom.one_apply, one_smul]
  exact y.algFormRep_eq_self_of_mem
    (inf_trivialOn_le_levelOf ⟨componentOn_mem_stdLevel (levelOf_le_stdLevel k.property), h_triv⟩)

/-- Let `T` commute with `π k` for all `k` in the maximal level. Then `T` keeps the vectors with the
level and character of `O` under `π`, and commutes there with the action of each element `a` of the
group algebra of `O.ChosenGL r`. -/
lemma exists_mem_levelSpace_chosenGLRep_map_eq {W : Type*} [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (Gf D.E n) W} {T : Module.End ℂ W}
    (hT : ∀ k : stdLevel D.E n, Commute (π k) T) (a : MonoidAlgebra ℂ (O.ChosenGL r))
    (v : levelSpace π (levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl))
      O.levelChar) :
    ∃ hTv : T v ∈ levelSpace π (levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl))
      O.levelChar,
      ((O.chosenGLRep π).asAlgebraHom a ⟨T v, hTv⟩).val =
        T ((O.chosenGLRep π).asAlgebraHom a v) := by
  refine ⟨map_mem_levelSpace_of_commute v.property fun k ↦ hT ⟨k, levelOf_le_stdLevel k.property⟩,
    ?_⟩
  have h_comm (k : stdLevel D.E n) : π k (T v) = T (π k v) := LinearMap.congr_fun (hT k).eq v
  simp [coe_asAlgebraHom_chosenGLRep_apply, h_comm]

open scoped Classical in
variable (O) in
/-- Right translation of forms of weight `(O.columnCount, O.detExp)` by the components of an element
at the places of `O` and their conjugates (`componentOn`, which puts `1` at all other places). -/
noncomputable abbrev translationAtPlaces :
    Representation ℂ (Gf D.E n) ((stdSpace D.E n).forms (O.columnCount, O.detExp)) :=
  ((stdSpace D.E n).formTranslation (O.columnCount, O.detExp)).comp
    (componentOn n O.places.toFinset)

open scoped Classical in
variable (O) in
/-- A `(c, S)`-form, for labels `c` at the chosen places of the descent pair `O` and a set `S` of
places: an eigenform `f` on the larger space of `O`, of the weight `(O.columnCount, O.detExp)` of
the pair and of type `c`, with the level and character of the forms of `O` off `S` and its
conjugate, and with any level there. The level of `O` is maximal off the places of `O` and their
conjugates; `S` is meant to avoid these. `H` gives the Hecke polynomials of `f`. -/
structure IsFormOfType (c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X])
    (S : Set (FinPlace D.E)) (f : (stdSpace D.E n).forms (O.columnCount, O.detExp))
    (H : FinPlace D.E → ℂ[X]) : Prop where
  /-- The form `f` is a nonzero eigenform with Hecke polynomials `H` (`IsEigenform`). -/
  isEigenform : IsEigenform f.val H
  /-- At the places of `O`, the form `f` has the level and character of `O`. -/
  mem_levelSpace : f ∈ levelSpace (translationAtPlaces O)
    (levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl)) O.levelChar
  /-- The form `f` is of type `c`: the idempotent `tupleIdem r c` of the labels fixes it, for the
  action `O.chosenGLRep` of `∏ GL_r(k_w)` over the chosen places `w`. -/
  tupleIdem_apply :
    (O.chosenGLRep (translationAtPlaces O)).asAlgebraHom (tupleIdem r c) ⟨f, mem_levelSpace⟩ =
      ⟨f, mem_levelSpace⟩
  /-- The form `f` has maximal level at each place `v` such that `v` and its conjugate avoid `S`
  and the places of `O`. -/
  mem_sphericalAt (v : FinPlace D.E) (hv : v ∉ S ∪ O.places) (hv_star : star v ∉ S ∪ O.places) :
    f.val ∈ sphericalAt (rightRegular ℂ (Gf D.E n) (WeylIndex n O.columnCount → ℂ)) v

/-- Let the labels `c` form a lift setting for `O` and the twist `ϑ` (`IsLiftSetting`), let the
modulus `ϑ.Q` be auxiliary (`IsAuxiliary`), and let `S` be a set of places outside `badPlaces D ℓ`,
the places dividing `ℓ p₀ p₁ N`. Let `f` be a `(c, S)`-form (`IsFormOfType`) and `R` attached to
its Hecke polynomials. Then the normalised representation `normalisedRep O R` is a representation
of a type (`IsRepOfType`): it is conjugate self-dual with jumps `normalisedJumps O` and level `ϑ.Q`,
`S` and their conjugates, and inertia at the chosen places acts through the roots of
`scaledTypePoly O c i * (X - 1) ^ O.rankDiff`. -/
theorem IsFormOfType.isRepOfType_normalisedRep [Nonempty n] {ϑ : D.Twist}
    {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]} {S : Set (FinPlace D.E)}
    {f : (stdSpace D.E n).forms (O.columnCount, O.detExp)} {H : FinPlace D.E → ℂ[X]}
    (hf : IsFormOfType O c S f H) (h_lift : IsLiftSetting O c ϑ)
    (hQ : IsAuxiliary (badPlaces D ℓ) ϑ.Q) (hS : ∀ v ∈ S, v ∉ badPlaces D ℓ)
    {R : GalRep ℓ D.E n} (h_att : GaloisRep.Attached H R) :
    IsRepOfType O O.rankDiff (normalisedJumps O)
      (fun i : O.ChosenIndex ↦ scaledTypePoly O c i * (X - 1) ^ O.rankDiff)
      (Set.conjClosure ϑ.Q ∪ S.conjClosure) (normalisedRep O R) := by
  classical
  have h_transl (k : Gf D.E n) (hk : k ∈ supportedOn n O.places) : translationAtPlaces O k =
      (stdSpace D.E n).formTranslation (O.columnCount, O.detExp) k :=
    congrArg (formTranslation _ _) (componentOn_places_eq_self hk)
  -- The idempotent fixes `f ≠ 0`, so it does not kill `f`, and `f` has the labels made from `c`.
  have h_ne : (O.chosenGLRep (translationAtPlaces O)).asAlgebraHom (tupleIdem r c)
      ⟨f, hf.mem_levelSpace⟩ ≠ 0 := by
    simpa [hf.tupleIdem_apply] using hf.isEigenform.left
  refine Selmer.isRepOfType_normalisedRep h_lift hf.isEigenform h_att
    (fun v h_exc h_chosen ↦ ?_) (hasProductLabel_of_tupleIdem_apply_ne_zero h_lift h_transl h_ne)
  -- A place neither chosen nor exceptional avoids `S` and `O.places`, as does its conjugate.
  obtain ⟨hv, hv_star⟩ : v ∉ S ∪ O.places ∧ star v ∉ S ∪ O.places := by
    simpa only [Subtype.range_coe] using notMem_and_star_notMem_range_union_places h_lift hQ
      (U := (Subtype.val : S → FinPlace D.E)) (fun k ↦ hS k k.property)
      (by rwa [Subtype.range_coe]) h_chosen
  exact hf.mem_sphericalAt v hv hv_star

/-- Fix a prime `ℓ` with an isomorphism `ιℓ : ℂ ≃ ℚ̄_ℓ`, data `D` (among them a CM field `D.E`, two
primes `p₀`, `p₁` given by `D.levelPrime`, and a level `N = D.N`), and a descent pair `O`: hermitian
spaces with bases `r` and `n`, `card r < card n`, with chosen and twist places, weights and a
character. The weight `(O.columnCount, O.detExp)` of its forms on the larger space is given by
column numbers and a power of the determinant. Let `c` be labels at the chosen places that form a
lift setting with the twist `ϑ`. Let `ϑ.Q` be auxiliary: its places have prime norm, neither they
nor their conjugates divide `ℓ p₀ p₁ N` (`badPlaces D ℓ`), and the conjugates are not in `ϑ.Q`.

Then there are jumps `J` and base data `B` of that weight with three properties.
* (a) The projections `typeProjection O c y` of forms `y` of `O` by the idempotent of the labels `c`
  are forms of `B` with no extra level.
* (b) If `y` is integral above `ℓ`, so is `D.chosenGroupOrder • typeProjection O c y`.
* (c) Let `u` be a finite family of places outside `badPlaces D ℓ`, let `x` be an eigensystem of `B`
  of level `u`, and `R = normalisedRep O x.galRep` its representation twisted by
  `normalizingAvatar O`, the avatar of the inverse of the character of `O` with weight `-card r`.
  Then `R` satisfies `IsRepOfType` with jumps `J`, the level being `ϑ.Q`, `range u` and their
  conjugates: it is conjugate self-dual up to twist, has the local properties of
  `IsConjSelfDualOfLevel` off the level, and inertia at the chosen places acts through the roots of
  `scaledTypePoly O c i` (`c i` with roots scaled according to `(O.tamePart _)⁻¹`) times
  `(X - 1) ^ O.rankDiff`. Each `g` in the inertia above `ϑ.Q` and its conjugate satisfies
  `(R g - ϑ.invAvatar g) (R g - 1) = 0`. -/
lemma exists_baseLevel [Nonempty n] {ϑ : D.Twist}
    {c : (i : O.ChosenIndex) → (ResField (O.chosenPlace i))[X]} (h_lift : IsLiftSetting O c ϑ)
    (hQ : IsAuxiliary (badPlaces D ℓ) ϑ.Q) :
    ∃ J : (D.E →+* ℂ) → Multiset ℤ,
      ∃ B : BaseLevel (stdSpace D.E n) (O.columnCount, O.detExp) D.chosenGroupOrder,
      -- (a)
      (∀ y ∈ (typeProjection O c).range,
        y.toSmoothForm ∈ B.formsOfLevel (![] : Fin 0 → FinPlace D.E)) ∧
      -- (b)
      (∀ y : O.FormV, y.toSmoothForm ∈ BaseLevel.ellIntegralForms →
        D.chosenGroupOrder • (typeProjection O c y).toSmoothForm ∈ BaseLevel.ellIntegralForms) ∧
      -- (c)
      ∀ (K : Type) [Finite K] (u : K → FinPlace D.E), (∀ k : K, u k ∉ badPlaces D ℓ) →
        ∀ x ∈ B.Eigensystem u,
        let R : GalRep ℓ D.E n := normalisedRep O x.galRep
        -- `R` is a representation of a type for the scaled type polynomials of `c`,
        IsRepOfType O O.rankDiff J
          (fun i : O.ChosenIndex ↦ scaledTypePoly O c i * (X - 1) ^ O.rankDiff)
          (Set.conjClosure ϑ.Q ∪ (range u).conjClosure) R ∧
        -- and inertia at the auxiliary places satisfies a quadratic relation
        ∀ g ∈ inertiaAbove (Set.conjClosure ϑ.Q),
          ((R g).val - ϑ.invAvatar g • 1) * ((R g).val - 1) = 0 := by
  classical
  -- Let `π` act on forms through the components at the places `O.places` only. The space `Y`
  -- consists of the forms with the level and character of `O` under `π` that the idempotent `ρ` of
  -- the labels `c` fixes.
  let F : Submodule ℂ (Gf D.E n → WeylIndex n O.columnCount → ℂ) :=
    (stdSpace D.E n).forms (O.columnCount, O.detExp)
  let π : Representation ℂ (Gf D.E n) F :=
    ((stdSpace D.E n).formTranslation (O.columnCount, O.detExp)).comp
      (componentOn n O.places.toFinset)
  have hπ (k : Gf D.E n) (hk : k ∈ supportedOn n O.places) :
      π k = (stdSpace D.E n).formTranslation (O.columnCount, O.detExp) k :=
    congrArg (formTranslation _ _) (componentOn_places_eq_self hk)
  let V : Submodule ℂ F :=
    levelSpace π (levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl)) O.levelChar
  let ρ : Module.End ℂ V := (O.chosenGLRep π).asAlgebraHom (tupleIdem r c)
  let Y : Submodule ℂ F := (ρ.eqLocus 1).map V.subtype
  -- An operator that commutes with `π` on the maximal level commutes with `ρ`, so it keeps `Y`.
  have hY (T : Module.End ℂ F) (hT : ∀ k : stdLevel D.E n, Commute (π k) T) : Y ≤ Y.comap T := by
    rintro _ ⟨u, h_fixed : ρ u = u, rfl⟩
    obtain ⟨hTu, h_comm⟩ : ∃ hTu : T u.val ∈ V, (ρ ⟨T u.val, hTu⟩).val = T (ρ u).val :=
      exists_mem_levelSpace_chosenGLRep_map_eq hT (tupleIdem r c) u
    rw [h_fixed] at h_comm
    exact ⟨⟨T u.val, hTu⟩, Subtype.ext h_comm, rfl⟩
  let B : BaseLevel (stdSpace D.E n) (O.columnCount, O.detExp) D.chosenGroupOrder :=
    { places := O.places.toFinset, forms := Y, map_mem_forms := hY
      exists_level := ⟨levelOf O.placeAt (descentResidueLevel O.toLevelPlaces O.incl), O.levelChar,
        isOpen_levelOf, V.map_subtype_le (ρ.eqLocus 1)⟩
      card_aut_dvd := D.card_classAut_dvd_chosenGroupOrder h_lift.card_le le_rfl }
  refine ⟨normalisedJumps O, B, fun y hy ↦ ?_,
    chosenGroupOrder_nsmul_typeProjection_mem_ellIntegralForms h_lift, ?_⟩
  · -- On the form of `y`, the idempotent `ρ` acts as `typeProjection O c`, which fixes `y`.
    let u : V := ⟨y.toSmoothForm, toSmoothForm_mem_levelSpace_componentOn y⟩
    have h_proj : (ρ u).val = (typeProjection O c y).toSmoothForm := by
      rw [coe_asAlgebraHom_chosenGLRep_apply, toSmoothForm_typeProjection]
      simp only [π, u, MonoidHom.comp_apply]
    rw [IsLiftSetting.typeProjection_eq_self_of_mem_range hy] at h_proj
    exact ⟨⟨u, Subtype.ext h_proj, rfl⟩, toSmoothForm_mem_levelSpace_repOff B rfl y⟩
  · -- The system `x` contains a nonzero form `u` in `Y`, an eigenform to which `x.galRep` is
    -- attached.
    rintro K _ U hU x ⟨f, ⟨hx, hf⟩, hf_ne⟩
    obtain ⟨u, hu, rfl⟩ : ∃ u : V, ρ u = u ∧ u.val = f := hf.left
    have h_eig : IsEigenform u.val.val x.heckePolyAt := x.isEigenform hx hf_ne
    have h_att : GaloisRep.Attached x.heckePolyAt x.galRep := x.attached_galRep hx hf_ne
    -- Off `range U`, the places of `O` and their conjugates, `u` has maximal level.
    have h_form : IsFormOfType O c (range U) u.val x.heckePolyAt := by
      refine ⟨h_eig, u.property, hu, fun v hv hv_star g ↦ ?_⟩
      exact congrArg Subtype.val (levelSpace_le_sphericalAt (by simpa [B] using hv)
        (by simpa [B] using hv_star) (BaseLevel.formsOfLevel_le_levelSpace hf) g)
    exact ⟨h_form.isRepOfType_normalisedRep h_lift hQ (forall_mem_range.2 hU) h_att,
      normalisedRep_quadratic_on_inertia h_lift hQ h_eig h_att
        (hasTwistParahoricType_levelSpace hπ u)⟩

end New.Selmer
