import New.UpperBound.Divisibility.MarkedPrimes

/-!
# The places `Σ_N` above N and the set-up at p = N

This file sets up the case `p = N`. It defines the set `Σ_N` of the conjugates of the places above
`N` that `ιₚ` induces, and shows that it is a split level for `N`. Levels, forms and the operator
`Up` are described at the places of `Σ_N`, in bases of the lattices `L_j` (see
`New.Data.diagPointN`). The file ends with the module `𝒜'` of forms that `Up ^ (ϱ + 1)` sends to
source forms with values integral for `L_0`.

## Main definitions and results

* `New.Data.nonInducedPlaces`, `New.Data.upIntegralForms`: the places `Σ_N` and the module `𝒜'`.
* `New.Data.upOperator_mem_sourceForm`: the operator `Up = upOperator (D.formRepAtN 0)` preserves
  the source forms `D.SourceForm`, the forms on `X_0` fixed by its level.

Notions from other files:
* `New.Data.piNPlaces`: the set of primes dividing `π`, where `π π̄ = N`.
-/

noncomputable section

section PlacesAtLevel

open Matrix Finset Valued WithZero New IsSplitLevel Gf

namespace New.Data

variable {P : Parameters} (D : Data P) [PadicPlace D.N]

open scoped Classical in
/-- The set `Σ_N` of the conjugates of the places above `N` that `ιₚ` induces. -/
def nonInducedPlaces : Finset (FinPlace D.E) :=
  univ.image fun τ : D.Φ ↦ star (D.inducedPlace τ)

lemma star_inducedPlace_mem_nonInducedPlaces (τ : D.Φ) :
    star (D.inducedPlace τ) ∈ D.nonInducedPlaces := by
  classical exact mem_image_of_mem _ (mem_univ τ)

/-- The places of `Σ_N = D.nonInducedPlaces` lie above `N`. -/
lemma natCast_mem_of_mem_nonInducedPlaces {w : FinPlace D.E} (hw : w ∈ D.nonInducedPlaces) :
    ↑D.N ∈ w.asIdeal := by
  grind [p_mem_inducedPlace, mem_star_place, star_natCast, nonInducedPlaces]

/-- The set `Σ_N = D.nonInducedPlaces` is a split level for `N`: it contains exactly one place of
each pair `w, w̄` above `N`, and these places are unramified of degree one. -/
instance isSplitLevel_nonInducedPlaces : IsSplitLevel D.nonInducedPlaces D.N where
  star_notMem := by
    -- The induced places form one orbit of `Φ`, which contains no conjugate pair as `N` splits.
    have h_ne (τ σ : D.Φ) : (σ / τ) • D.inducedPlace τ ≠ star (D.inducedPlace τ) :=
      P.smul_ne_star D.N_modEq_one (D.p_mem_inducedPlace τ)
    simpa [nonInducedPlaces, ← inducedPlace_mul] using h_ne
  q_eq w hw := P.q_eq_of_modEq_one D.N_modEq_one (D.natCast_mem_of_mem_nonInducedPlaces hw)
  v_natCast w hw := D.v_N_eq_exp_neg_one (D.natCast_mem_of_mem_nonInducedPlaces hw)
  natCast_mem_iff w := by
    refine ⟨fun hw ↦ ?_, ?_⟩
    · -- Every place above `N` is an induced place or the conjugate of one.
      obtain ⟨τ, hτ⟩ : ∃ τ : D.Φ, τ • D.inducedPlace 1 = w ∨ star (τ • D.inducedPlace 1) = w :=
        P.exists_smul_eq_or_star (D.p_mem_inducedPlace 1) hw
      rw [← inducedPlace_mul, one_mul] at hτ
      rcases hτ with rfl | rfl <;> simp [D.star_inducedPlace_mem_nonInducedPlaces τ]
    · rintro (hw | hw) <;> simpa using D.natCast_mem_of_mem_nonInducedPlaces hw

/-- The point supported above `N` that is `diag (1, …, 1, N)` at the places of `Σ_N` in `S`, and `1`
at the other places of `Σ_N`. -/
abbrev diagPoint (j : ℕ) (S : Finset (FinPlace D.E)) : Gf D.E (D.X j) :=
  embedGL (diagN (P := D.nonInducedPlaces) (D.InitIndex j) S)

/-- The point `δ_j`, which is `diag (1, …, 1, N)` at the places of `Σ_N` that divide `π` and `1` at
the others. It takes the standard lattice at `Σ_N` to `L_j`, the lattice of integral vectors whose
last coordinate is divisible by `π`. -/
abbrev diagPointN (j : ℕ) : Gf D.E (D.X j) := D.diagPoint j D.piNPlaces

/-- The point `δ_j^∨`, which takes the standard lattice to the dual lattice `L_j^∨` at `Σ_N`. -/
abbrev dualPointN (j : ℕ) : Gf D.E (D.X j) :=
  D.diagPointN j * (D.diagPoint j D.nonInducedPlaces)⁻¹

/-- A matrix `a` over `LocProd D.nonInducedPlaces`, the product of the completions at `Σ_N`, goes to
`δ_j * embedGL a * δ_j⁻¹`. Here `embedGL a` is the unitary adelic point supported above `N` with
components `a` at `Σ_N`, and `δ_j = D.diagPointN j`. So `a` is read in a basis of `L_j`. -/
def conjEmbedGL (j : ℕ) : GL (D.X j) (LocProd D.nonInducedPlaces) →* Gf D.E (D.X j) :=
  (MulAut.conj (D.diagPointN j)).toMonoidHom.comp embedGL

/-- Forms on `X_j` as a representation of `GL` at `Σ_N`, in a basis of `L_j`. -/
abbrev formRepAtN (j : ℕ) : Rep ℂ (GL (D.X j) (LocProd D.nonInducedPlaces)) :=
  Rep.of (X := D.FormX j) ((smoothFormRep (stdSpace D.E (D.X j)).embFin _).comp (D.conjEmbedGL j))

open scoped Classical in
/-- The point `D.diagPoint j S` is supported above `N`, and is `diag (1, …, 1, N)` at the places of
`Σ_N` in `S` and `1` at the other places of `Σ_N`. For an infinite place `τ`, the map
`adeleExtension (weightEmbedding ιₚ τ)` reads an adele in `ℂ_[N]` through its component at the
conjugate `w̄` of the place `w = inducedPlace τ`. It sends the point to `diag (1, …, 1, N)` if `w̄`
lies in `S`, and to `1` otherwise. -/
lemma map_adeleExtension_diagPoint (j : ℕ) (S : Finset (FinPlace D.E)) (τ : D.Φ) :
    GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) (D.diagPoint j S).val =
      diagGL fun i : D.X j ↦ if i.isLeft then 1 else
        if star (inducedPlace τ) ∈ S then .mk0 ↑D.N NeZero.out else 1 := by
  -- The embedding factors through the completion at `star (inducedPlace τ)`, a place of `Σ_N`.
  let w : FinPlace D.E := placeOfEmb (weightEmbedding ιₚ τ)
  let φ : LocField w →+* ℂ_[D.N] := (exists_placeOfEmb_extension (weightEmbedding ιₚ τ)).choose
  have h_place : w = star (D.inducedPlace τ) := by simp [w, inducedPlace, placeOfEmb_comp_star]
  have h_factor (g : Gf D.E (D.X j)) :
      GeneralLinearGroup.map (adeleExtension (weightEmbedding ιₚ τ)) g.val =
        GeneralLinearGroup.map φ (g.atPlace w) := rfl
  have h_at : (D.diagPoint j S).atPlace w = diagGL fun i : D.X j ↦
      if i.isLeft then 1 else if w ∈ S then .mk0 (D.N : LocField w) NeZero.out else 1 :=
    atPlace_embedGL_diagN (n := D.InitIndex j) (S := S)
      ⟨w, by simpa [h_place] using D.star_inducedPlace_mem_nonInducedPlaces τ⟩
  rw [h_factor, h_at, ← h_place, Units.ext_iff]
  by_cases hS : w ∈ S <;> simp [hS, apply_ite Units.val, apply_ite φ]

/-- The direct datum is non-zero at a matrix `M` over the completions at `Σ_N` exactly if at each
place `w` of `Σ_N` the matrix `M` is integral and its last column is that of `1` modulo `w`. Here
`v` is the valuation of the completion at `w`, with `v N = exp (-1)`. -/
lemma directDatum_ne_zero_iff {j : ℕ} (M : Matrix (D.X j) (D.X j) (LocProd D.nonInducedPlaces)) :
    directDatum M ≠ 0 ↔ ∀ w : D.nonInducedPlaces,
      (∀ b c : D.X j, v (M b c w) ≤ 1) ∧
      ∀ b : D.X j, v (M b (.inr ()) w - if b.isLeft then 0 else 1) ≤ exp (-1) := by
  -- non-vanishing means integral entries and last column `lastBasisVector` after reduction
  have h_lift : directDatum M ≠ 0 ↔ ∃ h : ∀ b c : D.X j, M b c ∈ SemilocalField.O,
      ∀ b : D.X j, D.isSplitLevel_nonInducedPlaces.reduction ⟨M b (.inr ()), h b (.inr ())⟩ =
        lastBasisVector b := by
    simp [directDatum, lastColDatum, liftFn_apply, funext_iff (α := D.X j), -Sum.forall]
    exact exists_congr fun _ ↦ by split_ifs <;> simp [*]
  simp [h_lift, mem_O_locProd, reduction_eq_iff, D.isSplitLevel_nonInducedPlaces.v_natCast,
    div_le_one₀, ZMod.val_one, ← forall_and, forall_comm (β := D.nonInducedPlaces),
    -Subtype.forall, -ZMod.natCast_val]

/-- Let `Σ_N = D.nonInducedPlaces` be the conjugates of the places above `N` induced by the
embedding of `[PadicPlace D.N]`, let `D.piNPlaces` be the primes dividing `π = D.piN` (where
`π π̄ = N`), and let `δ_j = D.diagPointN j` be `diag (1, …, 1, N)` at the places of `Σ_N` that
divide `π` and `1` at the others. The matrix of `δ_j⁻¹ k δ_j` at `Σ_N` is integral with last column
that of `1` modulo `N` exactly if, for each `w` in `Σ_N`, `k` is integral at `w`, the last row of
`k⁻¹` is that of `1` modulo `w̄` if `w̄ ∣ π`, and the last row of `k` is that of `1` modulo `w` if
`w ∣ π`. -/
lemma directDatum_conj_ne_zero_iff {j : ℕ} (k : Gf D.E (D.X j)) :
    directDatum (atPlaces D.nonInducedPlaces ((D.diagPointN j)⁻¹ * k * D.diagPointN j)).val ≠ 0 ↔
      ∀ w ∈ D.nonInducedPlaces,
        (∀ b c : D.X j, v (k.atPlace w b c) ≤ 1) ∧
        (star w ∈ D.piNPlaces → ∀ b : D.X j,
          v (((k⁻¹.atPlace (star w)).val - 1) (.inr ()) b) ≤ exp (-1)) ∧
        (w ∈ D.piNPlaces → ∀ b : D.X j, v (((k.atPlace w).val - 1) (.inr ()) b) ≤ exp (-1)) := by
  classical
  rw [directDatum_ne_zero_iff, Subtype.forall']
  refine forall_congr' fun w ↦ ?_
  -- Conjugation multiplies the last column by `t` and divides the last row by `t`, where `t = N`
  -- at `w ∣ π` and `t = 1` otherwise.
  let t (i : D.X j) : LocField w.val :=
    if i.isLeft then 1 else if w.val ∈ D.piNPlaces then D.N else 1
  have h_conj (b c : D.X j) :
      (atPlaces D.nonInducedPlaces ((D.diagPointN j)⁻¹ * k * D.diagPointN j)).val b c w =
        (t b)⁻¹ * k.atPlace w b c * t c := by
    have h_entry : atPlaces D.nonInducedPlaces k b c w = k.atPlace w b c := rfl
    cases b <;> cases c <;> simp [t, ← map_inv, diagN, h_entry, apply_ite Units.val]
  -- The last row of `k⁻¹` at `w̄` is the conjugate of the last column of `k` at `w`.
  have h_star (b : D.X j) : v (((k⁻¹.atPlace (star w.val)).val - 1) (.inr ()) b) =
      v (k.atPlace w b (.inr ()) - if b.isLeft then 0 else 1) := by
    rw [← v_conjLoc rfl (k.atPlace w b (.inr ()) - _)]
    cases b <;> simp [k⁻¹.atPlace_star rfl, ← map_inv]
  simp only [h_conj, h_star]
  by_cases hw : w.val ∈ D.piNPlaces
  · -- Integrality of the conjugate is the congruence on the last row off the corner entry; the
    -- congruence on its last column covers the corner entry and otherwise says that the last
    -- column of `k` is integral.
    have hN : v (D.N : LocField w.val) = exp (-1) :=
      D.isSplitLevel_nonInducedPlaces.v_natCast w w.prop
    have h_exp : exp (-1 : ℤ) ≤ 1 := exp_le_exp.2 (by norm_num : (-1 : ℤ) ≤ 0)
    let M : Matrix (D.X j) (D.X j) (LocField w.val) := k.atPlace w
    -- Both sides entry by entry: upper block, last row, last column, corner, then the congruences.
    suffices h_entries : (∀ a a', v (M (.inl a) (.inl a')) ≤ 1) ∧
          (∀ a, v (M (.inr ()) (.inl a)) ≤ exp (-1)) ∧
          (∀ a, exp (-1) * v (M (.inl a) (.inr ())) ≤ 1) ∧ v (M (.inr ()) (.inr ())) ≤ 1 ∧
          (∀ a, v (M (.inl a) (.inr ())) ≤ 1) ∧ v (M (.inr ()) (.inr ()) - 1) ≤ exp (-1) ↔
        (∀ a a', v (M (.inl a) (.inl a')) ≤ 1) ∧ (∀ a, v (M (.inr ()) (.inl a)) ≤ 1) ∧
          (∀ a, v (M (.inl a) (.inr ())) ≤ 1) ∧ v (M (.inr ()) (.inr ())) ≤ 1 ∧
          (∀ a, v (M (.inr ()) (.inl a)) ≤ exp (-1)) ∧ v (M (.inr ()) (.inr ()) - 1) ≤ exp (-1) by
      simpa [M, t, hw, hN, D.isSplitLevel_piNPlaces.star_notMem _ hw, inv_mul_le_one₀,
        mul_right_comm, Unique.forall_iff, inv_mul_cancel_of_invertible, forall_and, and_assoc,
        -WithZero.inv_exp] using h_entries
    constructor
    · rintro ⟨h_block, h_row, -, h_corner, h_col, h_cong⟩
      exact ⟨h_block, fun a ↦ (h_row a).trans h_exp, h_col, h_corner, h_row, h_cong⟩
    · rintro ⟨h_block, -, h_col, h_corner, h_row, h_cong⟩
      exact ⟨h_block, h_row, fun a ↦ mul_le_one' h_exp (h_col a), h_corner, h_col, h_cong⟩
  · -- Both sides ask for integrality and the congruence on the last column.
    have h_star_mem : star w.val ∈ D.piNPlaces :=
      ((D.isSplitLevel_piNPlaces.natCast_mem_iff _).1 (natCast_level_mem _ w.prop)).resolve_left hw
    simp [t, hw, h_star_mem]

/-- Let `Σ_N = D.nonInducedPlaces` be the conjugates of the places of `E` above `N = D.N` induced by
the embedding `ιₚ` of `[PadicPlace D.N]`, and let `δ_j = D.diagPointN j` be the point supported
above `N` that is `diag (1, …, 1, N)` at the places of `Σ_N` dividing `π = D.piN` (where `π π̄ = N`)
and `1` at the other places of `Σ_N`. Let `k` lie in `D.levelX j`, the group of finite adelic points
of the unitary group of the hermitian space `X_j` (basis `D.X j`) that lie in the integral subgroup
`D.chosenLevel` and have last row that of `1` modulo `π`. Then the components of `δ_j⁻¹ k δ_j` at
`Σ_N` lie in `mirabolic`, the group of integral invertible matrices whose last column is that of
`1` modulo `N`. -/
lemma atPlaces_conj_mem_mirabolic {j : ℕ} (k : D.levelX j) :
    atPlaces D.nonInducedPlaces ((D.diagPointN j)⁻¹ * k.val * D.diagPointN j) ∈ mirabolic := by
  have h_ne (k' : D.levelX j) : directDatum
      (atPlaces D.nonInducedPlaces ((D.diagPointN j)⁻¹ * k'.val * D.diagPointN j)).val ≠ 0 := by
    obtain ⟨h_level, h_row⟩ := D.mem_levelX.1 k'.prop
    obtain ⟨-, h_row_inv⟩ := D.mem_levelX.1 k'⁻¹.prop
    exact (D.directDatum_conj_ne_zero_iff _).2 fun w _ ↦
      ⟨(mem_stdLevel_iff.1 (levelOf_le_stdLevel h_level) w).isIntMatrix, h_row_inv (star w),
        h_row w⟩
  have h_ne_inv : directDatum
      (atPlaces D.nonInducedPlaces ((D.diagPointN j)⁻¹ * k.val * D.diagPointN j))⁻¹.val ≠ 0 := by
    simpa [mul_assoc] using h_ne k⁻¹
  obtain ⟨a, h_col, ha⟩ := exists_inclGL_eq (h_ne k) h_ne_inv
  -- `h_col`: the indicator of "the last column is the last basis vector" is non-zero at `a`
  have h_last : (reductionGL a).valᵀ (.inr ()) = lastBasisVector := (ite_ne_right_iff.1 h_col).1
  exact ⟨a, (mulVec_single_one ..).trans h_last, ha⟩

/-- Let `Σ_N = D.nonInducedPlaces` be the conjugates of the places of `E` above `N = D.N` induced by
the embedding `ιₚ` of `[PadicPlace D.N]`, and let `δ_j = D.diagPointN j` be the point supported
above `N` that is `diag (1, …, 1, N)` at the places of `Σ_N` dividing `π = D.piN` (where `π π̄ = N`)
and `1` at the other places of `Σ_N`. Let `g` be a finite adelic point of the unitary group of the
hermitian space `X_j` (basis `D.X j`). Suppose that `g` is `1` at every place outside `Σ_N` and its
conjugates (`supportedOn`), and that the components of `δ_j⁻¹ g δ_j` at `Σ_N` lie in `mirabolic`:
they are integral and invertible, with last column that of `1` modulo `N`. Then `g` lies in
`D.levelX j`, the elements of the integral subgroup `D.chosenLevel` with last row that of `1`
modulo `π`. -/
lemma mem_levelX_of_mem_mirabolic {j : ℕ} {g : Gf D.E (D.X j)}
    (h_supp : g ∈ supportedOn (D.X j) D.nonInducedPlaces)
    (h_mir : atPlaces D.nonInducedPlaces ((D.diagPointN j)⁻¹ * g * D.diagPointN j) ∈ mirabolic) :
    g ∈ D.levelX j := by
  choose h_int _ h_row using (D.directDatum_conj_ne_zero_iff g).1
    (directDatum_ne_zero_of_mem_mirabolic h_mir)
  choose h_int_inv h_row_inv _ using (D.directDatum_conj_ne_zero_iff g⁻¹).1
    (directDatum_ne_zero_of_mem_mirabolic (by simpa [mul_assoc] using inv_mem h_mir))
  have h_std : g ∈ stdLevel D.E (D.X j) :=
    (mem_stdLevel_iff_of_supportedOn h_supp).2 fun w hw ↦ mem_intGL.2 ⟨h_int w hw, h_int_inv w hw⟩
  refine D.mem_levelX.2
    ⟨D.inf_supportedOn_le_chosenLevel natCast_level_mem ⟨h_std, h_supp⟩, fun w hw ↦ ?_⟩
  obtain hw_mem | hw_star : w ∈ D.nonInducedPlaces ∨ star w ∈ D.nonInducedPlaces :=
    (natCast_mem_iff w).1 (D.isSplitLevel_piNPlaces.natCast_level_mem w hw)
  · exact h_row w hw_mem hw
  · -- If `w̄ ∈ Σ_N`, use the condition on `g⁻¹` at `w̄`.
    specialize h_row_inv (star w) hw_star
    rw [star_star, inv_inv] at h_row_inv
    exact h_row_inv hw

/-- The representation `ρ = D.formRepAtN 0` is the action of matrices at `Σ_N` on algebraic
automorphic forms for the unitary group of the hermitian space `X_0`, by right translation after
conjugation by `D.diagPointN 0`. Let `φ` be a source form, one fixed by the level subgroup
`D.levelX 0`, and let it be ramified: at each prime `u` dividing `π = D.piN` (where `π π̄ = N`), its
mean over the powers of the scaling `D.scalingGenerator u` is `0`. Then `φ` is a ramified vector of
`ρ`: for each `w` in `Σ_N` it has the form `ψ - ρ x ψ`, with `x` an integral unit scalar matrix that
is `1` modulo `N` at the other places of `Σ_N`. -/
lemma mem_ramified_of_mem_ramifiedSourceForms {φ : D.SourceForm} (hφ : φ ∈ D.ramifiedSourceForms) :
    φ.val ∈ ramified (D.formRepAtN 0) := by
  intro w
  -- One of `w`, `w̄` is a place `u ∣ π`, and the scaling at `u` is an integral unit scalar at `w`.
  obtain ⟨u, hu⟩ : ∃ u : D.piNPlaces, w.val = u ∨ star w.val = u := by
    simpa [and_or_left, exists_or] using
      (D.isSplitLevel_piNPlaces.natCast_mem_iff _).1 (natCast_level_mem _ w.prop)
  obtain ⟨h_int, h_supp⟩ := D.isScalingAt_scalingGenerator u
  have h_supp_w : ∀ u' ≠ w.val, star u' ≠ w → (D.scalingGenerator u).val u' = 1 := by aesop
  obtain ⟨x, hx_one, hx⟩ := exists_embedGL_scalar_eq_scalarFin (n := D.X 0) w h_int h_supp_w
  -- A scalar is not changed by the passage to a basis of `L_0`.
  have h_conj : D.conjEmbedGL 0 (inclGL (GeneralLinearGroup.scalar (D.X 0) x)) =
      scalarFin (D.X 0) (D.scalingGenerator u) := by
    simp [conjEmbedGL, hx, ← (Seesaw.commute_scalarFin _).eq]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : D.SourceForm, φ.val = ψ.val -
      algFormRep D.columnCount (D.lastEntry 0) (scalarFin (D.X 0) (D.scalingGenerator u)) ψ :=
    D.exists_eq_sub_scalingGenerator u hφ
  exact ⟨x, hx_one, ψ, by simp [h_conj, hψ]⟩

/-- For a matrix `a` over the completions at `Σ_N = D.nonInducedPlaces`, the adelic point
`D.conjEmbedGL j a` (`a` read in a basis of the lattice `L_j`) lies in
`supportedOn (D.X j) D.nonInducedPlaces`. That is, its component is `1` at every place outside `Σ_N`
and the conjugate places. -/
lemma conjEmbedGL_mem_supportedOn (j : ℕ) (a : GL (D.X j) (LocProd D.nonInducedPlaces)) :
    D.conjEmbedGL j a ∈ supportedOn (D.X j) D.nonInducedPlaces :=
  mul_mem (mul_mem (embedGL_mem_supportedOn _) (embedGL_mem_supportedOn a))
    (inv_mem (embedGL_mem_supportedOn _))

/-- The stabiliser `mirabolic` of the standard marked lattice, read in a basis of `L_j`, lies in the
level of `X_j`. -/
lemma conjEmbedGL_mem_levelX {j : ℕ} {a : GL (D.X j) (LocProd D.nonInducedPlaces)}
    (ha : a ∈ mirabolic) : D.conjEmbedGL j a ∈ D.levelX j :=
  D.mem_levelX_of_mem_mirabolic (D.conjEmbedGL_mem_supportedOn j a)
    (by simpa [conjEmbedGL, mul_assoc] using ha)

/-- The operator `Up = upOperator (D.formRepAtN 0)` acts on `D.FormX 0`, the algebraic automorphic
forms for the unitary group of the hermitian space `X_0`, and preserves `D.SourceForm`, the forms
fixed by the level subgroup `D.levelX 0`. -/
lemma upOperator_mem_sourceForm {φ : D.FormX 0} (hφ : φ ∈ D.SourceForm) :
    upOperator (D.formRepAtN 0) φ ∈ D.SourceForm := by
  -- Write an element `k` of the level as its part above `N`, with matrix `a` in a basis of `L_0`,
  -- times a part `b` away from `N`. Both parts lie in the level. `Up` commutes with `b`, which
  -- fixes `φ`, and preserves the forms fixed by the part of the level above `N`.
  intro k
  let a : GL (D.X 0) (LocProd D.nonInducedPlaces) :=
    atPlaces D.nonInducedPlaces ((D.diagPointN 0)⁻¹ * k.val * D.diagPointN 0)
  have ha : a ∈ mirabolic := D.atPlaces_conj_mem_mirabolic k
  let b : Gf D.E (D.X 0) := (D.conjEmbedGL 0 a)⁻¹ * k.val
  have hb_away : b ∈ trivialOn (D.X 0) D.nonInducedPlaces := by
    have h_one : atPlaces D.nonInducedPlaces b = 1 := by simp [a, b, conjEmbedGL, mul_assoc]
    refine mem_trivialOn.2 fun w hw ↦ Units.ext (Matrix.ext fun i j ↦ ?_)
    rw [show b.atPlace w i j = atPlaces D.nonInducedPlaces b i j ⟨w, hw⟩ from rfl, h_one]
    by_cases hij : i = j <;> simp [hij]
  have h_fix {g : Gf D.E (D.X 0)} (hg : g ∈ D.levelX 0) :
      algFormRep D.columnCount (D.lastEntry 0) g φ = φ := by simpa using hφ ⟨g, hg⟩
  have h_commute : Commute (algFormRep D.columnCount (D.lastEntry 0) b)
    (upOperator (D.formRepAtN 0)) :=
    commute_upOperator (π := D.formRepAtN 0) fun g ↦
      (commute_supportedOn_trivialOn (D.conjEmbedGL_mem_supportedOn 0 g) hb_away).symm.map _
  have hb_fix : algFormRep D.columnCount (D.lastEntry 0) b (upOperator (D.formRepAtN 0) φ) =
      upOperator (D.formRepAtN 0) φ := by
    rw [← Module.End.mul_apply, h_commute.eq, Module.End.mul_apply,
      h_fix (mul_mem (inv_mem (D.conjEmbedGL_mem_levelX ha)) k.prop)]
  -- The character of the level in the definition of `D.SourceForm` is trivial.
  rw [show k.val = D.conjEmbedGL 0 a * b from (mul_inv_cancel_left _ _).symm, map_mul,
    Module.End.mul_apply, hb_fix, MonoidHom.one_apply, one_smul]
  exact mirabolic_fix_upOperator (π := D.formRepAtN 0)
    (fun _ hg ↦ h_fix (D.conjEmbedGL_mem_levelX hg)) ha

/-- The module `𝒜'` of the forms `φ` on `X_0` such that `Up ^ (ϱ + 1) φ` is a source form with
values integral for `L_0`, over the ring `embValRing` of complex numbers that `ιₚ` sends to `N`-adic
integers. Here `Up` is the operator `upOperator` at `Σ_N` (see `upOperator_mem_sourceForm`), and
`ϱ = D.ϱ` with `ϱ + 1 = m / 2`. The module does not depend on the twist. -/
abbrev upIntegralForms : Submodule embValRing (D.FormX 0) :=
  (integralFormsAt D.SourceForm (D.diagPointN 0)).comap
    ((upOperator (D.formRepAtN 0) ^ (D.ϱ + 1)).restrictScalars embValRing)

end New.Data

end PlacesAtLevel

end
