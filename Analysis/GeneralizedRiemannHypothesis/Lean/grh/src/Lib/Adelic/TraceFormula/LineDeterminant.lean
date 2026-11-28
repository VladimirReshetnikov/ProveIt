import Lib.Base

/-!
# Traces on the range of an idempotent from traces of a raising operator

Let `T⁺`, `T⁻` be adjoint operators on a finite-dimensional inner product space with
`T⁺ * T⁻ = d • (1 + c • e)`, where `d, c > 0`, `e` is idempotent and `A` commutes with `T⁺` and
`T⁻`. The traces of the `A ^ l * T⁺ ^ i`, `l, i ≥ 1`, determine the trace of `A` on the range of `e`
(`LineRelation.trace_mul_mean_eq`): on the generalised eigenspace of `A` for each non-zero
eigenvalue they give the eigenvalues of `T⁺`, hence the dimension and
`|det T⁺| ^ 2 = d ^ dim * (1 + c) ^ rank e`.

The first section collects what traces determine on generalised eigenspaces; in particular the
traces of all powers of an operator determine its characteristic polynomial
(`charpoly_eq_of_trace_pow_eq`).
-/

open Module LinearMap Polynomial InnerProductSpace

noncomputable section

namespace New

section GenEigenspace

variable {B B' : Type*} [AddCommGroup B] [Module ℂ B] [AddCommGroup B'] [Module ℂ B']
  {A T : End ℂ B} {A' T' : End ℂ B'}

/-- For an operator `T` that commutes with `A`, the restriction of `T` to the generalised
eigenspace of `A` for `μ`. -/
abbrev restrictGenEigenspace (h : Commute A T) (μ : ℂ) : End ℂ (A.maxGenEigenspace μ) :=
  T.restrict fun _ hx ↦ End.mapsTo_maxGenEigenspace_of_comm h μ hx

/-- Restriction to a generalised eigenspace of `A` commutes with taking powers. -/
lemma restrictGenEigenspace_pow (h : Commute A T) (μ : ℂ) (i : ℕ) :
    restrictGenEigenspace h μ ^ i = restrictGenEigenspace (h.pow_right i) μ :=
  End.pow_restrict i _

variable [Module.Finite ℂ B] [Module.Finite ℂ B']

/-- If `T` commutes with `A`, then on the generalised eigenspace of `A` for `μ` the trace of
`A * T` is `μ` times the trace of `T`, because `A - μ` is nilpotent there and commutes with `T`. -/
lemma trace_restrictGenEigenspace_mul (h : Commute A T) (μ : ℂ) :
    trace ℂ (A.maxGenEigenspace μ)
        (restrictGenEigenspace (T := A * T) ((Commute.refl A).mul_right h) μ) =
      μ * trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) := by
  have h_comm : Commute (restrictGenEigenspace h μ) (restrictGenEigenspace (.refl A) μ) :=
    restrict_commute h.symm _ _
  rw [show restrictGenEigenspace ((Commute.refl A).mul_right h) μ =
      restrictGenEigenspace (.refl A) μ * restrictGenEigenspace h μ from rfl, ← h_comm.eq]
  exact trace_comp_eq_mul_of_commute_of_isNilpotent μ h_comm
    (A.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ)

/-- If `T` commutes with `A`, then on the generalised eigenspace of `A` for `μ` the trace of
`A ^ l * T` is `μ ^ l` times the trace of `T`. -/
lemma trace_restrictGenEigenspace_pow_mul (h : Commute A T) (μ : ℂ) (l : ℕ) :
    trace ℂ (A.maxGenEigenspace μ)
        (restrictGenEigenspace (T := A ^ l * T) ((Commute.self_pow A l).mul_right h) μ) =
      μ ^ l * trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) := by
  induction l with
  | zero => simp only [restrictGenEigenspace, pow_zero, one_mul]
  | succ l ih =>
    have h_comm : Commute A (A ^ l * T) := (Commute.self_pow A l).mul_right h
    rw [pow_succ' μ, mul_assoc, ← ih, ← trace_restrictGenEigenspace_mul h_comm]
    simp only [restrictGenEigenspace, pow_succ', mul_assoc]

/-- Let `T` commute with `A` and let the finite set `S` contain all eigenvalues of `A`. Then the
trace of `A ^ l * T` is the sum over `μ ∈ S` of `μ ^ l` times the trace of `T` on the generalised
eigenspace of `A` for `μ`. -/
lemma trace_pow_mul_eq_sum (h : Commute A T) {S : Finset ℂ}
    (hS : ∀ μ : ℂ, μ ∉ S → A.maxGenEigenspace μ = ⊥) (l : ℕ) :
    trace ℂ B (A ^ l * T) =
      ∑ μ ∈ S, μ ^ l * trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) := by
  have h_subset : {μ : ℂ | A.maxGenEigenspace μ ≠ ⊥} ⊆ (S : Set ℂ) :=
    fun μ hμ ↦ by_contra fun hμS ↦ hμ (hS μ hμS)
  have h_finite : {μ : ℂ | A.maxGenEigenspace μ ≠ ⊥}.Finite := S.finite_toSet.subset h_subset
  have h_internal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    A.independent_maxGenEigenspace A.iSup_maxGenEigenspace_eq_top
  have h_comm : Commute A (A ^ l * T) := (Commute.self_pow A l).mul_right h
  calc _ = ∑ μ ∈ h_finite.toFinset,
          trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h_comm μ) :=
      trace_eq_sum_trace_restrict' h_internal h_finite (End.mapsTo_maxGenEigenspace_of_comm h_comm)
    _ = ∑ μ ∈ S, trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h_comm μ) := by
      refine Finset.sum_subset (h_finite.toFinset_subset.2 h_subset) fun μ _ hμ ↦ ?_
      have : Subsingleton (A.maxGenEigenspace μ) :=
        Submodule.subsingleton_iff_eq_bot.2 (by simpa using hμ)
      rw [Subsingleton.eq_zero (restrictGenEigenspace h_comm μ), map_zero]
    _ = ∑ μ ∈ S, μ ^ l * trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) :=
      Finset.sum_congr rfl fun μ _ ↦ trace_restrictGenEigenspace_pow_mul h μ l

/-- The sequences `l ↦ μ ^ l`, `μ : ℂ`, are linearly independent: two combinations of them that
agree for all `l` have the same coefficients. -/
lemma eq_of_sum_pow_mul_eq {S : Finset ℂ} {a a' : ℂ → ℂ}
    (h_sum : ∀ l : ℕ, ∑ μ ∈ S, μ ^ l * a μ = ∑ μ ∈ S, μ ^ l * a' μ) {μ : ℂ} (hμ : μ ∈ S) :
    a μ = a' μ := by
  have h_indep : LinearIndependent ℂ fun μ : ℂ ↦ ⇑(powersHom ℂ μ) :=
    (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp _ (powersHom ℂ).injective
  have h_fun : ∑ ν ∈ S, a ν • ⇑(powersHom ℂ ν) = ∑ ν ∈ S, a' ν • ⇑(powersHom ℂ ν) := by
    funext l
    simpa [mul_comm] using h_sum l.toAdd
  exact linearIndependent_iff'ₛ.1 h_indep S a a' h_fun μ hμ

/-- Given operators `A` and `A'` and a number `μ`, there is a finite set that contains `μ` and all
eigenvalues of `A` and of `A'`. -/
lemma exists_finset_maxGenEigenspace_eq_bot (A : End ℂ B) (A' : End ℂ B') (μ : ℂ) :
    ∃ S : Finset ℂ, μ ∈ S ∧
      (∀ ν : ℂ, ν ∉ S → A.maxGenEigenspace ν = ⊥) ∧
      ∀ ν : ℂ, ν ∉ S → A'.maxGenEigenspace ν = ⊥ := by
  have h_finite : {ν : ℂ | A.maxGenEigenspace ν ≠ ⊥}.Finite :=
    Submodule.finite_ne_bot_of_iSupIndep A.independent_maxGenEigenspace
  have h_finite' : {ν : ℂ | A'.maxGenEigenspace ν ≠ ⊥}.Finite :=
    Submodule.finite_ne_bot_of_iSupIndep A'.independent_maxGenEigenspace
  exact ⟨insert μ (h_finite.toFinset ∪ h_finite'.toFinset), Finset.mem_insert_self _ _,
    by simp +contextual, by simp +contextual⟩

/-- Let `T` commute with `A` and `T'` with `A'`. If the traces of `A ^ l * T` and `A' ^ l * T'`
agree for all `l`, then so do the traces of `T` and `T'` on the generalised eigenspaces of `A`
and `A'` for each `μ`. -/
lemma trace_restrictGenEigenspace_eq (h : Commute A T) (h' : Commute A' T')
    (h_trace : ∀ l : ℕ, trace ℂ B (A ^ l * T) = trace ℂ B' (A' ^ l * T')) (μ : ℂ) :
    trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) =
      trace ℂ (A'.maxGenEigenspace μ) (restrictGenEigenspace h' μ) := by
  obtain ⟨S, hμ, hS, hS'⟩ := exists_finset_maxGenEigenspace_eq_bot A A' μ
  refine eq_of_sum_pow_mul_eq
    (a := fun ν ↦ trace ℂ (A.maxGenEigenspace ν) (restrictGenEigenspace h ν))
    (a' := fun ν ↦ trace ℂ (A'.maxGenEigenspace ν) (restrictGenEigenspace h' ν)) (fun l ↦ ?_) hμ
  rw [← trace_pow_mul_eq_sum h hS, ← trace_pow_mul_eq_sum h' hS', h_trace]

/-- Let `T` commute with `A` and `T'` with `A'`. If the traces of `A ^ (l + 1) * T` and
`A' ^ (l + 1) * T'` agree for all `l`, then so do the traces of `T` and `T'` on the generalised
eigenspaces of `A` and `A'` for each non-zero `μ`. -/
lemma trace_restrictGenEigenspace_eq_of_ne_zero (h : Commute A T) (h' : Commute A' T')
    (h_trace : ∀ l : ℕ, trace ℂ B (A ^ (l + 1) * T) = trace ℂ B' (A' ^ (l + 1) * T'))
    {μ : ℂ} (hμ : μ ≠ 0) :
    trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) =
      trace ℂ (A'.maxGenEigenspace μ) (restrictGenEigenspace h' μ) := by
  apply mul_left_cancel₀ hμ
  rw [← trace_restrictGenEigenspace_mul, ← trace_restrictGenEigenspace_mul]
  refine trace_restrictGenEigenspace_eq _ _ (fun l ↦ ?_) μ
  rw [← mul_assoc, ← mul_assoc, ← pow_succ, ← pow_succ, h_trace]

/-- The trace of the identity on a generalised eigenspace is the dimension of that space. -/
lemma trace_restrictGenEigenspace_one (A : End ℂ B) (μ : ℂ) :
    trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace (Commute.one_right A) μ) =
      finrank ℂ (A.maxGenEigenspace μ) :=
  trace_one ℂ (A.maxGenEigenspace μ)

/-- Operators whose generalised eigenspaces have the same dimensions for every `μ` have the same
characteristic polynomial, as these dimensions are the multiplicities of its roots. -/
lemma charpoly_eq_of_finrank_maxGenEigenspace_eq
    (h_finrank : ∀ μ : ℂ, finrank ℂ (A.maxGenEigenspace μ) = finrank ℂ (A'.maxGenEigenspace μ)) :
    A.charpoly = A'.charpoly := by
  have h_roots : A.charpoly.roots = A'.charpoly.roots := by
    ext μ
    simp_rw [count_roots, ← finrank_maxGenEigenspace_eq, h_finrank]
  rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic,
    (IsAlgClosed.splits A'.charpoly).eq_prod_roots_of_monic A'.charpoly_monic, h_roots]

/-- Operators `A` and `A'` with the same traces of all powers have the same characteristic
polynomial. -/
lemma charpoly_eq_of_trace_pow_eq (h_trace : ∀ l : ℕ, trace ℂ B (A ^ l) = trace ℂ B' (A' ^ l)) :
    A.charpoly = A'.charpoly := by
  refine charpoly_eq_of_finrank_maxGenEigenspace_eq fun μ ↦ Nat.cast_injective (R := ℂ) ?_
  rw [← trace_restrictGenEigenspace_one, ← trace_restrictGenEigenspace_one]
  exact trace_restrictGenEigenspace_eq _ _ (fun l ↦ by simp only [mul_one, h_trace]) μ

lemma finrank_maxGenEigenspace_zero_of_det_ne_zero (h_det : T.det ≠ 0) :
    finrank ℂ (T.maxGenEigenspace 0) = 0 := by
  rw [finrank_maxGenEigenspace_eq]
  exact rootMultiplicity_eq_zero fun h_root ↦
    h_det (by simp [det_eq_sign_charpoly_coeff, coeff_zero_eq_eval_zero, h_root.eq_zero])

/-- Two invertible operators with the same traces of all positive powers have the same
characteristic polynomial. -/
lemma charpoly_eq_of_trace_pow_succ_eq (h_det : T.det ≠ 0) (h_det' : T'.det ≠ 0)
    (h_trace : ∀ i : ℕ, trace ℂ B (T ^ (i + 1)) = trace ℂ B' (T' ^ (i + 1))) :
    T.charpoly = T'.charpoly := by
  refine charpoly_eq_of_finrank_maxGenEigenspace_eq fun μ ↦ Nat.cast_injective (R := ℂ) ?_
  obtain rfl | hμ := eq_or_ne μ 0
  · simp [finrank_maxGenEigenspace_zero_of_det_ne_zero, h_det, h_det']
  rw [← trace_restrictGenEigenspace_one, ← trace_restrictGenEigenspace_one]
  exact trace_restrictGenEigenspace_eq_of_ne_zero _ _ (fun l ↦ by simp only [mul_one, h_trace]) hμ

/-- For an idempotent `e`, the determinant of `1 + c e` is `(1 + c) ^ rank e`. -/
lemma det_one_add_smul_of_isIdempotentElem {e : End ℂ B} (he : IsIdempotentElem e) (c : ℂ) :
    (1 + c • e).det = (1 + c) ^ finrank ℂ (range e) := by
  -- The operator is `1 + c` on the range of `e` and induces the identity on the quotient.
  have h_range (x : B) (hx : x ∈ range e) : (1 + c • e) x = (1 + c) • x := by
    simp [he.mem_range_iff.1 hx, add_smul]
  have h_stable (x : B) (hx : x ∈ range e) : (1 + c • e) x ∈ range e := by
    simpa only [h_range x hx] using Submodule.smul_mem _ (1 + c) hx
  have h_restrict : (1 + c • e).restrict h_stable = (1 + c) • 1 := by
    ext x
    simpa using h_range x x.2
  have h_quotient : (range e).mapQ (range e) (1 + c • e) h_stable = 1 := by
    ext x
    simp
  simp [det_eq_det_mul_det (range e) _ h_stable, h_restrict, h_quotient, det_smul]

end GenEigenspace

variable {B B' : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B]
  [NormedAddCommGroup B'] [InnerProductSpace ℂ B']
variable {d c : ℝ}

/-- The line relations among operators `T⁺ = Tp`, `T⁻ = Tm`, `e` and `A`: `T⁻` is the adjoint of
`T⁺`, `e` is idempotent, `T⁺ T⁻ = d (1 + c e)` with `c, d > 0`, and `A` commutes with `T⁺` and
`T⁻`. They are meant for the stabiliser of a line in `GL_n(𝒪)`, `𝒪` a local ring with residue
field of order `q`: there `e` is the mean over `GL_n(𝒪)` (whence `mean` in the names of the
lemmas), `d = q ^ (n - 2)` and `c = q ^ n - 1`. -/
structure LineRelation (d c : ℝ) (A Tp Tm e : End ℂ B) : Prop where
  /-- The constant `d` is positive. -/
  d_pos : 0 < d
  /-- The constant `c` is positive. -/
  c_pos : 0 < c
  /-- `e` is idempotent. -/
  idem : IsIdempotentElem e
  /-- `T⁻` is the adjoint of `T⁺`. -/
  adjoint : ∀ x y : B, ⟪Tp x, y⟫_ℂ = ⟪x, Tm y⟫_ℂ
  /-- `T⁺ T⁻ = d (1 + c e)`. -/
  mul_eq : Tp * Tm = (d : ℂ) • (1 + (c : ℂ) • e)
  /-- `A` commutes with `T⁺`. -/
  commute_plus : Commute A Tp
  /-- `A` commutes with `T⁻`. -/
  commute_minus : Commute A Tm

namespace LineRelation

variable {A Tp Tm e : End ℂ B} {A' Tp' Tm' e' : End ℂ B'}

lemma mean_eq (h : LineRelation d c A Tp Tm e) :
    e = (c : ℂ)⁻¹ • ((d : ℂ)⁻¹ • (Tp * Tm) - 1) := by
  rw [h.mul_eq, inv_smul_smul₀ (Complex.ofReal_ne_zero.2 h.d_pos.ne'), add_sub_cancel_left,
    inv_smul_smul₀ (Complex.ofReal_ne_zero.2 h.c_pos.ne')]

/-- Under the line relations, `A` commutes with `e`, which is a polynomial in `T⁺ T⁻`. -/
lemma commute_mean (h : LineRelation d c A Tp Tm e) : Commute A e := by
  rw [h.mean_eq]
  exact (((h.commute_plus.mul_right h.commute_minus).smul_right _).sub_right
    (.one_right A)).smul_right _

/-- Under the line relations, a subspace that is stable under `T⁺` and `T⁻` is stable under `e`,
as `e` is a linear combination of `T⁺ T⁻` and the identity. -/
lemma mapsTo_mean (h : LineRelation d c A Tp Tm e) {H : Submodule ℂ B}
    (h_plus : ∀ x ∈ H, Tp x ∈ H) (h_minus : ∀ x ∈ H, Tm x ∈ H) : ∀ x ∈ H, e x ∈ H := by
  intro x hx
  simpa [h.mean_eq] using H.smul_mem _ (H.sub_mem (H.smul_mem _ (h_plus _ (h_minus x hx))) hx)

/-- The line relations (`T⁺`, `T⁻` adjoint, `T⁺ T⁻ = d (1 + c e)`, `A` commuting with both) pass
to a subspace that is stable under `A`, `T⁺` and `T⁻`. -/
lemma restrict (h : LineRelation d c A Tp Tm e) {H : Submodule ℂ B} (hA : ∀ x ∈ H, A x ∈ H)
    (h_plus : ∀ x ∈ H, Tp x ∈ H) (h_minus : ∀ x ∈ H, Tm x ∈ H) :
    LineRelation d c (A.restrict hA) (Tp.restrict h_plus) (Tm.restrict h_minus)
      (e.restrict (h.mapsTo_mean h_plus h_minus)) where
  d_pos := h.d_pos
  c_pos := h.c_pos
  idem := by
    ext x
    simpa using LinearMap.congr_fun h.idem.eq x
  adjoint x y := by simpa only [Submodule.coe_inner, restrict_apply] using h.adjoint x y
  mul_eq := by
    ext x
    simpa using LinearMap.congr_fun h.mul_eq x
  commute_plus := restrict_commute h.commute_plus hA h_plus
  commute_minus := restrict_commute h.commute_minus hA h_minus

/-- The line relations (`T⁺`, `T⁻` adjoint, `T⁺ T⁻ = d (1 + c e)`, `A` commuting with both) hold
for the restrictions of `A`, `T⁺`, `T⁻` and `e` to the generalised eigenspace of `A` for `α`. -/
lemma restrict_maxGenEigenspace (h : LineRelation d c A Tp Tm e) (α : ℂ) :
    LineRelation d c (restrictGenEigenspace (T := A) (.refl A) α)
      (restrictGenEigenspace (T := Tp) h.commute_plus α)
      (restrictGenEigenspace (T := Tm) h.commute_minus α)
      (restrictGenEigenspace (T := e) h.commute_mean α) :=
  h.restrict (fun _ hx ↦ End.mapsTo_maxGenEigenspace_of_comm (.refl A) α hx)
    (fun _ hx ↦ End.mapsTo_maxGenEigenspace_of_comm h.commute_plus α hx)
    (fun _ hx ↦ End.mapsTo_maxGenEigenspace_of_comm h.commute_minus α hx)

variable [Module.Finite ℂ B] [Module.Finite ℂ B']

/-- For operators with `T⁻` adjoint to `T⁺` and `T⁺ T⁻ = d (1 + c e)`, `e` idempotent, one has
`|det T⁺| ^ 2 = det (T⁺ T⁻) = d ^ dim B * (1 + c) ^ rank e`. -/
lemma norm_det_sq (h : LineRelation d c A Tp Tm e) :
    ‖Tp.det‖ ^ 2 = d ^ finrank ℂ B * (1 + c) ^ finrank ℂ (range e) := by
  have h_adjoint : Tp.adjoint = Tm := by
    rw [(eq_adjoint_iff Tp Tm).2 h.adjoint, adjoint_adjoint]
  apply Complex.ofReal_injective
  calc _ = (Tm * Tp).det := by
        rw [← normDet_eq_norm_det, ← h_adjoint]
        exact normDet_sq Tp
    _ = (Tp * Tm).det := by rw [map_mul, map_mul, mul_comm]
    _ = (d : ℂ) ^ finrank ℂ B * (1 + c) ^ finrank ℂ (range e) := by
      rw [h.mul_eq, det_smul, det_one_add_smul_of_isIdempotentElem h.idem]
    _ = (d ^ finrank ℂ B * (1 + c) ^ finrank ℂ (range e) : ℝ) := by norm_cast

lemma det_ne_zero (h : LineRelation d c A Tp Tm e) : Tp.det ≠ 0 := by
  refine norm_ne_zero_iff.1 (ne_zero_pow two_ne_zero ?_)
  rw [h.norm_det_sq]
  have := h.d_pos
  have := h.c_pos
  positivity

/-- Let `A, T⁺, T⁻, e` and `A', T⁺', T⁻', e'` satisfy the line relations (`T⁺`, `T⁻` adjoint,
`T⁺ T⁻ = d (1 + c e)`) for the same `c, d > 0`. If `T⁺` and `T⁺'` have the same characteristic
polynomial, then `e` and `e'` have the same rank: the polynomial gives the dimension and
`det T⁺`, hence the rank. -/
lemma finrank_range_eq_of_charpoly_eq (h : LineRelation d c A Tp Tm e)
    (h' : LineRelation d c A' Tp' Tm' e') (h_charpoly : Tp.charpoly = Tp'.charpoly) :
    finrank ℂ (range e) = finrank ℂ (range e') := by
  have h_dim : finrank ℂ B = finrank ℂ B' := by
    rw [← Tp.charpoly_natDegree, h_charpoly, Tp'.charpoly_natDegree]
  have h_det : Tp.det = Tp'.det := by
    rw [det_eq_sign_charpoly_coeff, det_eq_sign_charpoly_coeff, h_dim, h_charpoly]
  have h_pow : (1 + c) ^ finrank ℂ (range e) = (1 + c) ^ finrank ℂ (range e') :=
    mul_left_cancel₀ (pow_pos h.d_pos (finrank ℂ B')).ne'
      (by rw [← h'.norm_det_sq, ← h_det, h.norm_det_sq, h_dim])
  exact pow_right_injective₀ (add_pos one_pos h.c_pos) (lt_add_of_pos_right 1 h.c_pos).ne' h_pow

/-- Let `A, T⁺, T⁻, e` and `A', T⁺', T⁻', e'` satisfy the line relations (`T⁺`, `T⁻` adjoint,
`T⁺ T⁻ = d (1 + c e)`, `A` commuting with both) for the same `c, d > 0`. If the traces of
`A ^ (l + 1) * T⁺ ^ (i + 1)` and `A' ^ (l + 1) * T⁺' ^ (i + 1)` agree for all `l, i`, then for
each non-zero `α` the idempotents `e` and `e'` have the same rank on the generalised eigenspaces
of `A` and `A'` for `α`. -/
lemma finrank_range_restrictGenEigenspace_eq (h : LineRelation d c A Tp Tm e)
    (h' : LineRelation d c A' Tp' Tm' e')
    (h_trace : ∀ l i : ℕ,
      trace ℂ B (A ^ (l + 1) * Tp ^ (i + 1)) = trace ℂ B' (A' ^ (l + 1) * Tp' ^ (i + 1)))
    {α : ℂ} (hα : α ≠ 0) :
    finrank ℂ (range (restrictGenEigenspace (T := e) h.commute_mean α)) =
      finrank ℂ (range (restrictGenEigenspace (T := e') h'.commute_mean α)) := by
  -- On the generalised eigenspaces for `α` the operators `T⁺` are invertible, so the traces of
  -- their positive powers determine their characteristic polynomials.
  have h_charpoly : (restrictGenEigenspace h.commute_plus α).charpoly =
      (restrictGenEigenspace h'.commute_plus α).charpoly := by
    refine charpoly_eq_of_trace_pow_succ_eq (h.restrict_maxGenEigenspace α).det_ne_zero
      (h'.restrict_maxGenEigenspace α).det_ne_zero fun i ↦ ?_
    rw [restrictGenEigenspace_pow, restrictGenEigenspace_pow]
    exact trace_restrictGenEigenspace_eq_of_ne_zero _ _ (fun l ↦ h_trace l i) hα
  exact (h.restrict_maxGenEigenspace α).finrank_range_eq_of_charpoly_eq
    (h'.restrict_maxGenEigenspace α) h_charpoly

/-- Let `A, T⁺, T⁻, e` and `A', T⁺', T⁻', e'` satisfy the line relations (`T⁺`, `T⁻` adjoint,
`T⁺ T⁻ = d (1 + c e)`, `A` commuting with both) for the same `c, d > 0`. If the traces of
`A ^ (l + 1) * T⁺ ^ (i + 1)` and `A' ^ (l + 1) * T⁺' ^ (i + 1)` agree for all `l, i`, then so do
the traces of `A * e` and `A' * e'`, which are those of `A` and `A'` on the ranges of `e` and
`e'`. -/
theorem trace_mul_mean_eq (h : LineRelation d c A Tp Tm e) (h' : LineRelation d c A' Tp' Tm' e')
    (h_trace : ∀ l i : ℕ,
      trace ℂ B (A ^ (l + 1) * Tp ^ (i + 1)) = trace ℂ B' (A' ^ (l + 1) * Tp' ^ (i + 1))) :
    trace ℂ B (A * e) = trace ℂ B' (A' * e') := by
  -- Both traces are sums over a finite set containing the eigenvalues of `A` and `A'`: the term of
  -- `α` is `α` times the rank of the idempotent on the generalised eigenspace for `α`.
  obtain ⟨S, -, hS, hS'⟩ := exists_finset_maxGenEigenspace_eq_bot A A' 0
  rw [← pow_one A, ← pow_one A', trace_pow_mul_eq_sum h.commute_mean hS,
    trace_pow_mul_eq_sum h'.commute_mean hS']
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  obtain rfl | hα := eq_or_ne α 0
  · rw [pow_one, zero_mul, zero_mul]
  -- The trace of an idempotent is its rank.
  simp only [(h.restrict_maxGenEigenspace α).idem.isProj_range.trace,
    (h'.restrict_maxGenEigenspace α).idem.isProj_range.trace,
    h.finrank_range_restrictGenEigenspace_eq h' h_trace hα]

end LineRelation

end New

end
