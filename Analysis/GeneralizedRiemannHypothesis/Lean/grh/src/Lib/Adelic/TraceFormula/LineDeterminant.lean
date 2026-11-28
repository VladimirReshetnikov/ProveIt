import Lib.General.LinearAlgebra.Eigenvalues

/-!
# Traces on the range of an idempotent from traces of a raising operator

Let `T⁺`, `T⁻` be adjoint operators on a finite-dimensional complex inner product space, with
`T⁺ * T⁻ = d • (1 + c • e)`, `d, c > 0`, and `e` idempotent. If `A` commutes with both operators,
then its trace on the range of `e` is determined by the traces of `A * T⁺ ^ j` for positive `j`.
When comparing two spaces it suffices to take `j` up to the number of distinct eigenvalues in the
union of their raising-operator spectra (`LineRelation.trace_mul_mean_eq_of_positive_moments`).

On a generalized eigenspace of `A`, the determinant relation expresses the rank of `e` as a sum of
logarithms over the roots of the characteristic polynomial of `T⁺`, counted with multiplicity.
Interpolate these values by a common polynomial with zero constant term. The trace of that
polynomial in `T⁺` agrees with the rank on every generalized eigenspace, giving the weighted trace.
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

/-- Traces of all powers determine the characteristic polynomial. -/
lemma charpoly_eq_of_trace_pow_eq (h_trace : ∀ l : ℕ, trace ℂ B (A ^ l) = trace ℂ B' (A' ^ l)) :
    A.charpoly = A'.charpoly := by
  let b := Module.finBasis ℂ B
  let b' := Module.finBasis ℂ B'
  rw [← charpoly_toMatrix A b, ← charpoly_toMatrix A' b']
  simpa using charpoly_eq_mul_of_trace_pow_add (toMatrix b b A) (B := toMatrix b' b' A')
    (∅ : Finset ℂ) id (fun l ↦ by simp [toMatrix_pow, ← trace_eq_matrix_trace, h_trace])

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

end LineRelation

/-- Sum the logarithmic weights over the nonzero roots, including their multiplicities. -/
private lemma sum_spectral_logs (s : Multiset ℂ) (hs : 0 ∉ s) (d c : ℝ) (hd : 0 < d) :
    (s.map fun z ↦ Real.log (‖z‖ ^ 2 / d) / Real.log (1 + c)).sum =
      (Real.log (‖s.prod‖ ^ 2) - s.card * Real.log d) / Real.log (1 + c) := by
  simp_rw [div_eq_mul_inv _ (Real.log (1 + c)), Multiset.sum_map_mul_right]
  congr 1
  have hlog := Real.log_multiset_prod (s := s.map fun z ↦ ‖z‖ ^ 2 / d) (by
    simpa using fun z (hz : z ∈ s) ↦ And.intro (fun h : z = 0 ↦ hs (h ▸ hz)) hd.ne')
  rw [Multiset.map_map, Function.comp_def] at hlog
  have hn : (s.map norm).prod = ‖s.prod‖ := (map_multiset_prod (normHom : ℂ →*₀ ℝ) s).symm
  rw [← hlog, Multiset.prod_map_div, Multiset.prod_map_pow, hn]
  simp [Real.log_div (pow_ne_zero _ (norm_ne_zero_iff.mpr (Multiset.prod_ne_zero hs)))
    (pow_ne_zero _ hd.ne'), Real.log_pow]

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Module.Finite ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [Module.Finite ℂ V']
  {A T U e : End ℂ V} {d c : ℝ}

private lemma trace_aeval_eq_root_sum (T : End ℂ V) (p : ℂ[X]) :
    trace ℂ V (aeval T p) = (T.charpoly.roots.map p.eval).sum := by
  let b := Module.finBasis ℂ V
  rw [trace_eq_matrix_trace ℂ b, ← charpoly_toMatrix T b]
  exact (congrArg Matrix.trace (aeval_algHom_apply (toMatrixAlgEquiv b) T p).symm).trans
    (trace_aeval_eq_sum_roots _ _)

/-- When a polynomial interpolates the logarithmic weights, its trace is the rank of the mean. -/
private lemma LineRelation.trace_aeval_eq_rank (h : LineRelation d c A T U e) (p : ℂ[X])
    (hp : ∀ z ∈ T.charpoly.roots, p.eval z = (Real.log (‖z‖ ^ 2 / d) / Real.log (1 + c) : ℝ)) :
    trace ℂ V (aeval T p) = finrank ℂ (range e) := by
  have hdet : T.det = T.charpoly.roots.prod :=
    End.det_eq_prod_roots_charpoly_of_splits (IsAlgClosed.splits _)
  have hz : 0 ∉ T.charpoly.roots := by
    intro hz
    exact h.det_ne_zero (hdet.trans (Multiset.prod_eq_zero hz))
  have hn := (IsAlgClosed.splits T.charpoly).natDegree_eq_card_roots
  rw [T.charpoly_natDegree] at hn
  let g (z : ℂ) := Real.log (‖z‖ ^ 2 / d) / Real.log (1 + c)
  have hcast (s : Multiset ℂ) : (s.map fun z ↦ (g z : ℂ)).sum = ↑((s.map g).sum) := by
    simpa [Multiset.map_map, Function.comp_def] using (map_multiset_sum Complex.ofRealHom (s.map g)).symm
  rw [trace_aeval_eq_root_sum, Multiset.map_congr rfl hp, hcast]
  norm_cast
  rw [sum_spectral_logs _ hz d c h.d_pos, ← hdet, ← hn, h.norm_det_sq]
  have hpw : (1 + c) ^ finrank ℂ (range e) ≠ 0 := pow_ne_zero _ (by have := h.c_pos; positivity)
  rw [Real.log_mul (pow_ne_zero _ h.d_pos.ne') hpw, Real.log_pow, Real.log_pow,
    add_sub_cancel_left, mul_div_cancel_right₀ _ (Real.log_pos (by have := h.c_pos; linarith)).ne']

private noncomputable abbrev eigSupport (A : End ℂ V) : Finset ℂ :=
  (Submodule.finite_ne_bot_of_iSupIndep A.independent_maxGenEigenspace).toFinset

private lemma trace_mul_eq_sum_gen {A E : End ℂ V} (h : Commute A E) :
    trace ℂ V (A * E) = ∑ μ ∈ eigSupport A,
      μ * trace ℂ (A.maxGenEigenspace μ) (restrictGenEigenspace h μ) := by
  have hd := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    A.independent_maxGenEigenspace A.iSup_maxGenEigenspace_eq_top
  rw [trace_eq_sum_trace_restrict' hd (Submodule.finite_ne_bot_of_iSupIndep A.independent_maxGenEigenspace)
    (End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl A).mul_right h))]
  exact Finset.sum_congr rfl fun μ _ ↦ trace_restrictGenEigenspace_mul h μ

private lemma trace_mul_poly_eq_sum_gen (h : Commute A T) (p : ℂ[X]) :
    trace ℂ V (A * aeval T p) = ∑ μ ∈ eigSupport A,
      μ * trace ℂ (A.maxGenEigenspace μ) (aeval (restrictGenEigenspace h μ) p) := by
  induction p using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add, mul_add, hf, hg, Finset.sum_add_distrib]
  | monomial n r =>
    simp only [aeval_monomial, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul,
      trace_mul_eq_sum_gen (h.pow_right n), ← restrictGenEigenspace_pow h, Finset.mul_sum,
      mul_left_comm r]

private lemma root_mem_of_restrict {T : End ℂ V} {H : Submodule ℂ V}
    (hH : ∀ x ∈ H, T x ∈ H) {z : ℂ} (hz : z ∈ (T.restrict hH).charpoly.roots) :
    z ∈ T.charpoly.roots := by
  rw [Polynomial.mem_roots (T.restrict hH).charpoly_monic.ne_zero,
    ← End.hasEigenvalue_iff_isRoot_charpoly] at hz
  rw [Polynomial.mem_roots T.charpoly_monic.ne_zero, ← End.hasEigenvalue_iff_isRoot_charpoly]
  exact fun (h : T.eigenspace z = ⊥) ↦ hz (End.eigenspace_restrict_eq_bot hH (by simp [h]))

/-- A polynomial interpolating the logarithmic weights represents the mean inside traces against
any operator commuting with the raising and lowering operators. -/
lemma LineRelation.trace_mul_eq_spectral (h : LineRelation d c A T U e) (p : ℂ[X])
    (hp : ∀ z ∈ T.charpoly.roots, p.eval z = (Real.log (‖z‖ ^ 2 / d) / Real.log (1 + c) : ℝ)) :
    trace ℂ V (A * e) = trace ℂ V (A * aeval T p) := by
  rw [trace_mul_eq_sum_gen h.commute_mean, trace_mul_poly_eq_sum_gen h.commute_plus]
  refine Finset.sum_congr rfl fun μ _ ↦ congrArg (μ * ·) ?_
  rw [(h.restrict_maxGenEigenspace μ).idem.isProj_range.trace]
  exact ((h.restrict_maxGenEigenspace μ).trace_aeval_eq_rank p
    (fun z hz ↦ hp z (root_mem_of_restrict _ hz))).symm

variable {A' T' U' e' : End ℂ V'}

/-- To compare the traces of the means, it suffices to know the positive raising-operator
moments up to the size of the union of the two distinct spectra. Only one power of the test
operator occurs. -/
theorem LineRelation.trace_mul_mean_eq_of_positive_moments
    (h : LineRelation d c A T U e) (h' : LineRelation d c A' T' U' e')
    (hmom : ∀ k < (T.charpoly.roots.toFinset ∪ T'.charpoly.roots.toFinset).card,
      trace ℂ V (A * T ^ (k + 1)) = trace ℂ V' (A' * T' ^ (k + 1))) :
    trace ℂ V (A * e) = trace ℂ V' (A' * e') := by
  classical
  let S := T.charpoly.roots.toFinset ∪ T'.charpoly.roots.toFinset
  let f (z : ℂ) : ℂ := (Real.log (‖z‖ ^ 2 / d) / Real.log (1 + c) : ℝ)
  -- Factoring out X gives only positive powers, including when the interpolation set is empty.
  let q := Lagrange.interpolate S id (fun z ↦ f z / z)
  have heval {z : ℂ} (hz : z ∈ S) : (X * q).eval z = f z := by
    rw [eval_mul, eval_X, show q.eval z = f z / z from
      Lagrange.eval_interpolate_at_node _ Function.injective_id.injOn hz]
    by_cases h0 : z = 0
    · simp [h0, f]
    · rw [mul_comm, div_mul_cancel₀ _ h0]
  have hdeg : q.degree < S.card := Lagrange.degree_interpolate_lt _ Function.injective_id.injOn
  rw [h.trace_mul_eq_spectral (X * q) (fun z hz ↦ heval (by simp [S, hz])),
    h'.trace_mul_eq_spectral (X * q) (fun z hz ↦ heval (by simp [S, hz]))]
  simp only [map_mul, aeval_X]
  simp only [aeval_def, eval₂_eq_sum, Polynomial.sum_def,
    ← Algebra.smul_def, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, ← pow_succ']
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [hmom k (WithBot.coe_lt_coe.mp ((le_degree_of_mem_supp k hk).trans_lt hdeg))]

namespace LineRelation

variable [Module.Finite ℂ B] [Module.Finite ℂ B']
  {A Tp Tm e : End ℂ B} {A' Tp' Tm' e' : End ℂ B'}

/-- Let `A, T⁺, T⁻, e` and `A', T⁺', T⁻', e'` satisfy the line relations (`T⁺`, `T⁻` adjoint,
`T⁺ T⁻ = d (1 + c e)`, `A` commuting with both) for the same `c, d > 0`. If the traces of
`A ^ (l + 1) * T⁺ ^ (i + 1)` and `A' ^ (l + 1) * T⁺' ^ (i + 1)` agree for all `l, i`, then so do
the traces of `A * e` and `A' * e'`, which are those of `A` and `A'` on the ranges of `e` and
`e'`. -/
theorem trace_mul_mean_eq (h : LineRelation d c A Tp Tm e) (h' : LineRelation d c A' Tp' Tm' e')
    (h_trace : ∀ l i : ℕ,
      trace ℂ B (A ^ (l + 1) * Tp ^ (i + 1)) = trace ℂ B' (A' ^ (l + 1) * Tp' ^ (i + 1))) :
    trace ℂ B (A * e) = trace ℂ B' (A' * e') := by
  exact h.trace_mul_mean_eq_of_positive_moments h' fun k _ ↦ by simpa using h_trace 0 k

end LineRelation

end New

end
