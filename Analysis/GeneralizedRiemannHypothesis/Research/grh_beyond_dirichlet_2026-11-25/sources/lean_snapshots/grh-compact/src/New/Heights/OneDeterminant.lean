import New.Heights.Heights

/-! Few translates nearly span; height of one Gram determinant. If translates of a linear map spread
modulo every subspace, a logarithm times the least possible number of them nearly span the target,
and for a family completed to a basis the ratio of twisted to untwisted volume has height at most
the Gram size plus twice the index plus a cost per added vector. Greedy covering with a logarithmic
loss and size-versus-divisibility bounds for a determinant are known. Related work: Wolsey, Greedy
algorithm for the submodular set covering problem, 1982; Bost, Algebraic leaves of algebraic
foliations over number fields, 2001; Laurent, Linear forms in two logarithms and interpolation
determinants, 1994.

Part of: Second moment of the Poincaré series with constant one (see New.Filling.Moments).

This file: Positive-type functions avoid singular minors; Hilbert-Schmidt variance inequality giving
spread. Few translates nearly span; height bound for a ratio of Gram determinants. -/

open Module InnerProductSpace Finset EuclideanSpace Complex Matrix WithLp Fintype AddChar Submodule
  OrthonormalBasis LinearMap
variable {G H k n m} [Group G] [Fintype G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Field k]
  [Fintype n] [Fintype m] (b : OrthonormalBasis m ℂ H) {u v : G → H}

lemma inner_sum_sum_eq_card_mul f (h : ∀ a b, ⟪u a, v b⟫_ℂ = f (a⁻¹ * b)) : ⟪∑ a, u a, ∑ a, v a⟫_ℂ =
  card G * univ.sum f := by simp [↓sum_inner, inner_sum, h, (Group.mulLeft_bijective _).sum_comp]

/-- Let π represent a finite group on 𝔽_q^n, π' be contragredient, A, A' n × m matrices, Θ ≥ 0
of positive type. If the fixers of Av, A'v (v ≠ 0) have Θ-mass ≤ Y, then q·Θ{det A'ᵀπ(s)A =
0} ≤ 2Θ(G) + q^(m+n/2) Y. -/
lemma card_mul_sum_det_le [Fintype k] (π : G →* GL n k) (A : _ → Matrix n m k) {Θ} (h0 : ∀ s, 0 ≤ Θ
  s) (hu : ∀ a b, ⟪u a, u b⟫_ℂ = Θ (a⁻¹ * b)) Y (hY : 0 ≤ Y) (h : ∀ b, ∀ v ≠ 0, ∑ s with A b *ᵥ v =
  cond b invTransposeGL 1 (π s) • A b *ᵥ v, Θ s ≤ Y) : card k * ∑ s with ((A true)ᵀ *
  (π s).1 * A false).det = 0, Θ s ≤ 2 * univ.sum Θ + card k ^ card m * √(card k ^ card n) * Y := by
  set r := √_
  obtain ⟨ψ, p⟩ : ∃ _, _ := ⟨_, FiniteField.primitiveChar_to_Complex_isPrimitive k⟩
  have N {c : (n → k) → EuclideanSpace ℂ (n → k)} (h : Orthonormal ℂ c) {σ : MulAut _} x :
      ∑ s with x = σ (π s) • x, Θ s = ‖∑ a, c (σ (π a) • x) ⊗ₜ[ℂ] u a‖ ^ 2 / card G
  rw [@norm_sq_eq_re_inner ℂ, inner_sum_sum_eq_card_mul (ofReal ∘ _)]
  simpa using sum_filter ..
  simp [*, orthonormal_iff_ite.1, apply_ite ofReal, mul_smul, eq_inv_smul_iff]
  let W y v s := ψ (y ᵥ* (A true)ᵀ ᵥ* π s ᵥ* A false ⬝ᵥ v) * Θ s
  apply ((sum_mono fun y ↦ univ.expect_le_expect fun v _ ↦ (?_ : re (∑ s, W y v s) ≤
    ite (y = 0) (∑ s, Θ s) 0 + ite (v = 0) (∑ s, Θ s) 0 + r * Y)).trans _).trans'
  simp [W, -ite_mul, sum_comm, mul_sum, sum_filter, apply_ite, ↓← re_expect, ← sum_mul, ← mul_assoc,
    expect, NNRat.smul_def, sum_addChar_dotProduct p]
  gcongr; repeat' split
  cases exists_vecMul_eq_zero_iff.2 ‹_›
  grw [← card_univ, card_le_card_of_injOn _ _ (smul_left_injective _ (by tauto)).injOn]
  on_goal -1 => apply flip id (add_le_add (h true y _) (h false v _))
                grw [@N fun x ↦ toLp 2 fun ζ ↦ ψ (-x ⬝ᵥ ζ) / r, N orthonormal_single, ← add_div,
    ← two_mul_le_add_sq, mul_assoc, ← @re_inner_le_norm ℂ, inner_sum_sum_eq_card_mul (W y v · / r)]
  all_goals simp [*, smul_vecMul, mul_nonneg, expect_add_distrib, NNRat.smul_def, W, r, add_nonneg,
    sum_nonneg', inner, field, vecMul_mulVec, ← Matrix.mul_assoc, orthonormal_iff_ite, two_mul,
    invTransposeGL, dotProduct_mulVec, div_mul_div_comm, ← map_neg_eq_conj, ← map_add_eq_mul,
    ← ofReal_mul, transposeGL,
    add_assoc, ← sum_div, neg_add_eq_sub, ← sub_dotProduct, sum_addChar_dotProduct, Units.smul_def]

/-- For a finite family of vectors v_x in H, the tensor ∑_x v̄_x ⊗ v_x, where v̄_x is the vector
of conjugated coordinates of v_x in the orthonormal basis b. -/
noncomputable def dyadSum (v : n → H) := ∑ x, toLp 2 (⟪v x, b ·⟫_ℂ) ⊗ₜ[ℂ] v x

@[simp] lemma inner_dyadSum {l} [Fintype l] (v : n → H) (w : l → H) : ⟪dyadSum b v, dyadSum b w⟫_ℂ =
  ∑ x, ∑ y, ‖⟪w y, v x⟫_ℂ‖ ^ 2 := by simp [dyadSum, ← mul_conj', inner, b.sum_inner_mul_inner,
  @sum_comm n]

/-- Let P : ℂⁿ → H and R : H → H be linear, with Pv − RPv ∈ A for all v ∈ U. Then dim U − ∑_x
‖(P*P − 1)e_x‖ ≤ ‖p_A P‖² + ‖RP‖² in Hilbert–Schmidt norms, p_A the orthogonal projection to
A (first norm written with `dyadSum`). -/
lemma finrank_sub_le_re_inner_dyadSum [FiniteDimensional ℂ H] (P : EuclideanSpace ℂ n →ₗ[ℂ] H) (R :
  End ℂ H) (U A : Submodule ℂ _) {ε} (k : ∑ x, ‖(P.adjoint ∘ₗ P - 1) (.single x 1)‖ ≤ ε)
  (h : ∀ v ∈ U, P v - R (P v) ∈ A) : finrank ℂ U - ε - ∑ x, ‖R (P (.single x 1))‖ ^ 2 ≤
  re ⟪dyadSum b (P <| .single · 1), dyadSum b (stdOrthonormalBasis ℂ A ·)⟫_ℂ := by
  obtain u := stdOrthonormalBasis ℂ U, congrArg re (trace_comp_comm' U.subtype
    (U.orthogonalProjectionOnto ∘ₗ (1 - P.adjoint ∘ₗ P))),
    ((stdOrthonormalBasis ℂ A).sum_sq_norm_inner_right <| orthogonalProjectionOnto _ ·)
  have B (T : End ℂ H) : ∑ i, ‖T (P (basisFun n ℂ i))‖ ^ 2 ≥ ∑ j, ‖T (P (u j))‖ ^ 2
  simp_rw [← b.sum_sq_norm_inner_left, ← adjoint_inner_right, @sum_comm m, sum_sq_norm_inner_right]
  grw [Orthonormal.sum_inner_products_le]; exact u.orthonormal
  simp_all [trace_eq_sum_inner _ (basisFun ..), trace_eq_sum_inner _ u, ← ofReal_pow, norm_sub_rev,
    norm_coe, inner_sub_right, inner_single_left, adjoint_inner_right, -map_sub, sub_eq_iff_eq_add']
  grw (transparency := .all) [re_le_norm, PiLp.norm_apply_le, norm_starProjection_apply_le, ← B,
    ← B A.starProjection, ← sum_add_distrib, ← Aᗮ.norm_starProjection_apply_le (R _)]
  gcongr
  erw [← Aᗮ.starProjection.sub_mem_ker_iff.1 (by aesop), ← norm_sq_eq_add_norm_sq_projection]

open Real NormedField
variable {Θ V W S : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] [Module.Finite ℂ V] [Module.Finite ℂ W]

/-- For every subspace F of W some index s has dim (B s)⁻¹F ≤ ((1 + φ)/2 + η)·dim V, where φ =
dim F / dim W. -/
def IsSpread {W} [AddCommMonoid W] [Module ℂ W] (B : S → V →ₗ[ℂ] W) η :=
  ∀ F : Submodule .., let φ : ℝ := finrank ℂ F / finrank ℂ W
  ∃ s, finrank ℂ (comap (B s) F) ≤ ((1 + φ) / 2 + η) * finrank ℂ V

/-- Few translates. If η > 0, V ≠ 0 and B is spread (`IsSpread` B η), some finite set t of indices
has #t·dim V ≤ 5·dim W·log(1 + 1/η), and the images of the B s, s ∈ t, span dimension ≥ (1 − 4η)·dim
W. -/
lemma exists_few_translates {B : Θ → V →ₗ[ℂ] W} {η} (hη : 0 < η) (h : IsSpread B η) [Nontrivial V] :
    ∃ t, #t * finrank ℂ V ≤ 5 * finrank ℂ W * Real.log (1 + η⁻¹) ∧
    (1 - 4 * η) * finrank ℂ W ≤ finrank ℂ ↥(⨆ s ∈ t, (B s).range) := by
  let T (t : Finset Θ) := ⨆ s ∈ t, (B s).range
  let ψ (F : Submodule ℂ W) := 5 * finrank ℂ W * Real.log (1 + finrank ℂ (W ⧸ F) / finrank ℂ W / η)
  refine (exists_maximalFor_of_wellFoundedGT (fun t ↦ #t * finrank ℂ V + ψ (T t) ≤ _) T ⟨∅, by
    simp [ψ]; grw [finrank_quotient_le, div_self_le_one]; simp⟩).imp fun t ⟨ht, m⟩ ↦
    (h (T t)).rec fun s _ ↦ ⟨ht.trans' (by bound), ?_⟩; by_contra
  obtain ⟨_ | _, m⟩ := em (finrank ℂ W = 0), @m (insert s t), (T t).finrank_quotient_add_finrank,
    ((T t).mkQ ∘ₗ B s).index_eq_of_finiteDimensional <;> simp_all [T, index, t.iSup_insert]
  grw [range_comp, ker_comp, ker_mkQ, card_insert_le] at *
  have : ψ (T t ⊔ (B s).range) - ψ (T t) ≤ -finrank ℂ V
  grw [← mul_sub, ← log_div, log_le_sub_one_of_pos] <;> try positivity
  rify [field, (quotientQuotientEquivQuotientSup ..).finrank_eq] at *; nlinarith
  simpa [T, m (by grind), finrank_pos.ne']

/-- In a finite-dimensional complex vector space V, a linearly independent family y of n vectors
extends to a basis by adding finitely many members of a spanning set S. -/
lemma exists_extend_basis_of_span_eq_top {n S} {y : Fin n → V} (i : LinearIndependent ℂ y) (h :
  span ℂ S = ⊤) :
  ∃ k z, (∀ a : Fin k, z a ∈ S) ∧ LinearIndependent ℂ (y ⊕ᵥ z) ∧ finrank ℂ V = n + k := by
  choose w a _ j using exists_fun_fin_finrank_span_eq ℂ ((span ℂ (.range y)).mkQ '' S)
  choose z hz e using a
  exists _, z, hz, (linearIndependent_span i).sumElim_of_quotient z (funext e ▸ j :)
  rw [span_image, h, ← range_eq_map, range_mkQ, ← finrank_quotient_add_finrank,
    finrank_span_eq_card i]; simp; lia

/-- One determinant. Let x be a basis of W, u o injective, all conjugates of the Gram determinant of
u o ∘ x of modulus ≤ exp α, γ nonzero with |γ|⁻² of height ≤ g, all finite sums of e at most δ. If
for all ι at l and j : ℂ → ℂ_l the pairing of Λ ι (j∘conj) with Λ ι j is j-integral and a complex
matrix m with |j(det m)| ≥ exp(−e l)·|j(γ ι)|^k recombines u (θ ι) ∘ x into Λ ι j, then the
squared-volume ratios of u (θ ι) to u o have height ≤ α + 2δ + kg. -/
lemma one_determinant {θ : _ → Θ} {H : Θ → Type} [∀ ϑ, NormedAddCommGroup (H ϑ)] [∀ ϑ,
  InnerProductSpace ℂ (H ϑ)] (u : ∀ ϑ, W →ₗ[ℂ] H ϑ) {o} (hu : (⇑(u o)).Injective) [Fintype S] {x :
  S → W} (i : LinearIndependent ℂ x) (hk : finrank ℂ W = card S) {α δ g} (hα : ∀ σ : ℂ ≃+* ℂ, ‖σ
  (gram ℂ (u o ∘ x)).det‖ ≤ Real.exp α) {γ : _ → ℂ} (γ0 : ∀ ι, γ ι ≠ 0) (hγ : HeightLe g fun ι ↦ (‖γ
  ι‖ ^ 2 :)⁻¹) {e : ℕ → ℝ} (he : ∀ U, ∑ l ∈ U, e l ≤ δ) (Λ : ∀ ι : PrimePadicIso, (ℂ →+* ℂ_[ι.1]) →
  Set (H (θ ι))) (k : ℕ) (w : ∀ ι j, ∀ x ∈ Λ ι (j.comp (starRingEnd ℂ)), ∀ y ∈ Λ ι j, ‖j ⟪x, y⟫_ℂ‖ ≤
  1) (l : ∀ ι j, ∃ m, Real.exp (-e ι.1) * ‖j (γ ι)‖ ^ k ≤ ‖j (det m)‖ ∧ ∀ i, ∑ l, m i l • u _ (x
  l) ∈ Λ ι j) : HeightLe (α + 2 * δ + k * g) fun ι ↦ (u (θ ι)).normDet ^ 2 / (u o).normDet ^ 2 := by
  have Z := det_gram_ne_zero_iff_linearIndependent.2 (i.map_injOn _ hu.injOn)
  refine (IsUnit.div_mul_cancel (by simp [Pi.isUnit_iff, *]) _).subst
    (.mul ⟨_, α, 2 • e, Z, hα, fun ι ↦ ?_, by simp [← mul_sum, *]⟩ (hγ.pow k))
  -- at `ι`, the products of the integral combinations for `j ∘ conj` and for `j` are integral
  choose m a b using l ι
  let j := complexToCp ι.2
  have : ‖j (_ᴴᵀ * (_ * (m j)ᵀ)).det‖ ≤ 1 := IsIntMatrix.det_mem (R := valuation.integer.comap j)
    fun i k ↦ star_dotProduct_gram_mulVec (u _ ∘ x) (m _ i) _ ▸ w ι j _ (b ..) _ (b ..)
  -- the Gram determinant is the squared volume (`⟨.neg _⟩`: minus the standard orthonormal basis)
  simp [gram, ← by simpa [normDet_comp_of_finrank_eq, gram, *] using (u · ∘ₗ
    (PiLp.basisFun 2 ..).constr ℂ x |>.normDet_sq_eq_det_gram ⟨.neg _⟩), ← (γ ι).conj_mul'] at *
  grw [← j.comp_apply, ← a, ← a] at *
  simp [j, Z, field, mul_pow, Real.exp_neg, ← Real.exp_nsmul] at *; bound

