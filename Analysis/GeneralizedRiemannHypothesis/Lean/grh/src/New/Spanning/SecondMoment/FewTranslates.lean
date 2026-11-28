import Lib.Shimura.Uniformisation.HolomorphicFamilies
import New.Spanning.SecondMoment.PositiveType

/-!
# Few translates fill

Let a finite group act unitarily on `T`, let `pr₀` be the projection onto a stable subspace `T₀`,
and let `B : S → T` be linear. Suppose that `pr₀ B` is almost an isometry from below in mean square
and that the second moment of the operators `B* s B` is nearly as small as Cauchy–Schwarz allows.
Then a few translates `s pr₀ B` span almost all of `T₀`. In this file `‖A‖`, written of a linear map
`A`, is its Hilbert–Schmidt norm.

* `New.hilbertSchmidtNorm`, `New.IsNearIsometry`: the Hilbert–Schmidt norm, and the first
  hypothesis.
* `New.isSpread_of_second_moment`: for any subspace `W` of `T₀`, the preimage of `W` under some
  translate `s pr₀ B` is small, in terms of the share of `W` in `T₀` (`New.IsSpread`).
* `New.IsSpread.exists_few_le_finrank_iSup_range`: a logarithm times `dim T₀ / dim S` translates
  span almost all of `T₀`.

## Relation to the literature

Rank bounds from second moments: Welch 1974. Greedy covering with a logarithmic loss: Wolsey, Greedy
algorithm for the submodular set covering problem, 1982.
-/

open Module LinearMap Finset

open scoped InnerProductSpace

namespace New

section Spread

open Submodule

variable {Θ V : Type} [AddCommGroup V] [Module ℂ V]

/-- The maps `B s` spread: for every subspace `F` of `W`, with share `α` of the dimension, the
preimage of `F` under one of them has dimension at most `((1 + α) / 2 + η) dim V`. The share is the
quotient of the two values of `finrank`, so it is `0` if `finrank W = 0`. -/
def IsSpread {W : Type*} [AddCommMonoid W] [Module ℂ W] (B : Θ → V →ₗ[ℂ] W) (η : ℝ) : Prop :=
  ∀ F : Submodule ℂ W, let α : ℝ := finrank ℂ F / finrank ℂ W
  ∃ s : Θ, finrank ℂ (comap (B s) F) ≤ ((1 + α) / 2 + η) * finrank ℂ V

end Spread

section HilbertSchmidt

open Complex

variable {S T T' : Type}
  [NormedAddCommGroup S] [InnerProductSpace ℂ S] [FiniteDimensional ℂ S]
  [NormedAddCommGroup T] [InnerProductSpace ℂ T] [FiniteDimensional ℂ T]
  [NormedAddCommGroup T'] [InnerProductSpace ℂ T'] [FiniteDimensional ℂ T']

/-- The values of a linear map on an orthonormal basis of the source, as one vector of a Hilbert
space. Its inner product is the Hilbert–Schmidt inner product of maps. -/
noncomputable def hilbertSchmidtVector : (S →ₗ[ℂ] T) →ₗ[ℂ] PiLp 2 fun _ : Fin (finrank ℂ S) ↦
  T where
  toFun A := WithLp.toLp 2 fun i ↦ A (stdOrthonormalBasis ℂ S i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The Hilbert–Schmidt norm of a linear map. -/
noncomputable def hilbertSchmidtNorm (A : S →ₗ[ℂ] T) : ℝ := ‖hilbertSchmidtVector A‖

omit [FiniteDimensional ℂ T] in
lemma hilbertSchmidtNorm_nonneg (A : S →ₗ[ℂ] T) : 0 ≤ hilbertSchmidtNorm A := norm_nonneg _

/-- The inner product of `hilbertSchmidtVector A` and `hilbertSchmidtVector B`, the vectors of the
values of `A` and `B` on an orthonormal basis, is the trace of `A* B`: the Hilbert–Schmidt inner
product. -/
lemma inner_hilbertSchmidtVector (A B : S →ₗ[ℂ] T) :
    ⟪hilbertSchmidtVector A, hilbertSchmidtVector B⟫_ℂ = trace ℂ S (A.adjoint ∘ₗ B) := by
  rw [trace_eq_sum_inner _ (stdOrthonormalBasis ℂ S), PiLp.inner_apply]
  exact sum_congr rfl fun i _ ↦ (adjoint_inner_right A _ _).symm

lemma hilbertSchmidtNorm_sq_eq_trace (A : S →ₗ[ℂ] T) :
    ((hilbertSchmidtNorm A ^ 2 : ℝ) : ℂ) = trace ℂ S (A.adjoint ∘ₗ A) := by
  simp [← inner_hilbertSchmidtVector, hilbertSchmidtNorm, inner_self_eq_norm_sq_to_K]

/-- The squared Hilbert–Schmidt norm of `A` is the sum of `‖A (b i)‖ ^ 2` over the vectors `b i` of
any orthonormal basis `b` of `S`. -/
lemma hilbertSchmidtNorm_sq_eq_sum {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ S)
    (A : S →ₗ[ℂ] T) :
    hilbertSchmidtNorm A ^ 2 = ∑ i : ι, ‖A (b i)‖ ^ 2 := by
  apply ofReal_injective
  rw [hilbertSchmidtNorm_sq_eq_trace, trace_eq_sum_inner _ b, ofReal_sum]
  simp [inner_self_eq_norm_sq_to_K, adjoint_inner_right]

/-- The squared Hilbert–Schmidt norm is the sum of the squared moduli of the matrix entries. -/
lemma hilbertSchmidtNorm_sq_eq_sum_entries {ι κ : Type} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ S) (c : OrthonormalBasis κ ℂ T) (A : S →ₗ[ℂ] T) :
    hilbertSchmidtNorm A ^ 2 = ∑ j : κ, ∑ i : ι, ‖⟪A (b i), c j⟫_ℂ‖ ^ 2 := by
  rw [hilbertSchmidtNorm_sq_eq_sum b, sum_comm]
  exact sum_congr rfl fun i _ ↦ (c.sum_sq_norm_inner_left _).symm

lemma hilbertSchmidtNorm_adjoint (A : S →ₗ[ℂ] T) :
    hilbertSchmidtNorm A.adjoint = hilbertSchmidtNorm A := by
  rw [← sq_eq_sq₀ (hilbertSchmidtNorm_nonneg _) (hilbertSchmidtNorm_nonneg _), ← ofReal_inj,
    hilbertSchmidtNorm_sq_eq_trace,
    hilbertSchmidtNorm_sq_eq_trace, adjoint_adjoint, trace_comp_comm']

/-- If `‖A x‖ ≤ ‖B x‖` for all `x`, then the Hilbert–Schmidt norm of `A` is at most that of `B`. -/
lemma hilbertSchmidtNorm_le_of_norm_le {A : S →ₗ[ℂ] T} {B : S →ₗ[ℂ] T'}
    (h_le : ∀ x : S, ‖A x‖ ≤ ‖B x‖) :
    hilbertSchmidtNorm A ≤ hilbertSchmidtNorm B := by
  rw [← sq_le_sq₀ (hilbertSchmidtNorm_nonneg _) (hilbertSchmidtNorm_nonneg _),
    hilbertSchmidtNorm_sq_eq_sum (stdOrthonormalBasis ℂ S),
      hilbertSchmidtNorm_sq_eq_sum (stdOrthonormalBasis ℂ S)]
  exact sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (h_le _) 2

/-- The orthogonal projection onto a subspace, as the linear map under `starProjection`. -/
noncomputable def orthoProj (U : Submodule ℂ S) : S →ₗ[ℂ] S := U.starProjection

lemma adjoint_orthoProj (U : Submodule ℂ S) : (orthoProj U).adjoint = orthoProj U :=
  U.starProjection_isSymmetric.adjoint_eq

lemma orthoProj_comp_self (U : Submodule ℂ S) : orthoProj U ∘ₗ orthoProj U = orthoProj U :=
  LinearMap.ext fun x ↦ Submodule.starProjection_eq_self_iff.2 (U.starProjection_apply_mem x)

/-- The squared Hilbert–Schmidt norm of the orthogonal projection onto `U` is `dim U`. -/
lemma hilbertSchmidtNorm_orthoProj_sq (U : Submodule ℂ S) :
    hilbertSchmidtNorm (orthoProj U) ^ 2 = finrank ℂ U := by
  have h_proj : IsProj U (orthoProj U) :=
    ⟨U.starProjection_apply_mem, fun _ ↦ Submodule.starProjection_eq_self_iff.2⟩
  apply ofReal_injective
  rw [hilbertSchmidtNorm_sq_eq_trace, adjoint_orthoProj, orthoProj_comp_self, h_proj.trace,
    ofReal_natCast]

lemma hilbertSchmidtNorm_comp_orthoProj_le (A : S →ₗ[ℂ] T) (U : Submodule ℂ S) :
    hilbertSchmidtNorm (A ∘ₗ orthoProj U) ≤ hilbertSchmidtNorm A := by
  rw [← hilbertSchmidtNorm_adjoint (A ∘ₗ orthoProj U), ← hilbertSchmidtNorm_adjoint A, adjoint_comp,
    adjoint_orthoProj]
  exact hilbertSchmidtNorm_le_of_norm_le fun x ↦ U.norm_starProjection_apply_le (A.adjoint x)

/-- The squared Hilbert–Schmidt norm of `pr_W A` is the real part of the inner product of
`pr_W` with `A A*`, where `hilbertSchmidtVector` carries the Hilbert–Schmidt inner product of
maps. -/
lemma hilbertSchmidtNorm_orthoProj_comp_sq (W : Submodule ℂ T) (A : S →ₗ[ℂ] T) :
    hilbertSchmidtNorm (orthoProj W ∘ₗ A) ^ 2 = re ⟪hilbertSchmidtVector (orthoProj W),
      hilbertSchmidtVector (A ∘ₗ A.adjoint)⟫_ℂ := by
  set p : T →ₗ[ℂ] T := orthoProj W
  have h_adjoint : (p ∘ₗ A).adjoint ∘ₗ (p ∘ₗ A) = A.adjoint ∘ₗ p ∘ₗ A := by
    rw [adjoint_comp, adjoint_orthoProj, comp_assoc, ← comp_assoc A p, orthoProj_comp_self]
  rw [inner_hilbertSchmidtVector, adjoint_orthoProj, ← comp_assoc, trace_comp_comm', ← h_adjoint,
    ← hilbertSchmidtNorm_sq_eq_trace, ofReal_re]

/-- `A` is almost an isometry from below in mean square, with the error `ε`: on every subspace `U`
its squared Hilbert–Schmidt norm `‖A pr_U‖²` is at least `dim U - ε dim S`. -/
def IsNearIsometry (A : S →ₗ[ℂ] T) (ε : ℝ) : Prop :=
  ∀ U : Submodule ℂ S, finrank ℂ U - ε * finrank ℂ S ≤ hilbertSchmidtNorm (A ∘ₗ orthoProj U) ^ 2

/-- If the squared Hilbert–Schmidt norm of `A* A - 1` is at most `ε² dim S`, then
`IsNearIsometry A ε`: on every subspace `U` the squared Hilbert–Schmidt norm of `A` is at least
`dim U - ε dim S`. -/
lemma isNearIsometry_of_hilbertSchmidtNorm_le {A : S →ₗ[ℂ] T} {ε : ℝ} (hε : 0 ≤ ε)
    (h_defect : hilbertSchmidtNorm (A.adjoint ∘ₗ A - 1) ^ 2 ≤ ε ^ 2 * finrank ℂ S) :
      IsNearIsometry A ε := by
  intro U
  set p : S →ₗ[ℂ] S := orthoProj U
  have h_norm : hilbertSchmidtNorm (A ∘ₗ p) ^ 2 = re ⟪hilbertSchmidtVector p,
    hilbertSchmidtVector (A.adjoint ∘ₗ A)⟫_ℂ := by
    rw [← hilbertSchmidtNorm_adjoint, adjoint_comp, adjoint_orthoProj,
      hilbertSchmidtNorm_orthoProj_comp_sq,
      adjoint_adjoint]
  have h_dim : (finrank ℂ U : ℝ) = re ⟪hilbertSchmidtVector p,
    hilbertSchmidtVector (1 : S →ₗ[ℂ] S)⟫_ℂ := by
    simpa [hilbertSchmidtNorm_orthoProj_sq, End.one_eq_id] using
      hilbertSchmidtNorm_orthoProj_comp_sq U (1 : S →ₗ[ℂ] S)
  have h_diff : hilbertSchmidtNorm (A ∘ₗ p) ^ 2 - finrank ℂ U =
      re ⟪hilbertSchmidtVector p, hilbertSchmidtVector (A.adjoint ∘ₗ A - 1)⟫_ℂ := by
    rw [map_sub, inner_sub_right, sub_re, h_norm, h_dim]
  have h_bound : hilbertSchmidtNorm p * hilbertSchmidtNorm (A.adjoint ∘ₗ A - 1) ≤ ε * finrank ℂ
    S := by
    refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
    calc (hilbertSchmidtNorm p * hilbertSchmidtNorm (A.adjoint ∘ₗ A - 1)) ^ 2
        ≤ finrank ℂ S * (ε ^ 2 * finrank ℂ S) := by
          rw [mul_pow, hilbertSchmidtNorm_orthoProj_sq]
          gcongr
          exact U.finrank_le
      _ = (ε * finrank ℂ S) ^ 2 := by ring
  have h_cs : |re ⟪hilbertSchmidtVector p,
    hilbertSchmidtVector (A.adjoint ∘ₗ A - 1)⟫_ℂ| ≤ ε * finrank ℂ S :=
    (abs_re_le_norm _).trans ((norm_inner_le_norm _ _).trans h_bound)
  linarith [(abs_le.1 h_cs).1]

omit [FiniteDimensional ℂ T] in
/-- A near isometry with the error `ε` is one with any larger error. -/
lemma IsNearIsometry.mono {A : S →ₗ[ℂ] T} {ε ε' : ℝ} (hA : IsNearIsometry A ε) (h_le : ε ≤ ε') :
    IsNearIsometry A ε' :=
  fun U ↦ le_trans (by gcongr) (hA U)

/-- Let `pr₀` be any endomorphism. If `pr₀ B` is almost an isometry from below in mean square, with
an error `ε` below `1`, and the source `S` is not zero, then the range of `pr₀` is not zero. -/
lemma IsNearIsometry.finrank_range_pos [Nontrivial S] {pr₀ : T →ₗ[ℂ] T} {B : S →ₗ[ℂ] T} {ε : ℝ}
    (h_isom : IsNearIsometry (pr₀ ∘ₗ B) ε) (hε : ε < 1) : 0 < finrank ℂ (range pr₀) := by
  -- Otherwise `pr₀ = 0`, and the hypothesis for the whole of `S` reads `(1 - ε) dim S ≤ 0`.
  refine Nat.pos_of_ne_zero fun h_zero ↦ ?_
  obtain rfl : pr₀ = 0 := range_eq_bot.1 (Submodule.finrank_eq_zero.1 h_zero)
  have h_top : finrank ℂ S - ε * finrank ℂ S ≤ 0 := by simpa [hilbertSchmidtNorm] using h_isom ⊤
  have h_pos : (0 : ℝ) < finrank ℂ S := by exact_mod_cast finrank_pos
  nlinarith

omit [FiniteDimensional ℂ T] in
/-- An orthogonal projection `pr` splits `y` orthogonally: `‖y‖² = ‖pr y‖² + ‖(1 - pr) y‖²`. -/
lemma norm_sq_eq_add_of_isSymmetricProjection {pr : T →ₗ[ℂ] T} (hpr : pr.IsSymmetricProjection)
    (y : T) : ‖y‖ ^ 2 = ‖pr y‖ ^ 2 + ‖(1 - pr) y‖ ^ 2 := by
  have h_orth : ⟪pr y, (1 - pr) y⟫_ℂ = 0 := by
    rw [hpr.isSymmetric, ← End.mul_apply, hpr.isIdempotentElem.mul_one_sub_self,
      LinearMap.zero_apply, inner_zero_right]
  simpa [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h_orth

/-- For an orthogonal projection `p` and any `q`: in squared Hilbert–Schmidt norm, the part
`(1 - p q) A` that `p q` misses is at most the sum of the parts that `p` and `q` miss. -/
lemma hilbertSchmidtNorm_one_sub_mul_comp_sq_le {p : T →ₗ[ℂ] T} (hp : p.IsSymmetricProjection)
    (q : T →ₗ[ℂ] T) (A : S →ₗ[ℂ] T) : hilbertSchmidtNorm ((1 - p * q) ∘ₗ A) ^ 2 ≤
      hilbertSchmidtNorm ((1 - p) ∘ₗ A) ^ 2 + hilbertSchmidtNorm ((1 - q) ∘ₗ A) ^ 2 := by
  simp only [hilbertSchmidtNorm_sq_eq_sum (stdOrthonormalBasis ℂ S), ← sum_add_distrib, comp_apply]
  refine sum_le_sum fun i _ ↦ ?_
  -- The inequality holds for the value `y` of `A` at each basis vector.
  generalize A (stdOrthonormalBasis ℂ S i) = y
  -- Split `1 - p q` into the orthogonal parts `p (1 - q)` and `1 - p`.
  have h_range : p * (1 - p * q) = p * (1 - q) := by
    simp [mul_sub, ← mul_assoc, hp.isIdempotentElem.eq]
  have h_ker : (1 - p) * (1 - p * q) = 1 - p := by
    simp [mul_sub, ← mul_assoc, hp.isIdempotentElem.one_sub_mul_self]
  have h_split : ‖(1 - p * q) y‖ ^ 2 = ‖p ((1 - q) y)‖ ^ 2 + ‖(1 - p) y‖ ^ 2 := by
    rw [norm_sq_eq_add_of_isSymmetricProjection hp, ← End.mul_apply, ← End.mul_apply (1 - p),
      h_range, h_ker, End.mul_apply]
  have h_contract : ‖p ((1 - q) y)‖ ^ 2 ≤ ‖(1 - q) y‖ ^ 2 := by
    linarith [norm_sq_eq_add_of_isSymmetricProjection hp ((1 - q) y),
      sq_nonneg ‖(1 - p) ((1 - q) y)‖]
  linarith

/-- Let `IsNearIsometry A ε`: `dim U - ε dim S ≤ ‖A pr_U‖²` in Hilbert–Schmidt norm for all
subspaces `U`. If an orthogonal projection `pr` misses at most `δ dim S` of the squared norm of
`A`, then `IsNearIsometry (pr A) (ε + δ)`. -/
lemma IsNearIsometry.proj_comp {A : S →ₗ[ℂ] T} {ε δ : ℝ} (hA : IsNearIsometry A ε)
    {pr : T →ₗ[ℂ] T} (hpr : pr.IsSymmetricProjection)
    (h_rest : hilbertSchmidtNorm ((1 - pr) ∘ₗ A) ^ 2 ≤ δ * finrank ℂ S) :
    IsNearIsometry (pr ∘ₗ A) (ε + δ) := by
  intro U
  have h_split : hilbertSchmidtNorm (A ∘ₗ orthoProj U) ^ 2 = hilbertSchmidtNorm
    ((pr ∘ₗ A) ∘ₗ orthoProj U) ^ 2 +
      hilbertSchmidtNorm (((1 - pr) ∘ₗ A) ∘ₗ orthoProj U) ^ 2 := by
    simp only [hilbertSchmidtNorm_sq_eq_sum (stdOrthonormalBasis ℂ S), ← sum_add_distrib,
      comp_apply]
    exact sum_congr rfl fun i _ ↦ norm_sq_eq_add_of_isSymmetricProjection hpr _
  have h_cut : hilbertSchmidtNorm (((1 - pr) ∘ₗ A) ∘ₗ orthoProj U) ^ 2 ≤ hilbertSchmidtNorm
    ((1 - pr) ∘ₗ A) ^ 2 :=
    pow_le_pow_left₀ (hilbertSchmidtNorm_nonneg _) (hilbertSchmidtNorm_comp_orthoProj_le _ U) 2
  linarith [hA U]

variable {Γ : Type} [Group Γ] {ρ : Representation ℂ Γ T}

lemma adjoint_rep_of_unitary (hρ : ∀ (s : Γ) (x y : T), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ) (s : Γ) :
    (ρ s).adjoint = ρ s⁻¹ := by
  refine ((eq_adjoint_iff _ _).2 fun x y ↦ ?_).symm
  rw [← hρ s, ρ.self_inv_apply]

/-- Let `ρ` be a unitary representation of `Γ` on `T`. The vector `hilbertSchmidtVector X` lists the
values of a map `X` on an orthonormal basis, so `⟪hilbertSchmidtVector X, hilbertSchmidtVector Y⟫`
is the Hilbert–Schmidt inner product `tr (X* Y)`. This product of `s B B* s⁻¹` and `t B B* t⁻¹` is
the squared Hilbert–Schmidt norm of `B* s⁻¹ t B`. So `s ↦ ‖B* s B‖²` has positive type in this
norm. -/
lemma inner_hilbertSchmidtVector_translate (hρ : ∀ (s : Γ) (x y : T), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ)
    (B : S →ₗ[ℂ] T) (s t : Γ) :
    ⟪hilbertSchmidtVector ((ρ s ∘ₗ B) ∘ₗ (ρ s ∘ₗ B).adjoint),
      hilbertSchmidtVector ((ρ t ∘ₗ B) ∘ₗ (ρ t ∘ₗ B).adjoint)⟫_ℂ =
      (hilbertSchmidtNorm (B.adjoint ∘ₗ ρ (s⁻¹ * t) ∘ₗ B) ^ 2 : ℝ) := by
  set X : S →ₗ[ℂ] T := ρ s ∘ₗ B with hX
  set Y : S →ₗ[ℂ] T := ρ t ∘ₗ B with hY
  have h_factor : B.adjoint ∘ₗ ρ (s⁻¹ * t) ∘ₗ B = X.adjoint ∘ₗ Y := by
    simp [hX, hY, adjoint_comp, adjoint_rep_of_unitary hρ, End.mul_eq_comp, comp_assoc]
  rw [h_factor, hilbertSchmidtNorm_sq_eq_trace, inner_hilbertSchmidtVector]
  calc trace ℂ T ((X ∘ₗ X.adjoint).adjoint ∘ₗ Y ∘ₗ Y.adjoint)
      = trace ℂ T (((X ∘ₗ X.adjoint) ∘ₗ Y) ∘ₗ Y.adjoint) := by
        rw [adjoint_comp, adjoint_adjoint, comp_assoc _ Y]
    _ = trace ℂ S (Y.adjoint ∘ₗ (X ∘ₗ X.adjoint) ∘ₗ Y) := trace_comp_comm' _ _
    _ = trace ℂ S ((X.adjoint ∘ₗ Y).adjoint ∘ₗ X.adjoint ∘ₗ Y) := by
        simp only [adjoint_comp, adjoint_adjoint, comp_assoc]

/-- Cauchy–Schwarz for the projection onto `W` and the sum of the operators `s B B* s⁻¹`, where
`s` runs through a finite group that acts unitarily: the sum of the squared Hilbert–Schmidt norms
`‖pr_W s B‖²` has square at most `dim W` times the order of the group times the sum of
`‖B* s B‖²`. -/
lemma sq_sum_hilbertSchmidtNorm_orthoProj_comp_le [Fintype Γ]
    (hρ : ∀ (s : Γ) (x y : T), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ) (B : S →ₗ[ℂ] T) (W : Submodule ℂ T) :
    (∑ s : Γ, hilbertSchmidtNorm (orthoProj W ∘ₗ ρ s ∘ₗ B) ^ 2) ^ 2 ≤
      finrank ℂ W * (Fintype.card Γ * ∑ s : Γ, hilbertSchmidtNorm (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2) := by
  set sumBB : PiLp 2 fun _ : Fin (finrank ℂ T) ↦ T :=
    ∑ s : Γ, hilbertSchmidtVector ((ρ s ∘ₗ B) ∘ₗ (ρ s ∘ₗ B).adjoint)
  have h_norm : ‖sumBB‖ ^ 2 = Fintype.card Γ * ∑ s,
    hilbertSchmidtNorm (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_sum_sum_eq_card_mul
      (fun s ↦ ((hilbertSchmidtNorm (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2 : ℝ) : ℂ))
        (inner_hilbertSchmidtVector_translate hρ B),
      ← ofReal_sum, ← ofReal_natCast, ← ofReal_mul]
    exact ofReal_re _
  have h_inner : ∑ s, hilbertSchmidtNorm (orthoProj W ∘ₗ ρ s ∘ₗ B) ^ 2 =
      re ⟪hilbertSchmidtVector (orthoProj W), sumBB⟫_ℂ := by
    simp only [sumBB, hilbertSchmidtNorm_orthoProj_comp_sq, inner_sum, re_sum]
  have h_cs : re ⟪hilbertSchmidtVector (orthoProj W),
    sumBB⟫_ℂ ≤ hilbertSchmidtNorm (orthoProj W) * ‖sumBB‖ :=
    (re_le_norm _).trans (norm_inner_le_norm _ _)
  calc (∑ s : Γ, hilbertSchmidtNorm (orthoProj W ∘ₗ ρ s ∘ₗ B) ^ 2) ^ 2
      ≤ (hilbertSchmidtNorm (orthoProj W) * ‖sumBB‖) ^ 2 :=
        pow_le_pow_left₀ (sum_nonneg fun _ _ ↦ sq_nonneg _) (h_inner.trans_le h_cs) 2
    _ = finrank ℂ W * (Fintype.card Γ * ∑ s : Γ,
      hilbertSchmidtNorm (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2) := by
        rw [mul_pow, hilbertSchmidtNorm_orthoProj_sq, h_norm]

/-- **One translate.** Let a finite group `Γ` act unitarily on `T` by `ρ`, and let `pr₀` be the
orthogonal projection onto a stable subspace `T₀`, so that `pr₀ s = s pr₀`. Suppose that `pr₀ B` is
almost an isometry in mean square with the error `ε`, and that `dim T₀` times the mean of
`‖B* s B‖²` is at most `(1 + ε) (dim S)²`. Then the maps `pr₀ s B` spread (`IsSpread`): for every
subspace `W` of `T₀`, of dimension `α dim T₀`, the preimage of `W` under some `pr₀ s B` has
dimension at most `(1 + α + 3 ε) / 2 · dim S`. -/
theorem isSpread_of_second_moment [Fintype Γ]
    (hρ : ∀ (s : Γ) (x y : T), ⟪ρ s x, ρ s y⟫_ℂ = ⟪x, y⟫_ℂ) {pr₀ : T →ₗ[ℂ] T}
    (hpr₀ : pr₀.IsSymmetricProjection) (h_comm : ∀ s : Γ, Commute pr₀ (ρ s)) {B : S →ₗ[ℂ] T}
    {ε : ℝ} (hε : 0 ≤ ε) (h_isom : IsNearIsometry (pr₀ ∘ₗ B) ε)
    (h_moment : finrank ℂ (range pr₀) * ∑ s : Γ, hilbertSchmidtNorm (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2 ≤
      Fintype.card Γ * ((1 + ε) * finrank ℂ S ^ 2)) :
    IsSpread (fun s : Γ ↦ pr₀.rangeRestrict ∘ₗ ρ s ∘ₗ B) (3 / 2 * ε) := by
  -- Cauchy–Schwarz bounds the mean of `‖pr_W s B‖²`, so for some `s` this squared norm is within
  -- that bound. For this `s` the near isometry, applied to the preimage of `W`, bounds the
  -- dimension of that preimage. Here `W₀` is `W` inside `T₀`, and `α = dim W / dim T₀`.
  intro W₀ α
  set W : Submodule ℂ T := W₀.map (range pr₀).subtype
  have hα : 0 ≤ α := by positivity
  have h_dim : (finrank ℂ W : ℝ) = α * finrank ℂ (range pr₀) := by
    rw [Submodule.finrank_map_subtype_eq]
    have h_zero (h : (finrank ℂ (range pr₀) : ℝ) = 0) : (finrank ℂ W₀ : ℝ) = 0 :=
      mod_cast Nat.eq_zero_of_le_zero (W₀.finrank_le.trans_eq (mod_cast h))
    exact (div_mul_cancel_of_imp h_zero).symm
  set moment : ℝ := ∑ s : Γ, hilbertSchmidtNorm (B.adjoint ∘ₗ ρ s ∘ₗ B) ^ 2
  have h_mean : ∑ s, hilbertSchmidtNorm (orthoProj W ∘ₗ ρ s ∘ₗ B) ^ 2 ≤
      Fintype.card Γ * ((α + 1 + ε) / 2 * finrank ℂ S) := by
    refine (abs_le_of_sq_le_sq' ?_ (by positivity)).2
    calc (∑ s, hilbertSchmidtNorm (orthoProj W ∘ₗ ρ s ∘ₗ B) ^ 2) ^ 2
        ≤ finrank ℂ W * (Fintype.card Γ * moment) :=
          sq_sum_hilbertSchmidtNorm_orthoProj_comp_le hρ B W
      _ = α * Fintype.card Γ * (finrank ℂ (range pr₀) * moment) := by
          rw [h_dim]
          ring
      _ ≤ α * Fintype.card Γ * (Fintype.card Γ * ((1 + ε) * finrank ℂ S ^ 2)) := by gcongr
      _ = α * (1 + ε) * (Fintype.card Γ * finrank ℂ S) ^ 2 := by ring
      _ ≤ ((α + 1 + ε) / 2) ^ 2 * (Fintype.card Γ * finrank ℂ S) ^ 2 := by
          gcongr
          nlinarith [sq_nonneg (α - (1 + ε))]
      _ = (Fintype.card Γ * ((α + 1 + ε) / 2 * finrank ℂ S)) ^ 2 := by ring
  obtain ⟨s, -, hs⟩ : ∃ s ∈ (Finset.univ : Finset Γ),
      hilbertSchmidtNorm (orthoProj W ∘ₗ ρ s ∘ₗ B) ^ 2 ≤ (α + 1 + ε) / 2 * finrank ℂ S :=
    exists_le_of_sum_le univ_nonempty (by rwa [sum_const, card_univ, nsmul_eq_mul])
  refine ⟨s, ?_⟩
  set W' : Submodule ℂ S := W₀.comap (pr₀.rangeRestrict ∘ₗ ρ s ∘ₗ B)
  -- On the preimage `W'` of `W` the maps `s pr₀ B` and `pr_W s B` agree.
  have h_agree (x : S) (hx : x ∈ W') : ρ s (pr₀ (B x)) = orthoProj W (ρ s (B x)) := by
    have h_mem : pr₀ (ρ s (B x)) ∈ W :=
      Submodule.mem_map_of_mem (f := (range pr₀).subtype) hx
    have h_orth (w : T) (hw : w ∈ W) : ⟪ρ s (B x) - pr₀ (ρ s (B x)), w⟫_ℂ = 0 := by
      obtain ⟨y, rfl⟩ : w ∈ range pr₀ := Submodule.map_subtype_le _ W₀ hw
      simp [← hpr₀.isSymmetric _ y, ← End.mul_apply pr₀ pr₀, hpr₀.isIdempotentElem.eq]
    rw [← End.mul_apply, ← (h_comm s).eq, End.mul_apply]
    exact (Submodule.eq_starProjection_of_mem_of_inner_eq_zero h_mem h_orth).symm
  have h_preimage : hilbertSchmidtNorm ((pr₀ ∘ₗ B) ∘ₗ orthoProj W') ≤ hilbertSchmidtNorm
    (orthoProj W ∘ₗ ρ s ∘ₗ B) := by
    refine (hilbertSchmidtNorm_le_of_norm_le fun x ↦ ?_).trans
      (hilbertSchmidtNorm_comp_orthoProj_le _ W')
    have h_isometry (y : T) : ‖ρ s y‖ = ‖y‖ := by
      rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hρ, ← norm_eq_sqrt_re_inner]
    calc ‖pr₀ (B (orthoProj W' x))‖
        = ‖ρ s (pr₀ (B (orthoProj W' x)))‖ := (h_isometry _).symm
      _ ≤ ‖orthoProj W (ρ s (B (orthoProj W' x)))‖ := by
          rw [h_agree (orthoProj W' x) (W'.starProjection_apply_mem x)]
  have h_near : finrank ℂ W' - ε * finrank ℂ S ≤ hilbertSchmidtNorm ((pr₀ ∘ₗ B) ∘ₗ orthoProj W') ^
    2 :=
    h_isom W'
  linarith [pow_le_pow_left₀ (hilbertSchmidtNorm_nonneg _) h_preimage 2]

end HilbertSchmidt

section FewTranslates

open Submodule Real

variable {Θ V W : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
  [AddCommGroup W] [Module ℂ W] [Module.Finite ℂ W]

/-- The image of `A` adds `dim V - dim A⁻¹ F` dimensions to `F`. -/
lemma finrank_sup_range_add_finrank_comap (A : V →ₗ[ℂ] W) (F : Submodule ℂ W) :
    finrank ℂ ↥(F ⊔ range A) + finrank ℂ (F.comap A) = finrank ℂ F + finrank ℂ V := by
  have h_comap : finrank ℂ ↥(F ⊓ range A) + finrank ℂ (ker A) = finrank ℂ (F.comap A) := by
    rw [← (A.domRestrict (F.comap A)).finrank_range_add_finrank_ker, range_domRestrict,
      map_comap_eq, inf_comm, ker_domRestrict,
      (comapSubtypeEquivOfLe (ker_le_comap A : ker A ≤ F.comap A)).finrank_eq]
  have h_sup := finrank_sup_add_finrank_inf_eq F (range A)
  linarith [A.finrank_range_add_finrank_ker]

variable {B : Θ → V →ₗ[ℂ] W} {ε : ℝ}

/-- One step of the greedy choice. Let `W` be nonzero and suppose that the maps `B s` spread with
the error `3 ε / 2`. If `F` misses more than a share `16 ε` of the dimensions of `W`, then adding
some image `range (B s)` to `F` multiplies the codimension by at most `1 - 2 dim V / (5 dim W)`. -/
lemma IsSpread.exists_codim_le (h_spread : IsSpread B (3 / 2 * ε)) (F : Submodule ℂ W)
    (hW : 0 < finrank ℂ W) (hF : 16 * ε * finrank ℂ W < (finrank ℂ W - finrank ℂ F : ℝ)) :
    ∃ s : Θ, (finrank ℂ W - finrank ℂ ↥(F ⊔ range (B s)) : ℝ) ≤
      (1 - 2 * finrank ℂ V / (5 * finrank ℂ W)) * (finrank ℂ W - finrank ℂ F) := by
  obtain ⟨s, hs⟩ := h_spread F
  refine ⟨s, ?_⟩
  have hW' : (0 : ℝ) < finrank ℂ W := by exact_mod_cast hW
  set α : ℝ := finrank ℂ F / finrank ℂ W
  have hα : (finrank ℂ F : ℝ) = α * finrank ℂ W := (div_mul_cancel₀ _ hW'.ne').symm
  have hα_le : α ≤ 1 := (div_le_one hW').2 (by exact_mod_cast F.finrank_le)
  have h_share : 16 * ε < 1 - α := lt_of_mul_lt_mul_right (by linarith) hW'.le
  have h_added : (finrank ℂ ↥(F ⊔ range (B s)) : ℝ) + finrank ℂ (F.comap (B s)) =
      finrank ℂ F + finrank ℂ V := by exact_mod_cast finrank_sup_range_add_finrank_comap (B s) F
  -- The image adds at least `(1/2 - 3/32) (1 - α) dim V ≥ (2/5) (1 - α) dim V` dimensions.
  have h_gain : ((1 + α) / 2 + 3 / 2 * ε) * finrank ℂ V ≤ (1 - 2 / 5 * (1 - α)) * finrank ℂ V := by
    gcongr
    linarith
  have h_factor : (1 - 2 * finrank ℂ V / (5 * finrank ℂ W)) * (finrank ℂ W - finrank ℂ F : ℝ) =
      finrank ℂ W - finrank ℂ F - 2 / 5 * (1 - α) * finrank ℂ V := by
    rw [hα]
    field
  rw [h_factor]
  linarith

/-- The greedy choice after `l` steps. Let `W` be nonzero and let the maps `B s : V → W` spread with
the error `3 ε / 2`. Then the span of the images of at most `l` of them misses at most a share
`max (16 ε) (exp (-l rate))` of the dimensions of `W`, where `rate = 2 dim V / (5 dim W)`: each step
removes at least that share of what is missing. -/
lemma IsSpread.exists_codim_le_max (h_spread : IsSpread B (3 / 2 * ε)) (hW : 0 < finrank ℂ W)
    (l : ℕ) :
    ∃ t : Finset Θ, #t ≤ l ∧ (finrank ℂ W - finrank ℂ ↥(⨆ s ∈ t, range (B s)) : ℝ) ≤
      max (16 * ε) (exp (-(l * (2 * finrank ℂ V / (5 * finrank ℂ W))))) * finrank ℂ W := by
  classical
  have hW' : (0 : ℝ) < finrank ℂ W := by exact_mod_cast hW
  set rate : ℝ := 2 * finrank ℂ V / (5 * finrank ℂ W)
  let codim (t : Finset Θ) : ℝ := finrank ℂ W - finrank ℂ ↥(⨆ s ∈ t, range (B s))
  change ∃ t : Finset Θ, #t ≤ l ∧ codim t ≤ max (16 * ε) (exp (-(l * rate))) * finrank ℂ W
  induction l with
  | zero =>
    refine ⟨∅, le_rfl, ?_⟩
    calc codim ∅ ≤ finrank ℂ W := sub_le_self _ (Nat.cast_nonneg _)
      _ ≤ max (16 * ε) (exp (-((0 : ℕ) * rate))) * finrank ℂ W :=
          le_mul_of_one_le_left hW'.le (le_max_of_le_right (by simp))
  | succ l ih =>
    obtain ⟨t, h_card, h_codim⟩ := ih
    obtain h_done | h_more := le_or_gt (codim t) (16 * ε * finrank ℂ W)
    · exact ⟨t, h_card.trans l.le_succ,
        h_done.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW'.le)⟩
    obtain ⟨s, h_step⟩ := h_spread.exists_codim_le _ hW h_more
    have h_exp : codim t ≤ exp (-(l * rate)) * finrank ℂ W := by
      rw [max_mul_of_nonneg _ _ hW'.le, le_max_iff] at h_codim
      exact h_codim.resolve_left h_more.not_ge
    refine ⟨insert s t, (card_insert_le s t).trans (by omega), ?_⟩
    have h_insert : ⨆ i ∈ insert s t, range (B i) = (⨆ i ∈ t, range (B i)) ⊔ range (B s) := by
      rw [Finset.iSup_insert, sup_comm]
    calc codim (insert s t)
        ≤ (1 - rate) * codim t := by rwa [← h_insert] at h_step
      _ ≤ exp (-rate) * (exp (-(l * rate)) * finrank ℂ W) := by
          gcongr
          · exact sub_nonneg.2 (by exact_mod_cast Submodule.finrank_le _)
          · exact one_sub_le_exp_neg rate
      _ = exp (-((l + 1 : ℕ) * rate)) * finrank ℂ W := by
          rw [← mul_assoc, ← exp_add]
          push_cast
          ring_nf
      _ ≤ max (16 * ε) (exp (-((l + 1 : ℕ) * rate))) * finrank ℂ W :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hW'.le

/-- **Few maps span almost everything.** Let `V` and `W` be nonzero finite-dimensional spaces, let
`0 < ε < 1 / 16`, and let the maps `B s : V → W` spread with the error `3 ε / 2`. Then the images of
at most `(5/2) (1 + log (1 / (16 ε))) dim W / dim V` of them span a subspace of dimension at least
`(1 - 16 ε) dim W`. -/
theorem IsSpread.exists_few_le_finrank_iSup_range [Nontrivial V] (h_spread : IsSpread B (3 / 2 * ε))
    (hW : 0 < finrank ℂ W) (hε : 0 < ε) (hε_lt : ε < 1 / 16) :
    ∃ t : Finset Θ,
      #t * finrank ℂ V ≤ 5 / 2 * (1 + log (16 * ε)⁻¹) * finrank ℂ W ∧
      (1 - 16 * ε) * finrank ℂ W ≤ finrank ℂ ↥(⨆ s ∈ t, range (B s)) := by
  -- Choose the maps greedily. While more than a share `16 ε` is missing, each step multiplies the
  -- missing share by at most `1 - rate ≤ exp (-rate)`; about `log (1 / (16 ε)) / rate` steps do.
  have hW' : (0 : ℝ) < finrank ℂ W := by exact_mod_cast hW
  have hV : (0 : ℝ) < finrank ℂ V := by exact_mod_cast finrank_pos
  set rate : ℝ := 2 * finrank ℂ V / (5 * finrank ℂ W) with h_rate
  have h_rate_pos : 0 < rate := by positivity
  -- The first step shows `rate ≤ 1`.
  have h_rate_le : rate ≤ 1 := by
    have h_start : 16 * ε * finrank ℂ W < finrank ℂ W - finrank ℂ (⊥ : Submodule ℂ W) := by
      simpa using mul_lt_of_lt_one_left hW' (by linarith : 16 * ε < 1)
    obtain ⟨s, h_step⟩ := h_spread.exists_codim_le ⊥ hW h_start
    have h_codim_nonneg : (0 : ℝ) ≤ finrank ℂ W - finrank ℂ ↥(⊥ ⊔ range (B s)) :=
      sub_nonneg.2 (by exact_mod_cast Submodule.finrank_le _)
    have h_nonneg : 0 ≤ (1 - rate) * finrank ℂ W := by simpa using h_codim_nonneg.trans h_step
    exact sub_nonneg.1 (nonneg_of_mul_nonneg_left h_nonneg hW')
  -- Stop at the least `l` with `l rate ≥ log (1 / (16 ε))`; then `l rate ≤ 1 + log (1 / (16 ε))`.
  have h_log : 0 ≤ log (16 * ε)⁻¹ :=
    log_nonneg ((one_le_inv₀ (by positivity)).2 (by linarith))
  set l : ℕ := ⌈log (16 * ε)⁻¹ / rate⌉₊
  have hl_ge : log (16 * ε)⁻¹ ≤ l * rate := (div_le_iff₀ h_rate_pos).1 (Nat.le_ceil _)
  have hl_le : l * rate ≤ 1 + log (16 * ε)⁻¹ :=
    calc l * rate ≤ (log (16 * ε)⁻¹ / rate + 1) * rate := by
          gcongr
          exact (Nat.ceil_lt_add_one (by positivity)).le
      _ = rate + log (16 * ε)⁻¹ := by field
      _ ≤ 1 + log (16 * ε)⁻¹ := by gcongr
  obtain ⟨t, h_card, h_codim⟩ : ∃ t : Finset Θ, #t ≤ l ∧
      (finrank ℂ W - finrank ℂ ↥(⨆ s ∈ t, range (B s)) : ℝ) ≤
        max (16 * ε) (exp (-(l * rate))) * finrank ℂ W := h_spread.exists_codim_le_max hW l
  have h_exp : exp (-(l * rate)) ≤ 16 * ε := by
    rwa [← le_log_iff_exp_le (by positivity), _root_.neg_le, ← log_inv]
  rw [max_eq_left h_exp] at h_codim
  refine ⟨t, ?_, by linarith⟩
  calc (#t * finrank ℂ V : ℝ) ≤ l * finrank ℂ V := by gcongr
    _ = 5 / 2 * (l * rate) * finrank ℂ W := by rw [h_rate]; field
    _ ≤ 5 / 2 * (1 + log (16 * ε)⁻¹) * finrank ℂ W := by gcongr

/-- The images of a subspace `C` under `#t` maps span at most `#t dim C` dimensions. -/
lemma finrank_biSup_map_le (B : Θ → V →ₗ[ℂ] W) (t : Finset Θ) (C : Submodule ℂ V) :
    finrank ℂ ↥(⨆ s ∈ t, C.map (B s)) ≤ #t * finrank ℂ C := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert s t hs ih =>
    rw [t.iSup_insert, card_insert_of_notMem hs]
    calc finrank ℂ ↥(C.map (B s) ⊔ ⨆ s ∈ t, C.map (B s))
        ≤ finrank ℂ (C.map (B s)) + finrank ℂ ↥(⨆ s ∈ t, C.map (B s)) :=
          finrank_add_le_finrank_add_finrank _ _
      _ ≤ finrank ℂ C + #t * finrank ℂ C := add_le_add (finrank_map_le (B s) C) ih
      _ = (#t + 1) * finrank ℂ C := by ring

/-- Restricting finitely many maps to a subspace `U` lowers the dimension of the span of their
images by at most the codimension of `U` for each map. -/
lemma finrank_biSup_range_le (B : Θ → V →ₗ[ℂ] W) (t : Finset Θ) (U : Submodule ℂ V) :
    finrank ℂ ↥(⨆ s ∈ t, (B s).range) ≤
      finrank ℂ ↥(⨆ s ∈ t, U.map (B s)) + #t * (finrank ℂ V - finrank ℂ U : ℝ) := by
  obtain ⟨C, hC⟩ : ∃ C : Submodule ℂ V, IsCompl U C := U.exists_isCompl
  have h_dim : (finrank ℂ V - finrank ℂ U : ℝ) = finrank ℂ C := by
    rw [← finrank_add_eq_of_isCompl hC, Nat.cast_add, add_sub_cancel_left]
  have h_split : ⨆ s ∈ t, (B s).range = (⨆ s ∈ t, U.map (B s)) ⊔ ⨆ s ∈ t, C.map (B s) := by
    simp only [← iSup_sup_eq, ← Submodule.map_sup, hC.sup_eq_top, Submodule.map_top]
  rw [h_dim, h_split]
  exact_mod_cast (finrank_add_le_finrank_add_finrank _ _).trans
    (add_le_add_right (finrank_biSup_map_le B t C) _)

end FewTranslates

end New
