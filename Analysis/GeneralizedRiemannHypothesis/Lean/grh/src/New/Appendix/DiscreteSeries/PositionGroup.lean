import New.Appendix.DiscreteSeries.Periods
import New.Appendix.DiscreteSeries.StationaryPosition

/-!
# The group of a position

The elements `g` of `U(ε)` for which `g - 1` lowers the flag of a position form a closed subgroup
`R`. It maps to `U(η)` by the action `g'` on the image of `i₀` modulo `A_{≤ j₀ - 1}`, and it
carries an additive sum `σ`.

* The period over `R` in a stationary position is bounded below by Laplace's method
  (`IsStationary.integrable_periodIntegrand_and_measure_le`). The bound passes to a group that maps
  properly onto `R` (`IsStationary.period_lower_bound_of_surjective`).
* The pairing over `U(ε)` of a coefficient of `U(ε)` with a conjugated coefficient of `U(ε ⊕ 1)` is
  bounded below (`IsSteep.exists_volume_le_mul_norm_integral_dsCoeff`). This is the period in a
  stationary position with one vector `v₁`, where `R` is the stabilizer of `v₁` in `U(ε ⊕ 1)`, a
  conjugate of `U(ε)`.

Notions from other files:
* `USign ε` is the unitary group `U(ε)` of the diagonal matrix `signMatrix ε` of signs, and
  `formAdjoint ε η A` is the adjoint `A†` of `A : (ℂ^m, η) → (ℂ^n, ε)` for these forms.
* `IsPosition ε η d v i₀`: the columns `v₁, …, v_{j₀}` of `v`, `j₀ = d + 1`, are independent, their
  products vanish except that `v_{j₀}` has norm `±1`, `i₀` is an isometry into their orthogonal
  complement, and `card n = card m + 2 d + 1`.
* `LowersFlag d v Y σ`: `Y` maps the span `A_{≤ j}` of `v₁, …, v_j` into `A_{≤ j - 1}` for `j ≤ j₀`,
  and `σ` is the sum of the coefficients of `v_j` in `Y v_{j + 1}`.
* `InducesOn d v i₀ Y Y'`: `Y i₀ = i₀ Y'` modulo `A_{≤ j₀ - 1}`.
* `IsSteep l B e`: for `e : X ⊕ Fin M ≃ n`, the weight of the lowest `K`-type of `l` is `0` on `X`
  and decreases in `[-3 B, -B]` on the other coordinates, with alternating signs there.
* `IsLaplaceDatum` collects the hypotheses of Laplace's method on a map into `U(ε) × U(η)`.
-/

noncomputable section

open Finset Matrix MeasureTheory ComplexConjugate Norms.L2Operator

namespace New.DiscreteSeries

variable {n m X : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] {ε : n → ℤˣ}
  {η : m → ℤˣ} {d : ℕ} {v : Matrix n (Fin (d + 1)) ℂ} {i₀ : Matrix n m ℂ}

omit [DecidableEq n] in
/-- Multiplying on the left commutes with taking the first `d` columns. -/
lemma mul_initCols {p : Type} (A : Matrix p n ℂ) (v : Matrix n (Fin (d + 1)) ℂ) :
    A * initCols v = (A * v).submatrix id Fin.castSucc :=
  rfl

/-- Let `initCols` take the first `d` of `d + 1` columns. If `g - 1` maps the columns of `v` into
the span of the first `d` columns with the matrix `N`, then `g` maps this span into itself, with
the matrix `1 + initCols N`. -/
lemma mul_initCols_eq {g : Matrix n n ℂ} {N : Matrix (Fin d) (Fin (d + 1)) ℂ}
    (hN : (g - 1) * v = initCols v * N) : g * initCols v = initCols v * (1 + initCols N) := by
  have h_init : (g - 1) * initCols v = initCols v * initCols N := by simp only [mul_initCols, hN]
  rw [Matrix.mul_add, ← h_init, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, add_sub_cancel]

/-- Let `g` be invertible and let `g - 1` lower the flag of the columns `v₁, …, v_{d + 1}` of `v`:
it sends each `v_j` to a combination of `v₁, …, v_{j - 1}`, and `σ` is the sum over `j ≤ d` of the
coefficients of `v_j` in `(g - 1) v_{j + 1}`. Then `g⁻¹ - 1` lowers the same flag, with some sum of
coefficients `σ'`. -/
lemma LowersFlag.inv {g : (Matrix n n ℂ)ˣ} {σ : ℂ}
    (h_lowers : LowersFlag d v ((g : Matrix n n ℂ) - 1) σ) :
    ∃ σ' : ℂ, LowersFlag d v ((↑g⁻¹ : Matrix n n ℂ) - 1) σ' := by
  obtain ⟨N, hN_tri, hN, -⟩ : ∃ N : Matrix (Fin d) (Fin (d + 1)) ℂ,
      (∀ (a : Fin d) (b : Fin (d + 1)), b.val ≤ a.val → N a b = 0) ∧
      ((g : Matrix n n ℂ) - 1) * v = initCols v * N ∧ ∑ a : Fin d, N a a.succ = σ := h_lowers
  -- On the span of the first `d` columns of `v` the map `g` has a unipotent upper triangular matrix
  -- `T`.
  set T : Matrix (Fin d) (Fin d) ℂ := 1 + initCols N with hT
  have hT_tri : T.BlockTriangular id :=
    blockTriangular_one.add fun a b hba ↦ hN_tri a b.castSucc (le_of_lt hba)
  have hT_diag (a : Fin d) : T a a = 1 := by simp [hT, initCols, hN_tri]
  have hT_unit : IsUnit T.det := by simp [det_of_isUpperTriangular hT_tri, hT_diag]
  have : Invertible T := T.invertibleOfIsUnitDet hT_unit
  have hg_inv : (↑g⁻¹ : Matrix n n ℂ) * initCols v = initCols v * T⁻¹ :=
    calc _ = (↑g⁻¹ : Matrix n n ℂ) * ((g : Matrix n n ℂ) * initCols v) * T⁻¹ := by
          rw [mul_initCols_eq hN, ← Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hT_unit]
      _ = initCols v * T⁻¹ := by rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  -- The matrix of `g⁻¹ - 1 = -g⁻¹ (g - 1)` is `-(T⁻¹ N)`.
  have h_tri (a : Fin d) (b : Fin (d + 1)) (hba : b.val ≤ a.val) : (-(T⁻¹ * N)) a b = 0 := by
    rw [Matrix.neg_apply, neg_eq_zero, mul_apply]
    refine sum_eq_zero fun t _ ↦ (lt_or_ge t a).elim (fun hta ↦ ?_) fun hat ↦ ?_
    · exact mul_eq_zero_of_left (blockTriangular_inv_of_blockTriangular hT_tri hta) _
    · exact mul_eq_zero_of_right _ (hN_tri t b (hba.trans hat))
  have h_mul : ((↑g⁻¹ : Matrix n n ℂ) - 1) * v = initCols v * -(T⁻¹ * N) :=
    calc _ = -((↑g⁻¹ : Matrix n n ℂ) * (((g : Matrix n n ℂ) - 1) * v)) := by
          rw [← Matrix.mul_assoc, mul_sub, Units.inv_mul, mul_one, ← Matrix.neg_mul, neg_sub]
      _ = initCols v * -(T⁻¹ * N) := by
          rw [hN, ← Matrix.mul_assoc, hg_inv, Matrix.mul_assoc, Matrix.mul_neg]
  exact ⟨_, -(T⁻¹ * N), h_tri, h_mul, rfl⟩

/-- The group `R` of the `g` in `U(ε)` with `(g - 1) A_{≤ j} ⊆ A_{≤ j - 1}` for `j ≤ j₀ = d + 1`,
where `A_{≤ j}` is the span of the first `j` columns of `v`. -/
def positionGroup (ε : n → ℤˣ) (v : Matrix n (Fin (d + 1)) ℂ) : Subgroup (USign ε) where
  carrier := {g : USign ε | ∃ σ : ℂ, LowersFlag d v (g.val.val - 1) σ}
  one_mem' := ⟨0, 0, by simp, by simp, by simp⟩
  mul_mem' := fun ⟨σ₁, h₁⟩ ⟨σ₂, h₂⟩ ↦ ⟨σ₁ + σ₂, h₁.mul h₂⟩
  inv_mem' := fun ⟨_, h⟩ ↦ h.inv

/-- The sum of the coefficients of `v_j` in `g v_{j + 1}` over `j ≤ d`, where `v_j` are the columns
of `v` and `g` lies in the group `R = positionGroup ε v`. The choice is unique if the `v_j` are
independent, see `IsPosition.lowersFlag_unique`. -/
def positionSum (g : positionGroup ε v) : ℂ :=
  Exists.choose g.prop

/-- The matrix `g - 1` lowers the flag of the columns of `v`, with coefficient sum
`positionSum g`. -/
lemma lowersFlag_positionSum (g : positionGroup ε v) :
    LowersFlag d v ((g : Matrix n n ℂ) - 1) (positionSum g) := Exists.choose_spec g.prop

/-- For `g` in `positionGroup ε v`, the matrix `g - 1` maps the columns of `v` into the span of
the first `d` columns. -/
lemma exists_sub_one_mul_eq_initCols_mul (g : positionGroup ε v) :
    ∃ N : Matrix (Fin d) (Fin (d + 1)) ℂ, ((g : Matrix n n ℂ) - 1) * v = initCols v * N :=
  let ⟨N, _, hN, _⟩ := lowersFlag_positionSum g; ⟨N, hN⟩

namespace IsPosition

/-- For a position `(v, i₀)`, the sum of the coefficients of `v_j` in `g v_{j + 1}` is additive on
the group `positionGroup ε v`. -/
lemma positionSum_mul (hP : IsPosition ε η d v i₀) (g₁ g₂ : positionGroup ε v) :
    positionSum (g₁ * g₂) = positionSum g₁ + positionSum g₂ :=
  hP.lowersFlag_unique (lowersFlag_positionSum (g₁ * g₂))
    ((lowersFlag_positionSum g₁).mul (lowersFlag_positionSum g₂))

/-- For a position `(v, i₀)`, the group `positionGroup ε v` of the `g` for which `g - 1` lowers the
flag of the columns of `v` is closed in `U(ε)`. -/
lemma isClosed_positionGroup (hP : IsPosition ε η d v i₀) :
    IsClosed (positionGroup ε v : Set (USign ε)) := by
  -- In coordinates `Z` along `v₁, …, v_d` the matrix of `g - 1` is `Z (g - 1) v`.
  obtain ⟨Z, -, hZ : Z * initCols v = 1⟩ := hP.exists_mul_eq_zero_and_mul_initCols_eq_one
  let N (g : USign ε) : Matrix (Fin d) (Fin (d + 1)) ℂ := Z * (((g : Matrix n n ℂ) - 1) * v)
  have h_eq : (positionGroup ε v : Set (USign ε)) =
      {g : USign ε | ∀ (a : Fin d) (b : Fin (d + 1)), b.val ≤ a.val → N g a b = 0} ∩
      {g : USign ε | ((g : Matrix n n ℂ) - 1) * v = initCols v * N g} := by
    refine Set.ext fun g ↦ ⟨?_, fun ⟨h_tri, h_mul⟩ ↦ ⟨_, N g, h_tri, h_mul, rfl⟩⟩
    rintro ⟨σ, N₀, h_tri, h_mul, -⟩
    obtain rfl : N₀ = N g := by
      simp only [N, h_mul, ← Matrix.mul_assoc Z (initCols v), hZ, Matrix.one_mul]
    exact ⟨h_tri, h_mul⟩
  simp only [h_eq, Set.ofPred_forall]
  exact (isClosed_iInter fun a ↦ isClosed_iInter fun b ↦ isClosed_iInter fun _ ↦
    isClosed_eq (by fun_prop) continuous_const).inter (isClosed_eq (by fun_prop) (by fun_prop))

/-- For a position `(v, i₀)` and `g` in the group `positionGroup ε v`, the image of `(g - 1) i₀` is
orthogonal to the columns of `v` for the form of signs `ε`. -/
lemma vec_orthogonal_sub_one_mul (hP : IsPosition ε η d v i₀) (g : positionGroup ε v) :
    vᴴ * signMatrix ε * (((g : Matrix n n ℂ) - 1) * i₀) = 0 := by
  -- The adjoint `Y† = g⁻¹ - 1` maps the columns of `v` into the span of the first `d` columns.
  set Y : Matrix n n ℂ := (g : Matrix n n ℂ) - 1 with hY
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin d) (Fin (d + 1)) ℂ,
      formAdjoint ε ε Y * v = initCols v * N := by
    simpa [hY, formAdjoint_sub_one] using exists_sub_one_mul_eq_initCols_mul g⁻¹
  calc vᴴ * signMatrix ε * (Y * i₀) = (formAdjoint ε ε Y * v)ᴴ * signMatrix ε * i₀ := by
        simp [formAdjoint, IsHermitianInvolution.isHermitian.eq, Matrix.mul_assoc,
          signMatrix_mul_self]
    _ = Nᴴ * ((initCols v)ᴴ * signMatrix ε * i₀) := by
        simp only [hN, conjTranspose_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hP.initCols_orthogonal, Matrix.mul_zero]

/-- Let `(v, i₀)` be a position: the `d + 1` columns of `v` are independent, their products for the
form of signs `ε` vanish except that the last has norm `±1`, `i₀` is an isometry of `(ℂ^m, η)` into
their orthogonal complement, and `card n = card m + 2 d + 1`. Let `g` lie in `positionGroup ε v`, so
`g` is in `U(ε)` and `g - 1` maps each column of `v` into the span of the earlier ones. Then `g`
acts by `i₀† g i₀` on the image of `i₀` modulo the span of the first `d` columns of `v`. -/
lemma inducesOn (hP : IsPosition ε η d v i₀) (g : positionGroup ε v) :
    InducesOn d v i₀ ((g : Matrix n n ℂ) - 1)
      (formAdjoint ε η i₀ * (g : Matrix n n ℂ) * i₀ - 1) := by
  set Y : Matrix n n ℂ := (g : Matrix n n ℂ) - 1 with hY
  have h_orth : vᴴ * signMatrix ε * (Y * i₀) = 0 := hP.vec_orthogonal_sub_one_mul g
  -- Write `Y i₀ = i₀ T₁ + v T₂`; the last row of `T₂` vanishes, as `v_{d + 1}` has norm `±1`.
  obtain ⟨T, hT_cols : Y * i₀ = fromCols i₀ v * T⟩ :=
    hP.exists_eq_of_orthogonal (congrArg (·.submatrix Fin.castSucc id) h_orth)
  have hT : Y * i₀ = i₀ * toRows₁ T + v * toRows₂ T := by simp [hT_cols, ← fromCols_mul_fromRows]
  have h_top : formAdjoint ε η i₀ * (g : Matrix n n ℂ) * i₀ - 1 = toRows₁ T :=
    calc _ = formAdjoint ε η i₀ * (Y * i₀) := by
          simp [hY, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hP.formAdjoint_mul_self]
      _ = toRows₁ T := by
          simp [hT, Matrix.mul_add, ← Matrix.mul_assoc, hP.formAdjoint_mul_self,
            hP.formAdjoint_mul_vec]
  have h_last (j : m) : T (Sum.inr (Fin.last d)) j = 0 := by
    have h_gram : vᴴ * signMatrix ε * v * toRows₂ T = 0 := by
      rwa [hT, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.vec_orthogonal,
        Matrix.zero_mul, zero_add] at h_orth
    have h_entry :
        (vᴴ * signMatrix ε * v) (Fin.last d) (Fin.last d) * T (Sum.inr (Fin.last d)) j = 0 := by
      simpa [mul_apply (M := vᴴ * signMatrix ε * v), hP.gram_eq_zero, Fin.sum_univ_castSucc,
        Fin.castSucc_ne_last] using congrFun₂ h_gram (Fin.last d) j
    obtain h_norm | h_norm := hP.gram_last_eq_sign <;> simpa [h_norm] using h_entry
  refine ⟨(toRows₂ T).submatrix Fin.castSucc id, ?_⟩
  rw [hT, h_top, add_right_inj]
  ext i j
  simp [mul_apply, Fin.sum_univ_castSucc, h_last, initCols]

/-- Let `(v, i₀)` be a position: the `d + 1` columns of `v` are independent, their products for the
form of signs `ε` vanish except that the last has norm `±1`, `i₀` is an isometry of `(ℂ^m, η)` into
their orthogonal complement, and `card n = card m + 2 d + 1`. Then `g ↦ i₀† g i₀` is multiplicative
on the group `positionGroup ε v` of the `g` in `U(ε)` such that `g - 1` maps each column of `v` into
the span of the earlier ones. -/
lemma formAdjoint_conj_mul (hP : IsPosition ε η d v i₀) (g₁ g₂ : positionGroup ε v) :
    formAdjoint ε η i₀ * (↑(g₁ * g₂) : Matrix n n ℂ) * i₀ =
      formAdjoint ε η i₀ * (g₁ : Matrix n n ℂ) * i₀ *
        (formAdjoint ε η i₀ * (g₂ : Matrix n n ℂ) * i₀) := by
  obtain ⟨N, hN⟩ := exists_sub_one_mul_eq_initCols_mul g₁
  obtain ⟨C, h_act⟩ : ∃ C : Matrix (Fin d) m ℂ, (g₂ : Matrix n n ℂ) * i₀ =
      i₀ * (formAdjoint ε η i₀ * (g₂ : Matrix n n ℂ) * i₀) + initCols v * C := by
    simpa [InducesOn, Matrix.sub_mul, Matrix.mul_sub, sub_add_eq_add_sub] using hP.inducesOn g₂
  -- The element `g₁` preserves the span of `v₁, …, v_d`, on which `i₀†` vanishes.
  have h_zero : formAdjoint ε η i₀ * (g₁ : Matrix n n ℂ) * initCols v = 0 := by
    rw [Matrix.mul_assoc, mul_initCols_eq hN, ← Matrix.mul_assoc]
    simp [mul_initCols, hP.formAdjoint_mul_vec]
  calc formAdjoint ε η i₀ * (↑(g₁ * g₂) : Matrix n n ℂ) * i₀
      = formAdjoint ε η i₀ * (g₁ : Matrix n n ℂ) * ((g₂ : Matrix n n ℂ) * i₀) := by
        simp [Matrix.mul_assoc]
    _ = formAdjoint ε η i₀ * (g₁ : Matrix n n ℂ) * i₀ *
          (formAdjoint ε η i₀ * (g₂ : Matrix n n ℂ) * i₀) := by
        rw [h_act, Matrix.mul_add, ← Matrix.mul_assoc _ _ C, h_zero, Matrix.zero_mul, add_zero,
          ← Matrix.mul_assoc]

/-- For a position `(v, i₀)` and `g` in `positionGroup ε v`, the matrix `i₀† g i₀` preserves the
form of signs `η`, where `i₀† = formAdjoint ε η i₀`. -/
lemma isometry_formAdjoint_conj (hP : IsPosition ε η d v i₀) (g : positionGroup ε v) :
    (formAdjoint ε η i₀ * (g : Matrix n n ℂ) * i₀)ᴴ * signMatrix η *
      (formAdjoint ε η i₀ * (g : Matrix n n ℂ) * i₀) = signMatrix η := by
  refine isometry_of_formAdjoint_mul_self ?_
  have h_adj : formAdjoint η η (formAdjoint ε η i₀ * (g : Matrix n n ℂ) * i₀) =
      formAdjoint ε η i₀ * (↑g⁻¹ : Matrix n n ℂ) * i₀ := by
    simp [formAdjoint_mul (η := ε), formAdjoint_formAdjoint, formAdjoint_val, Matrix.mul_assoc]
  simpa [h_adj, hP.formAdjoint_mul_self] using (hP.formAdjoint_conj_mul g⁻¹ g).symm

/-- The map `g ↦ g' = i₀† g i₀` from the group `positionGroup ε v` of a position `(v, i₀)` to
`U(η)`, where `i₀† = formAdjoint ε η i₀`. -/
def inducedHom (hP : IsPosition ε η d v i₀) : positionGroup ε v →* USign η :=
  MonoidHom.mk'
    (fun g ↦ U.of IsHermitianInvolution.isUnit (formAdjoint ε η i₀ * g.val.val.val * i₀)
      (hP.isometry_formAdjoint_conj g))
    fun g₁ g₂ ↦ Subtype.ext (Units.ext (hP.formAdjoint_conj_mul g₁ g₂))

lemma inducedHom_val (hP : IsPosition ε η d v i₀) (g : positionGroup ε v) :
    (hP.inducedHom g : Matrix m m ℂ) = formAdjoint ε η i₀ * (g : Matrix n n ℂ) * i₀ := rfl

/-- For a position `(v, i₀)`, if `g` in `positionGroup ε v` acts by `y` on the image of `i₀` modulo
the span of the first `d` columns of `v`, then `y` is the image `i₀† g i₀` of `g` in `U(η)`. -/
lemma inducedHom_eq (hP : IsPosition ε η d v i₀) {g : positionGroup ε v} {y : USign η}
    (h_induces : InducesOn d v i₀ ((g : Matrix n n ℂ) - 1) ((y : Matrix m m ℂ) - 1)) :
    hP.inducedHom g = y := by
  obtain ⟨C, hC⟩ := h_induces
  have h_adj : formAdjoint ε η i₀ * (((g : Matrix n n ℂ) - 1) * i₀) = (y : Matrix m m ℂ) - 1 := by
    simp [hC, Matrix.mul_add, ← Matrix.mul_assoc, hP.formAdjoint_mul_self, mul_initCols,
      hP.formAdjoint_mul_vec]
  refine Subtype.ext (Units.ext ?_)
  simpa [inducedHom_val, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hP.formAdjoint_mul_self]
    using h_adj

/-- The function `θ g = c_l g * conj (c_k g') * exp (conj (σ g) - σ g)` on the group of a position
`(v, i₀)`. Here `l` and `k` are integer vectors, doubled Harish-Chandra parameters for `U(ε)` and
`U(η)`; `c_l`, `c_k` are their discrete series coefficients `HCParam.dsCoeff`, given by
Flensted-Jensen's normalised integral over the maximal compact subgroup (`HCParam.flenstedJensen`);
`g' = inducedHom g = i₀† g i₀`; and `σ` is the sum `positionSum`. -/
def periodIntegrand (hP : IsPosition ε η d v i₀) (l : HCParam ε) (k : HCParam η)
    (g : positionGroup ε v) : ℂ :=
  l.dsCoeff (g : Matrix n n ℂ) * conj (k.dsCoeff (hP.inducedHom g : Matrix m m ℂ)) *
    Complex.exp (conj (positionSum g) - positionSum g)

/-- Let `(v, i₀)` be a position: the `d + 1` columns of `v` are independent, their products for the
form of signs `ε` vanish except that the last has norm `±1`, `i₀` is an isometry of `(ℂ^m, η)` into
their orthogonal complement, and `card n = card m + 2 d + 1`. Every `y` in the unitary group
`U(η) = USign η` of the form of signs `η` is the image `i₀† g i₀` of an element `g` of
`positionGroup ε v` that acts by `y` on the image of `i₀` and fixes its orthogonal complement. -/
lemma exists_inducedHom_eq (hP : IsPosition ε η d v i₀) (y : USign η) :
    ∃ g : positionGroup ε v, hP.inducedHom g = y ∧
      (g : Matrix n n ℂ) - 1 = i₀ * ((y : Matrix m m ℂ) - 1) * formAdjoint ε η i₀ := by
  -- Extend `y` by the identity on the complement; the adjoint is the extension of `y⁻¹`.
  let A (z : USign η) : Matrix n n ℂ := 1 - i₀ * (1 - (z : Matrix m m ℂ)) * formAdjoint ε η i₀
  have h_cancel (M : Matrix m n ℂ) : formAdjoint ε η i₀ * (i₀ * M) = M := by
    simp [← Matrix.mul_assoc, hP.formAdjoint_mul_self]
  have h_sub : A y - 1 = i₀ * ((y : Matrix m m ℂ) - 1) * formAdjoint ε η i₀ := by
    simp [A, Matrix.mul_sub, Matrix.sub_mul]
  have h_adj : formAdjoint ε ε (A y) = A y⁻¹ := by
    simp [A, formAdjoint_sub, formAdjoint_mul (η := η), formAdjoint_formAdjoint, formAdjoint_val,
      formAdjoint_one, Matrix.mul_assoc]
  have h_unitary : formAdjoint ε ε (A y) * A y = 1 := by
    have h_inv (M : Matrix m n ℂ) : (↑y⁻¹ : Matrix m m ℂ) * ((y : Matrix m m ℂ) * M) = M := by
      simp [← Matrix.mul_assoc]
    rw [h_adj]
    simp only [A, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h_cancel, h_inv, Matrix.one_mul,
      Matrix.mul_one]
    abel
  have h_lowers : LowersFlag d v (A y - 1) 0 :=
    ⟨0, by simp, by simp [h_sub, Matrix.mul_assoc, hP.formAdjoint_mul_vec], by simp⟩
  have h_induced : formAdjoint ε η i₀ * A y * i₀ = (y : Matrix m m ℂ) := by
    simp [A, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hP.formAdjoint_mul_self, h_cancel]
  exact ⟨⟨U.of IsHermitianInvolution.isUnit (A y) (isometry_of_formAdjoint_mul_self h_unitary), 0,
    h_lowers⟩, Subtype.ext (Units.ext h_induced), h_sub⟩

end IsPosition

/-- Let `(v, i₀)` be a stationary position for the parameters `l` and `k`, where `e` and `e'` place
the common coordinates `X` in `n` and `m`, and let `l` be steep: on `X` its sign is `+1` and its
weight is `0`, and on the other coordinates the signs alternate and the weight decreases strictly in
`[-3 B, -B]`. On `X` let `η = 1` and the weight of the lowest `K`-type of `k` vanish; let this
weight be nonnegative, and at most `3 B` unless `U(η)` is compact.

For `g` in the group `positionGroup ε v` let `g' = inducedHom g = i₀† g i₀`, and let `σ g` be
`positionSum g`, the sum over `j ≤ d` of the coefficient of `v_j` in `(g - 1) v_{j + 1}`. Then
`g ↦ (g, g')` and `φ = σ - conj σ` satisfy the hypotheses `IsLaplaceDatum` of Laplace's method:
`φ` is additive and imaginary and is the difference of the phases at `(g - 1, g' - 1)`, the traces
of `g - 1` and `g' - 1` agree, the conditions above on the weights hold, and the image of the map
contains `U(X)`, embedded diagonally. -/
theorem IsStationary.isLaplaceDatum [Fintype X] [DecidableEq X] {l : HCParam ε} {k : HCParam η}
    {M M' : ℕ} {e : X ⊕ Fin M ≃ n} {e' : X ⊕ Fin M' ≃ m} {B : ℝ}
    (hP : IsStationary l k e e' d v i₀) (h_steep : IsSteep l B e)
    (h_sign_inl : ∀ x : X, η (e' (Sum.inl x)) = 1)
    (h_weight_inl : ∀ x : X, k.lowestKType (e' (Sum.inl x)) = 0)
    (h_weight_nonneg : ∀ i : m, 0 ≤ k.lowestKType i)
    (h_weight_le : ∀ i i' : m, η i ≠ η i' → k.lowestKType i ≤ 3 * B) :
    IsLaplaceDatum l k ((positionGroup ε v).subtype.prod hP.inducedHom) (e' ∘ Sum.inl) B e
      fun g : positionGroup ε v ↦ positionSum g - conj (positionSum g) := by
  -- The sum is a homomorphism to the additive group of `ℂ`, so it sends inverses to negatives.
  have h_inv (g : positionGroup ε v) : positionSum g⁻¹ = -positionSum g :=
    (MonoidHom.mk' (Multiplicative.ofAdd ∘ positionSum) hP.positionSum_mul).map_inv g
  -- The adjoint of `g - 1` is `g⁻¹ - 1`, which lowers the flag with the opposite sum.
  have h_adj (g : positionGroup ε v) :
      LowersFlag d v (formAdjoint ε ε ((g : Matrix n n ℂ) - 1)) (-positionSum g) := by
    simpa [formAdjoint_sub_one, ← h_inv] using lowersFlag_positionSum g⁻¹
  refine
    { toIsSteep := h_steep
      phase_eq := fun g ↦ by
        rw [sub_eq_add_neg (positionSum g), ← map_neg]
        exact hP.phase_eq (lowersFlag_positionSum g) (hP.inducesOn g) (h_adj g)
      trace_eq := fun g ↦ hP.trace_eq (lowersFlag_positionSum g) (hP.inducesOn g) (h_adj g)
      phase_mul := fun g₁ g₂ ↦ by rw [hP.positionSum_mul, map_add, add_sub_add_comm]
      re_phase_eq_zero := fun g ↦ by simp
      sign_weight_right := fun x ↦ ⟨h_sign_inl x, h_weight_inl x⟩
      weight_nonneg_and_le := fun i i' ↦ ⟨h_weight_nonneg i, h_weight_le i i'⟩
      exists_diagonal := fun u hu ↦ ?_ }
  -- As `i₀ = 1` on `ℂ^X`, the copy of `U(η)` contains `U(X)`, embedded diagonally.
  obtain ⟨y, hy⟩ : ∃ y : USign η, (y : Matrix m m ℂ) - 1 =
      inclMatrix ℂ (e' ∘ Sum.inl) * (u - 1) * (inclMatrix ℂ (e' ∘ Sum.inl))ᴴ :=
    exists_unitary_sub_one_eq_inclMatrix e' h_sign_inl (mem_unitaryGroup_iff'.1 hu)
  obtain ⟨g, rfl, hg⟩ := hP.exists_inducedHom_eq y
  have h_inc : i₀ * inclMatrix ℂ (e' ∘ Sum.inl) = inclMatrix ℂ (e ∘ Sum.inl) := by
    rw [mul_inclMatrix]
    ext i x
    simp [inclMatrix, hP.apply_inl, one_apply]
  have h_inc_adj : (inclMatrix ℂ (e' ∘ Sum.inl))ᴴ * formAdjoint ε η i₀ =
      (inclMatrix ℂ (e ∘ Sum.inl))ᴴ := by
    rw [← formAdjoint_inclMatrix (τ := e' ∘ Sum.inl) h_sign_inl, ← formAdjoint_mul, h_inc,
      formAdjoint_inclMatrix (τ := e ∘ Sum.inl) h_steep.sign_inl]
  refine ⟨g, Prod.ext ?_ hy⟩
  show (g : Matrix n n ℂ) - 1 =
    inclMatrix ℂ (e ∘ Sum.inl) * (u - 1) * (inclMatrix ℂ (e ∘ Sum.inl))ᴴ
  rw [hg, hy, Matrix.mul_assoc, Matrix.mul_assoc, h_inc_adj, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    h_inc]

/-- **Lower bound for the period over the group of a position.** Let the integer vectors `l = 2 λ`
and `k = 2 λ'` be doubled Harish-Chandra parameters for `U(ε)` and `U(η)`. The weight of `l` is
`l.lowestKType = λ + ρ - 2 ρ_c`, the highest weight of the lowest `K`-type, and likewise for `k`.
Take a stationary position `(v, i₀)` of `U(η)` in `U(ε)`: the weight `μ` of `l`, as a diagonal
matrix, takes each of the first `d` columns of `v` to the next, `i₀† μ i₀` is the weight of `k`, and
`i₀` is the identity on the coordinates `X`, placed in `n` and `m` by `e` and `e'`. Let `l` be steep
with `B ≥ 1`. Let the weight of `k` vanish on `X`, where the signs are `+1`, be nonnegative, and be
at most `3 B` unless `U(η)` is compact. Let `L` bound the entries of `l` and `k`, let `β ≥ 10 ^ 12`
be at least `N + L`, where `N = card n + card m`, and let `h ≥ 10 ^ 30 (N² log β)³`. Let
`l.HasLargeGap h` hold: the entries of `l` are distinct, congruent to `card n - 1` mod 2, and
`|λ i - λ j| ≥ 500 (card n)³ + h` whenever `ε i ≠ ε j`. Let `k.HasLargeGap h` hold, the same
condition for `λ'`, `η` and `m`. Then `periodIntegrand` is integrable for every right invariant
measure `ν` on `positionGroup ε v` that is finite on compact sets, and the volume of the set of `g`
with operator norms `‖g‖, ‖i₀† g i₀‖ ≤ β + 1` is at most `β ^ (20 N²)` times the norm of its
integral.

Here `positionGroup ε v` is the group of the `g` in `U(ε)` such that, for `j ≤ d + 1`, `g - 1` maps
the span of `v_1, …, v_j` into that of `v_1, …, v_{j - 1}`. -/
theorem IsStationary.integrable_periodIntegrand_and_measure_le [Fintype X] [DecidableEq X]
    [Nonempty n] [Nonempty m] {l : HCParam ε} {k : HCParam η} {M M' L h : ℕ} {e : X ⊕ Fin M ≃ n}
    {e' : X ⊕ Fin M' ≃ m} {B β : ℝ}
    (hP : IsStationary l k e e' d v i₀) (h_steep : IsSteep l B e) (hB : 1 ≤ B)
    (h_sign_inl : ∀ x : X, η (e' (Sum.inl x)) = 1)
    (h_weight_inl : ∀ x : X, k.lowestKType (e' (Sum.inl x)) = 0)
    (h_weight_nonneg : ∀ i : m, 0 ≤ k.lowestKType i)
    (h_weight_le : ∀ i i' : m, η i ≠ η i' → k.lowestKType i ≤ 3 * B)
    (hl_gap : l.HasLargeGap h) (hk_gap : k.HasLargeGap h)
    (hl_le : ∀ a : n, |l a| ≤ L) (hk_le : ∀ a : m, |k a| ≤ L)
    (hβ : 10 ^ 12 ≤ β) (h_card : Fintype.card n + Fintype.card m + L ≤ β)
    (hh : 10 ^ 30 * ((Fintype.card n + Fintype.card m) ^ 2 * β.log) ^ 3 ≤ h)
    (ν : Measure (positionGroup ε v)) [ν.IsMulRightInvariant] [IsFiniteMeasureOnCompacts ν] :
    Integrable (hP.periodIntegrand l k) ν ∧
    ν {g : positionGroup ε v |
        ‖(g : Matrix n n ℂ)‖ ≤ β + 1 ∧ ‖(hP.inducedHom g : Matrix m m ℂ)‖ ≤ β + 1} ≤
      ENNReal.ofReal (β ^ (20 * (Fintype.card n + Fintype.card m) ^ 2) *
        ‖∫ g : positionGroup ε v, hP.periodIntegrand l k g ∂ν‖) := by
  let j : positionGroup ε v →* USign ε × USign η := (positionGroup ε v).subtype.prod hP.inducedHom
  have h_integrand_eq : hP.periodIntegrand l k = l.laplaceIntegrand k j
      fun g : positionGroup ε v ↦ positionSum g - conj (positionSum g) := by
    ext g
    simp [IsPosition.periodIntegrand, HCParam.laplaceIntegrand, j]
  have h_cont : Continuous fun g : positionGroup ε v ↦ (j g).2 := by
    simp only [continuous_U_iff_matrix, j, MonoidHom.prod_apply, IsPosition.inducedHom_val]
    fun_prop
  rw [h_integrand_eq]
  exact (hP.isLaplaceDatum h_steep h_sign_inl h_weight_inl h_weight_nonneg
    h_weight_le).laplace_method ν hP.isClosed_positionGroup.isProperMap_subtypeVal h_cont hl_gap
    hk_gap hB hl_le hk_le hβ h_card hh

/-- **The period over a group that maps onto the group of a position.** Let `(v, i₀)` be a
stationary position of `U(η)` in `U(ε)` for the parameters `l = 2 λ` and `k = 2 λ'`: the columns
`v₁, …, v_{d + 1}` of `v` are independent, their products vanish except that the last has norm
`±1`, `i₀` is an isometry into their orthogonal complement and the identity on the common
coordinates `X` (placed by `e`, `e'`), the weight `μ = l.lowestKType`, as a diagonal matrix, takes
`v_j` to `v_{j + 1}`, and `i₀† μ i₀` is `μ' = k.lowestKType`. Let `l` be steep with `B ≥ 1`: on
`X` the signs are `+1` and `μ = 0`, and off `X` the signs alternate and `μ` decreases strictly in
`[-3 B, -B]`. Let `μ'` vanish on `X`, where the signs are `+1`, be nonnegative, and be at most `3 B`
unless `U(η)` is compact. Let `HasLargeGap h` hold for `l` and `k`: the entries are distinct, of
the parity of the dimension minus one, and entries of `λ` (resp. `λ'`) of opposite signs differ by
at least `500 (dimension)³ + h`, the dimension being `card n` (resp. `card m`). Let `L` bound the
entries of `l` and `k`, `N = card n + card m`, `β ≥ 10 ^ 12`, `β ≥ N + L` and
`h ≥ 10 ^ 30 (N² log β)³`.

Let `j : S →* U(ε) × U(η)` and write `j s = (g, g')`.
Let `s ↦ g` be proper and onto `positionGroup ε v`, let `g - 1` take each `v_j` into the span of
the earlier ones, with `σ s` the sum of the coefficients of `v_j` in `(g - 1) v_{j + 1}`, and let
`g` act by `g'` on the image of `i₀` modulo `v₁, …, v_d`. For a right invariant measure `ν` on `S`
that is finite on compact sets, the volume of the set where `‖g‖, ‖g'‖ ≤ β + 1` is at most
`β ^ (20 N²)` times the norm of the integral of
`laplaceIntegrand = c_l g * conj (c_k g') * exp (conj (σ s) - σ s)`, with the discrete series
coefficients `c_l`, `c_k`. -/
theorem IsStationary.period_lower_bound_of_surjective [Fintype X] [DecidableEq X] [Nonempty n]
    [Nonempty m] {l : HCParam ε} {k : HCParam η} {M M' L h : ℕ} {e : X ⊕ Fin M ≃ n}
    {e' : X ⊕ Fin M' ≃ m} {B β : ℝ}
    (hP : IsStationary l k e e' d v i₀) (h_steep : IsSteep l B e) (hB : 1 ≤ B)
    (h_sign_inl : ∀ x : X, η (e' (Sum.inl x)) = 1)
    (h_weight_inl : ∀ x : X, k.lowestKType (e' (Sum.inl x)) = 0)
    (h_weight_nonneg : ∀ i : m, 0 ≤ k.lowestKType i)
    (h_weight_le : ∀ i i' : m, η i ≠ η i' → k.lowestKType i ≤ 3 * B)
    (hl_gap : l.HasLargeGap h) (hk_gap : k.HasLargeGap h)
    (hl_le : ∀ a : n, |l a| ≤ L) (hk_le : ∀ a : m, |k a| ≤ L)
    (hβ : 10 ^ 12 ≤ β) (h_card : Fintype.card n + Fintype.card m + L ≤ β)
    (hh : 10 ^ 30 * ((Fintype.card n + Fintype.card m) ^ 2 * β.log) ^ 3 ≤ h)
    {S : Type} [Group S] [TopologicalSpace S] [MeasurableSpace S] [MeasurableMul S] [BorelSpace S]
    (ν : Measure S) [ν.IsMulRightInvariant] [IsFiniteMeasureOnCompacts ν]
    {j : S →* USign ε × USign η} {σ : S → ℂ} (h_proper : IsProperMap fun s : S ↦ (j s).1)
    (h_onto : ∀ g ∈ positionGroup ε v, ∃ s : S, (j s).1 = g)
    (h_lowers : ∀ s : S, LowersFlag d v (((j s).1 : Matrix n n ℂ) - 1) (σ s))
    (h_induces : ∀ s : S,
      InducesOn d v i₀ (((j s).1 : Matrix n n ℂ) - 1) (((j s).2 : Matrix m m ℂ) - 1)) :
    ν {s : S | ‖((j s).1 : Matrix n n ℂ)‖ ≤ β + 1 ∧ ‖((j s).2 : Matrix m m ℂ)‖ ≤ β + 1} ≤
      ENNReal.ofReal (β ^ (20 * (Fintype.card n + Fintype.card m) ^ 2) *
        ‖∫ s : S, l.laplaceIntegrand k j (fun s : S ↦ σ s - conj (σ s)) s ∂ν‖) := by
  -- Apply the bound for `R = positionGroup ε v` to the image of `ν` under `f : s ↦ g`.
  let f : S →* positionGroup ε v :=
    ((MonoidHom.fst (USign ε) (USign η)).comp j).codRestrict _ fun s ↦ ⟨σ s, h_lowers s⟩
  have hf_val (s : S) : (f s : USign ε) = (j s).1 := rfl
  have hf : Measurable f := (h_proper.continuous.subtype_mk _).measurable
  have : (ν.map f).IsMulRightInvariant := ⟨fun g ↦ by
    obtain ⟨t, rfl⟩ : ∃ t : S, f t = g := (h_onto g g.prop).imp fun _ ↦ Subtype.ext
    conv_rhs => rw [← map_mul_right_eq_self ν t]
    simp (disch := fun_prop) only [Measure.map_map, Function.comp_def, map_mul]⟩
  have : IsFiniteMeasureOnCompacts (ν.map f) := ⟨fun K hK ↦ by
    rw [Measure.map_apply hf hK.measurableSet, ← Set.preimage_image_eq K Subtype.val_injective]
    exact (h_proper.isCompact_preimage (hK.image continuous_subtype_val)).measure_lt_top⟩
  obtain ⟨h_int, h_vol⟩ := hP.integrable_periodIntegrand_and_measure_le h_steep hB h_sign_inl
    h_weight_inl
    h_weight_nonneg h_weight_le hl_gap hk_gap hl_le hk_le hβ h_card hh (ν.map f)
  -- The image `g'` in `U(η)` and the sum `σ` are determined by `g`.
  have h_snd (s : S) : hP.inducedHom (f s) = (j s).2 := hP.inducedHom_eq (h_induces s)
  have h_sum (s : S) : positionSum (f s) = σ s :=
    hP.lowersFlag_unique (lowersFlag_positionSum (f s)) (h_lowers s)
  have h_integrand (s : S) : hP.periodIntegrand l k (f s) =
      l.laplaceIntegrand k j (fun s : S ↦ σ s - conj (σ s)) s := by
    simp [IsPosition.periodIntegrand, HCParam.laplaceIntegrand, hf_val, h_snd, h_sum]
  rw [integral_map hf.aemeasurable h_int.aestronglyMeasurable] at h_vol
  simpa only [Set.preimage_ofPred_eq, hf_val, h_snd, h_integrand] using
    (Measure.le_map_apply hf.aemeasurable _).trans h_vol

end New.DiscreteSeries

end

/-! ## Restriction to `U(ε)` -/

section RestrictionLemma

open Matrix Fintype MeasureTheory ComplexConjugate Norms.L2Operator

namespace New.DiscreteSeries

variable {n X : Type} [Fintype n] [DecidableEq n] [Fintype X] {ε : n → ℤˣ}

/-- Let `(v, i₀)` be a position of `U(ε)` in `U(ε ⊕ 1)` with one vector `v₁`, the only column of
`v`. If `v₁` has norm `1` for the form `ε ⊕ 1`, the matrix `(i₀, v₁)` preserves that form. -/
lemma IsPosition.gram_fromCols {v : Matrix (n ⊕ Unit) (Fin 1) ℂ} {i₀ : Matrix (n ⊕ Unit) n ℂ}
    (hP : IsPosition (Sum.elim ε 1) ε 0 v i₀)
    (h_norm : (vᴴ * signMatrix (Sum.elim ε (1 : Unit → ℤˣ)) * v) 0 0 = 1) :
    (fromCols i₀ (replicateCol Unit (v.col 0)))ᴴ * signMatrix (Sum.elim ε 1) *
      fromCols i₀ (replicateCol Unit (v.col 0)) = signMatrix (Sum.elim ε 1) := by
  have h_herm : ((fromCols i₀ (replicateCol Unit (v.col 0)))ᴴ * signMatrix (Sum.elim ε 1) *
      fromCols i₀ (replicateCol Unit (v.col 0))).IsHermitian :=
    isHermitian_conjTranspose_mul_mul _ (by simp [IsHermitian, signMatrix])
  refine Eq.trans ?_ (signMatrix_sum ε 1)
  -- The blocks: `i₀` is an isometry, `v₁` is orthogonal to its image (twice), `v₁` has norm `1`.
  ext (a | a) (b | b)
  · exact congrFun₂ hP.isometry a b
  · exact congrFun₂ hP.orthogonal a 0
  · rw [← h_herm.apply, fromBlocks_apply₂₁, Matrix.zero_apply, star_eq_zero]
    exact congrFun₂ hP.orthogonal b 0
  · exact h_norm.trans (by simp)

/-- For `w` in `U(ε ⊕ 1)` and `g` in `U(ε)`: `w (g ⊕ 1) w⁻¹ - 1 = w ((g - 1) ⊕ 0) w⁻¹`. -/
lemma conj_inl_sub_one (w : USign (Sum.elim ε (1 : Unit → ℤˣ))) (g : USign ε) :
    ((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1 =
      (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) * fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 *
        (↑(w⁻¹) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) := by
  have h_block : (U.inl ε (1 : Unit → ℤˣ) g : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1 =
      fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 := by
    ext (a | a) (b | b) <;> simp [one_apply]
  simp [← h_block, mul_sub_one, sub_mul]

/-- If `g` in `U(ε)` is within `1` of the identity, then `‖w (g ⊕ 1) w⁻¹‖ ≤ 1 + ‖w‖²` for `w` in
`U(ε ⊕ 1)`, in the `L²` operator norm. -/
lemma norm_conj_inl_le (w : USign (Sum.elim ε (1 : Unit → ℤˣ))) {g : USign ε}
    (hg : ‖(g : Matrix n n ℂ) - 1‖ ≤ 1) :
    ‖((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ≤
      1 + ‖(w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 := by
  set W : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ := ↑w
  set Y : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ := fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 with hY
  have hY_le : ‖Y‖ ≤ 1 := by rwa [hY, norm_fromBlocks_zero_zero, norm_zero,
    max_eq_left (norm_nonneg _)]
  calc ‖((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖
      = ‖1 + W * Y * (↑(w⁻¹) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ := by
        rw [← conj_inl_sub_one w g, add_sub_cancel]
    _ ≤ 1 + ‖W‖ * ‖Y‖ * ‖W‖ := (norm_add_le _ _).trans
        (add_le_add norm_one.le (norm_mul₃_le.trans_eq (by rw [U.norm_inv w])))
    _ ≤ 1 + ‖W‖ * 1 * ‖W‖ := by gcongr
    _ = 1 + ‖W‖ ^ 2 := by ring

/-- For `w` in `U(ε ⊕ 1)` and `g` in `U(ε)`: `(w (g ⊕ 1) w⁻¹ - 1) w = w ((g - 1) ⊕ 0)`. -/
lemma conj_inl_sub_one_mul (w : USign (Sum.elim ε (1 : Unit → ℤˣ))) (g : USign ε) :
    (((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1) *
        (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) =
      (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) * fromBlocks ((g : Matrix n n ℂ) - 1) 0 0 0 :=
  (Units.eq_mul_inv_iff_mul_eq _).1 (conj_inl_sub_one w g)

/-- Let `w = (i₀, v₁)` lie in `U(ε ⊕ 1)`, where `v₁` is the only column of `v`. For `g` in `U(ε)`
the element `w (g ⊕ 1) w⁻¹` fixes `v₁`: its difference with `1` lowers the flag of `v`, with sum of
coefficients `0`. -/
lemma lowersFlag_conj_inl_sub_one {v : Matrix (n ⊕ Unit) (Fin 1) ℂ} {i₀ : Matrix (n ⊕ Unit) n ℂ}
    {w : USign (Sum.elim ε (1 : Unit → ℤˣ))}
    (hw : (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) = fromCols i₀ (replicateCol Unit (v.col 0)))
    (g : USign ε) :
    LowersFlag 0 v
      (((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1)
      0 := by
  set Y : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ :=
    ((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1
  -- Read the last column of `Y w = w ((g - 1) ⊕ 0)`.
  have h_vec : Y * replicateCol Unit (v.col 0) = 0 := by
    have h_eq := conj_inl_sub_one_mul w g
    rw [hw, mul_fromCols, fromCols_mul_fromBlocks, fromCols_ext_iff] at h_eq
    simpa [Y] using h_eq.right
  refine ⟨0, fun a ↦ a.elim0, ?_, Finset.sum_of_isEmpty _⟩
  rw [Matrix.mul_zero]
  ext i b
  obtain rfl : b = 0 := Fin.fin_one_eq_zero b
  exact congrFun₂ h_vec i ()

/-- Let `w = (i₀, v₁)` lie in `U(ε ⊕ 1)`, where `v₁` is the only column of `v`. For `g` in `U(ε)`,
`InducesOn 0 v i₀` holds: `w (g ⊕ 1) w⁻¹ - 1` acts on the image of `i₀` as `g - 1`. So
`(w (g ⊕ 1) w⁻¹ - 1) i₀ = i₀ (g - 1)`. -/
lemma inducesOn_conj_inl_sub_one {v : Matrix (n ⊕ Unit) (Fin 1) ℂ} {i₀ : Matrix (n ⊕ Unit) n ℂ}
    {w : USign (Sum.elim ε (1 : Unit → ℤˣ))}
    (hw : (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) = fromCols i₀ (replicateCol Unit (v.col 0)))
    (g : USign ε) :
    InducesOn 0 v i₀
      (((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1)
      ((g : Matrix n n ℂ) - 1) := by
  set Y : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ :=
    ((w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1)) : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1
  -- Read the first block of columns of `Y w = w ((g - 1) ⊕ 0)`.
  have h_image : Y * i₀ = i₀ * ((g : Matrix n n ℂ) - 1) := by
    have h_eq := conj_inl_sub_one_mul w g
    rw [hw, mul_fromCols, fromCols_mul_fromBlocks, fromCols_ext_iff] at h_eq
    simpa [Y] using h_eq.left
  exact ⟨0, by rw [Matrix.mul_zero, add_zero, h_image]⟩

/-- Let `(v, i₀)` be a position of `U(ε)` in `U(ε ⊕ 1)` with `d = 0`: `v` has a single column `v₁`,
of norm `±1` for the form `ε ⊕ 1`, and `i₀` is an isometry of `(ℂ^n, ε)` into its orthogonal
complement. Let `w = (i₀, v₁)` lie in `U(ε ⊕ 1)`. Every element `g` of `positionGroup (ε ⊕ 1) v`,
the stabilizer of `v₁`, has the form `w (y ⊕ 1) w⁻¹` with `y` in `U(ε)`. -/
lemma IsPosition.exists_conj_inl_eq {v : Matrix (n ⊕ Unit) (Fin 1) ℂ} {i₀ : Matrix (n ⊕ Unit) n ℂ}
    {w : USign (Sum.elim ε (1 : Unit → ℤˣ))} (hP : IsPosition (Sum.elim ε 1) ε 0 v i₀)
    (hw : (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) = fromCols i₀ (replicateCol Unit (v.col 0)))
    {g : USign (Sum.elim ε (1 : Unit → ℤˣ))} (hg : g ∈ positionGroup (Sum.elim ε 1) v) :
    ∃ y : USign ε, w * U.inl ε 1 y * w⁻¹ = g := by
  -- The element `g` acts on the image of `i₀` by some `y` in `U(ε)`, and it fixes `v₁`.
  let y : USign ε := hP.inducedHom ⟨g, hg⟩
  set Y : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ := (g : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1
  have h_image : Y * i₀ = i₀ * ((y : Matrix n n ℂ) - 1) := by
    obtain ⟨C, hC⟩ : InducesOn 0 v i₀ Y ((y : Matrix n n ℂ) - 1) := hP.inducesOn ⟨g, hg⟩
    rw [hC, Subsingleton.elim C 0, Matrix.mul_zero, add_zero]
  have h_vec : Y * replicateCol Unit (v.col 0) = 0 := by
    obtain ⟨N, hN : Y * v = initCols v * N⟩ := exists_sub_one_mul_eq_initCols_mul ⟨g, hg⟩
    rw [Subsingleton.elim N 0, Matrix.mul_zero] at hN
    ext i b
    exact congrFun₂ hN i 0
  have h_cols : Y * (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) =
      (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) * fromBlocks ((y : Matrix n n ℂ) - 1) 0 0 0 := by
    simp [hw, mul_fromCols, fromCols_mul_fromBlocks, h_image, h_vec]
  refine ⟨y, Subtype.ext (Units.ext (sub_left_injective (b := 1) ?_))⟩
  exact (Units.mul_left_inj _).1 ((conj_inl_sub_one_mul w y).trans h_cols.symm)

omit [Fintype X] [DecidableEq n] in
/-- If `l` is steep (so its weight is `0` on `X` and in `[-3 B, -B]` elsewhere) and has a large gap,
the weight of the lowest `K`-type of `-l` lies in `[0, 3 B]`. -/
lemma IsSteep.lowestKType_neg_mem {B : ℝ} {l : HCParam ε} {M h : ℕ} {e : X ⊕ Fin M ≃ n}
    (h_steep : IsSteep l B e) (hl_gap : l.HasLargeGap h) (hB : 0 ≤ B) (i : n) :
    ((-l).lowestKType i : ℝ) ∈ Set.Icc 0 (3 * B) := by
  obtain ⟨x | a, rfl⟩ := e.surjective i
  · simpa [h_steep.weight_eq_zero] using hB
  · obtain ⟨h_lower, h_upper⟩ := h_steep.weight_mem a
    have h_neg : ((-l).lowestKType (e (Sum.inr a)) : ℝ) = -l.lowestKType (e (Sum.inr a)) := by simp
    exact ⟨by linarith, by linarith⟩

/-- If the entries of `i₀` and of the only column of `v` have norm at most `R`, then the square
matrix `(i₀, v)` of size `card n + 1` has squared operator norm at most `(card n + 1)⁴ R²`. -/
lemma sq_norm_fromCols_le {v : Matrix (n ⊕ Unit) (Fin 1) ℂ} {i₀ : Matrix (n ⊕ Unit) n ℂ} {R : ℝ}
    (hv : ∀ (i : n ⊕ Unit) (a : Fin 1), ‖v i a‖ ≤ R)
    (hi₀ : ∀ (i : n ⊕ Unit) (a : n), ‖i₀ i a‖ ≤ R) :
    ‖fromCols i₀ (replicateCol Unit (v.col 0))‖ ^ 2 ≤ card (n ⊕ Unit) ^ 4 * R ^ 2 := by
  calc _ ≤ (card (n ⊕ Unit) * card (n ⊕ Unit) * R) ^ 2 := by
        gcongr
        refine l2_opNorm_le_of_apply fun i a ↦ ?_
        rcases a with a | a
        exacts [hi₀ i a, hv i 0]
    _ = card (n ⊕ Unit) ^ 4 * R ^ 2 := by ring

/-- Let the integer vectors `l = 2 λ` for `U(ε)` and `-l'` for `U(ε ⊕ 1)` be steep with `B ≥ 1`: on
`X` the signs are `+1` and the weight of the lowest `K`-type is `0`; on the other `M`, resp.
`M + 1`, coordinates the signs are `+, -, +, …` and the weight decreases strictly in `[-3 B, -B]`.
Let `M` be even and let `λ` be a Harish-Chandra parameter with gap `500 (card n)³ + h` between
entries of opposite signs. Then `-l'`, `-l` have a stationary position with one vector `v`: an
isometry `i₀` of `(ℂ^n, ε)` into the orthogonal complement of `v`, the identity on `ℂ^X`, with
`i₀† μ' i₀ = μ` for the weights `μ'`, `μ` of `-l'`, `-l` as diagonal matrices. The form of signs
`ε ⊕ 1` has value `1` at `v`, and the entries of `v`, `i₀` have modulus at most `(6 B) ^ (M + 1)`.
-/
lemma IsSteep.exists_isStationary_conjTranspose_mul_mul_eq_one {B : ℝ} {l : HCParam ε}
    {l' : HCParam (Sum.elim ε (1 : Unit → ℤˣ))} {M h : ℕ} {e : X ⊕ Fin M ≃ n}
    {e' : X ⊕ Fin (M + 1) ≃ n ⊕ Unit} (hM : Even M) (h_steep : IsSteep l B e)
    (h_steep' : IsSteep (-l') B e') (hB : 1 ≤ B) (hl_gap : l.HasLargeGap h) :
    ∃ (v : Matrix (n ⊕ Unit) (Fin 1) ℂ) (i₀ : Matrix (n ⊕ Unit) n ℂ),
      IsStationary (-l') (-l) e' e 0 v i₀ ∧
      (vᴴ * signMatrix (Sum.elim ε (1 : Unit → ℤˣ)) * v) 0 0 = 1 ∧
      (∀ (i : n ⊕ Unit) (a : Fin 1), ‖v i a‖ ≤ (6 * B) ^ (M + 1)) ∧
      ∀ (i : n ⊕ Unit) (a : n), ‖i₀ i a‖ ≤ (6 * B) ^ (M + 1) := by
  classical
  have h_mono : StrictMono fun a : Fin M ↦ (-l).lowestKType (e (Sum.inr a)) := by
    simpa using h_steep.weight_strictAnti.neg
  obtain ⟨v, i₀, hP, h_norm, h_vec_le, h_isometry_le, -⟩ :=
    h_steep'.exists_isStationary (k := -l) (d := 0) hB rfl h_steep.sign_inl
      (by simp [h_steep.weight_eq_zero]) h_steep.sign_inr h_mono (by linarith) fun a ↦
        h_steep.lowestKType_neg_mem hl_gap (by linarith) (e (Sum.inr a))
  rw [show 6 * B = 3 * B + 3 * B by ring]
  -- The form takes the value `(-1) ^ M` at `v`, and `M` is even.
  exact ⟨v, i₀, hP, h_norm.trans hM.neg_one_pow, h_vec_le, h_isometry_le⟩

/-- **Restriction.** Let the parameter `l = 2 λ` of `U(ε)` be steep for `(X, M, B)` with `M` even
and `B ≥ 1`, and let `l' = 2 λ'` be a parameter of `U(ε ⊕ 1)` with `-l'` steep for `(X, M + 1, B)`.
With `n = card n`, let `HasLargeGap h` hold for both: the entries of `l` (resp. `l'`) are distinct
and of the parity of `n - 1` (resp. `n`), and two entries of `λ` (resp. `λ'`) at coordinates of
opposite sign differ by at least `500 n³ + h` (resp. `500 (n + 1)³ + h`). Let the entries of `l`,
`l'` be bounded by `L`, let `β ≥ 10¹²` bound `2 n + 1 + L` and `(n + 1)⁴ (6 B) ^ (2 M + 2)`, and let
`h ≥ 10³⁰ ((2 n + 1)² log β)³`.

Let `c_l`, `c_l'` be the discrete series coefficients `HCParam.dsCoeff`, given by Flensted-Jensen's
integral over the maximal compact subgroup, divided by the squared norm of the lowest `K`-type. The
measure `volume` on `U(ε)` is the Haar measure `haarU` made from Lebesgue measure by a Cayley chart,
with the compact dual normalisation. Then some `y` in `U(ε ⊕ 1)` with `‖y‖² ≤ β` has:
`β ^ (20 (2 n + 1)²)` times the modulus of the integral over `U(ε)` of
`c_l g * conj (c_l' (y⁻¹ (g ⊕ 1) y))` is at least the volume of `{g | ‖g - 1‖ ≤ 1}`. -/
theorem IsSteep.exists_volume_le_mul_norm_integral_dsCoeff [Nonempty n] {B β : ℝ} {l : HCParam ε}
    {l' : HCParam (Sum.elim ε (1 : Unit → ℤˣ))} {M L h : ℕ} {e : X ⊕ Fin M ≃ n}
    {e' : X ⊕ Fin (M + 1) ≃ n ⊕ Unit} (hM : Even M)
    (h_steep : IsSteep l B e) (h_steep' : IsSteep (-l') B e') (hB : 1 ≤ B)
    (hl : l.HasLargeGap h) (hl' : l'.HasLargeGap h)
    (hL : ∀ a : n, |l a| ≤ L) (hL' : ∀ a : n ⊕ Unit, |l' a| ≤ L) (hβ : 10 ^ 12 ≤ β)
    (hn : card (n ⊕ Unit) + card n + L ≤ β)
    (h_size : card (n ⊕ Unit) ^ 4 * (6 * B) ^ (2 * M + 2) ≤ β)
    (hh : 10 ^ 30 * ((card (n ⊕ Unit) + card n) ^ 2 * β.log) ^ 3 ≤ h) :
    ∃ y : USign (Sum.elim ε (1 : Unit → ℤˣ)),
      ‖(y : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β ∧
      volume.real {g : USign ε | ‖(g : Matrix n n ℂ) - 1‖ ≤ 1} ≤
        β ^ (20 * (card (n ⊕ Unit) + card n) ^ 2) *
          ‖∫ g : USign ε, l.dsCoeff g *
            conj (l'.dsCoeff (y⁻¹ * U.inl ε 1 g * y : USign (Sum.elim ε 1)))‖ := by
  -- Take a stationary position `(v, i₀)` of `U(ε)` in `U(ε ⊕ 1)` for the parameters `-l'`, `-l`,
  -- put `w = (i₀, v)` and `y = w⁻¹`, and bound the period over its group `w U(ε) w⁻¹` from below.
  classical
  have h_mem (i : n) : ((-l).lowestKType i : ℝ) ∈ Set.Icc 0 (3 * B) :=
    h_steep.lowestKType_neg_mem hl (by linarith) i
  obtain ⟨v, i₀, hP, h_norm, h_vec_le, h_isometry_le⟩ :=
    h_steep.exists_isStationary_conjTranspose_mul_mul_eq_one hM h_steep' hB hl
  let w : USign (Sum.elim ε (1 : Unit → ℤˣ)) :=
    U.of IsHermitianInvolution.isUnit (fromCols i₀ (replicateCol Unit (v.col 0)))
      (hP.gram_fromCols h_norm)
  have hw : (w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) = fromCols i₀ (replicateCol Unit (v.col 0)) :=
    rfl
  have hw_norm : ‖(w : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ^ 2 ≤ β :=
    calc _ ≤ card (n ⊕ Unit) ^ 4 * ((6 * B) ^ (M + 1)) ^ 2 :=
          sq_norm_fromCols_le h_vec_le h_isometry_le
      _ ≤ β := le_of_eq_of_le (by ring) h_size
  -- The first component of `j g = (w (g ⊕ 1) w⁻¹, g)` maps `U(ε)` onto the group of the position.
  let j : USign ε →* USign (Sum.elim ε (1 : Unit → ℤˣ)) × USign ε :=
    ((MulAut.conj w).toMonoidHom.comp (U.inl ε 1)).prod (MonoidHom.id (USign ε))
  have h_proper : IsProperMap fun g : USign ε ↦ (j g).1 :=
    (Homeomorph.smul (ConjAct.toConjAct w)).isProperMap.comp isProperMap_inl
  have h_zero (x : X) : (-l).lowestKType (e (Sum.inl x)) = 0 := by simp [h_steep.weight_eq_zero]
  have h_lowers (g : USign ε) :
      LowersFlag 0 v (((j g).1 : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1) 0 :=
    lowersFlag_conj_inl_sub_one hw g
  have h_induces (g : USign ε) : InducesOn 0 v i₀
      (((j g).1 : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ) - 1) (((j g).2 : Matrix n n ℂ) - 1) :=
    inducesOn_conj_inl_sub_one hw g
  let Large : Set (USign ε) := {g : USign ε |
    ‖((j g).1 : Matrix (n ⊕ Unit) (n ⊕ Unit) ℂ)‖ ≤ β + 1 ∧ ‖((j g).2 : Matrix n n ℂ)‖ ≤ β + 1}
  have h_period : volume Large ≤ ENNReal.ofReal (β ^ (20 * (card (n ⊕ Unit) + card n) ^ 2) *
      ‖∫ g : USign ε, (-l').laplaceIntegrand (-l) j (fun _ ↦ 0 - conj 0) g‖) :=
    hP.period_lower_bound_of_surjective h_steep' hB h_steep.sign_inl h_zero
      (fun i ↦ mod_cast (h_mem i).left) (fun i _ _ ↦ (h_mem i).right) hl'.neg hl.neg
      (by simpa using hL') (by simpa using hL) hβ hn hh volume h_proper
      (fun _ ↦ hP.exists_conj_inl_eq hw) h_lowers h_induces
  -- The function `laplaceIntegrand` is the integrand of the pairing, and the ball `‖g - 1‖ ≤ 1`
  -- lies in the set whose volume `h_period` bounds.
  have h_integrand (g : USign ε) : (-l').laplaceIntegrand (-l) j (fun _ ↦ 0 - conj 0) g =
      l.dsCoeff g * conj (l'.dsCoeff (w * U.inl ε 1 g * w⁻¹ : USign (Sum.elim ε 1))) := by
    rw [HCParam.laplaceIntegrand, dsCoeff_neg hl, dsCoeff_neg hl']
    simp [j, mul_comm]
  have h_ball : {g : USign ε | ‖(g : Matrix n n ℂ) - 1‖ ≤ 1} ⊆ Large := fun g hg ↦
    ⟨(norm_conj_inl_le w hg).trans (by linarith),
      norm_le_add_one_of_norm_sub_one_le (by linarith) hg⟩
  refine ⟨w⁻¹, by rwa [U.norm_inv], ENNReal.toReal_le_of_le_ofReal (by positivity) ?_⟩
  simpa only [h_integrand, inv_inv] using (measure_mono h_ball).trans h_period

end New.DiscreteSeries

end RestrictionLemma
