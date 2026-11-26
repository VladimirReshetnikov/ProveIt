import Lib.General.Algebra.FittingIdealsAndLengths

/-!
# Maximal minors and lengths

Let `A` be a matrix over a discrete valuation ring `O` and let `a ≠ 0`. The length of the kernel of
`A` on `(O / a) ^ k` is the least valuation of a maximal minor of the matrix formed by the rows of
`A` and of `a • 1`. The kernel is isomorphic to the module of linear maps to `O / a` from the
quotient of `O ^ k` by these rows, so it has the length of this quotient, which is computed by the
Smith normal form and the multilinearity of the determinant.

* `New.Selmer.maximalMinors`, `New.Selmer.matrixKernel`: the minors and the kernel.
* `New.Selmer.isLeast_length_matrixKernel`: the statement for a matrix over a commutative ring `Λ`
  and a ring homomorphism `ev : Λ →+* O` with `ev a ≠ 0`.

Notions from other files:

* `New.QuotSpan a`: the quotient ring `O / a O`.
* `New.intGL k R`: the invertible matrices that, with their inverses, have entries in the subring
  `R`. The Smith normal form is stated for these, and here `R` is all of `O`.

## Relation to the literature

Known result: Length of a matrix kernel modulo `a` over a discrete valuation ring via maximal
minors. A consequence of the theorem on elementary divisors.
-/

noncomputable section

namespace New.Selmer

open Matrix Module Submodule IsDiscreteValuationRing

variable {Λ O r k : Type*} [CommRing Λ] [CommRing O] [Fintype k] [DecidableEq k]

/-- The minors of size `card k` of the matrix formed by the rows of `A` and of `a • 1`, where `k`
indexes the columns. The family of rows of `A` may be infinite. A choice of rows with a repetition
is allowed; it contributes the minor `0`. -/
def maximalMinors (A : Matrix r k Λ) (a : Λ) : Set Λ :=
  Set.range fun f : k → r ⊕ k ↦ ((A.fromRows (a • 1)).submatrix f id).det

/-- The kernel of `A` on `B ^ k`, for an `O`-module `B`: the vectors `w` such that
`∑ j, A i j • w j = 0` for every row index `i`. -/
def matrixKernel (A : Matrix r k O) (B : Type*) [AddCommGroup B] [Module O B] :
    Submodule O (k → B) :=
  ⨅ i : r, LinearMap.ker (∑ j : k, A i j • LinearMap.proj j : (k → B) →ₗ[O] B)

/-- The submodule of `O ^ k` spanned by the rows of `A` and of `a • 1`. -/
def rowLattice (A : Matrix r k O) (a : O) : Submodule O (k → O) :=
  span O (Set.range (A.fromRows (a • (1 : Matrix k k O))).row)

/-- A ring homomorphism `ev` maps the maximal minors of the rows of `A` and `a • 1` onto those of
the rows of `A.map ev` and `ev a • 1`. -/
lemma image_maximalMinors (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) :
    ev '' maximalMinors A a = maximalMinors (A.map ev) (ev a) := by
  have h_map : (A.fromRows (a • (1 : Matrix k k Λ))).map ev = (A.map ev).fromRows (ev a • 1) := by
    ext (i | i) j <;> simp [one_apply, apply_ite ev]
  simp [maximalMinors, ← Set.range_comp, Function.comp_def, ev.map_det, ← h_map, submatrix_map]

omit [DecidableEq k] in
/-- A vector lies in `matrixKernel A B` exactly if every row of `A` sends it to `0`. -/
lemma mem_matrixKernel {A : Matrix r k O} {B : Type*} [AddCommGroup B] [Module O B] {w : k → B} :
    w ∈ matrixKernel A B ↔ ∀ i : r, ∑ j : k, A i j • w j = 0 := by
  simp [matrixKernel]

lemma smul_mem_rowLattice (A : Matrix r k O) (a : O) (v : k → O) : a • v ∈ rowLattice A a := by
  rw [pi_eq_sum_univ' v, Finset.smul_sum]
  refine sum_mem fun j _ ↦ ?_
  rw [smul_comm]
  exact smul_mem _ _ (subset_span ⟨.inr j, by ext i; simp [one_apply, Pi.single_apply, eq_comm]⟩)

/-- The kernel of `A` on `(O / a) ^ k` (`QuotSpan a` is `O / a`) has the length of the module of
linear maps to `O / a` from the quotient of `O ^ k` by `rowLattice A a`, the span of the rows of
`A` and `a • 1`: a map corresponds to its values at the standard basis. -/
lemma length_matrixKernel_eq_length_linearMap (A : Matrix r k O) (a : O) :
    length O (matrixKernel A (QuotSpan a)) =
      length O (((k → O) ⧸ rowLattice A a) →ₗ[O] QuotSpan a) := by
  let val : (((k → O) ⧸ rowLattice A a) →ₗ[O] QuotSpan a) →ₗ[O] k → QuotSpan a :=
    LinearMap.pi fun j ↦ LinearMap.applyₗ ((rowLattice A a).mkQ (Pi.single j 1))
  have h_inj : Function.Injective val := fun g g' h_val ↦
    linearMap_qext _ ((Pi.basisFun O k).ext fun j ↦ by simpa [val] using congrFun h_val j)
  have h_range : val.range = matrixKernel A (QuotSpan a) := by
    ext w
    rw [mem_matrixKernel]
    refine ⟨?_, fun hw ↦ ?_⟩
    · rintro ⟨g, rfl⟩ i
      have h_row : (rowLattice A a).mkQ (A i) = 0 :=
        (Quotient.mk_eq_zero _).2 (subset_span ⟨.inl i, rfl⟩)
      calc ∑ j, A i j • val g j
        _ = g ((rowLattice A a).mkQ (∑ j, A i j • Pi.single j 1)) := by simp [val]
        _ = 0 := by rw [← pi_eq_sum_univ', h_row, map_zero]
    · have h_kill : rowLattice A a ≤ (Fintype.linearCombination O w).ker := span_le.2 <| by
        rintro _ ⟨i | i, rfl⟩
        · exact hw i
        · change ∑ j : k, (a * (1 : Matrix k k O) i j) • w j = 0
          exact Finset.sum_eq_zero fun j _ ↦ smul_quot_eq_zero_of_dvd (dvd_mul_right a _) (w j)
      exact ⟨liftQ _ _ h_kill, funext fun j : k ↦ by simp [val]⟩
  rw [← h_range, (LinearEquiv.ofInjective val h_inj).length_eq]

variable [DVR O]

/-- In a discrete valuation ring let `d ∣ a ≠ 0`. The module of linear maps `O / d → O / a` has
the length of `O / d` (`QuotSpan x` is `O / x`). -/
lemma length_linearMap_quotSpan_of_dvd {a d : O} (ha : a ≠ 0) (hd : d ∣ a) :
    length O (QuotSpan d →ₗ[O] QuotSpan a) = length O (QuotSpan d) := by
  -- The linear maps `O / d → O / a` are the multiples of multiplication by `a / d`.
  obtain ⟨c, rfl⟩ := hd
  have h_mul_le : Ideal.span {d} ≤ Submodule.comap (LinearMap.lsmul O O c) (Ideal.span {d * c}) :=
    (Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_span_singleton.2 (by simp [mul_comm]))
  let mulC : QuotSpan d →ₗ[O] QuotSpan (d * c) := mapQ _ _ (LinearMap.lsmul O O c) h_mul_le
  let φ : O →ₗ[O] QuotSpan d →ₗ[O] QuotSpan (d * c) := LinearMap.toSpanSingleton O _ mulC
  -- `φ t` is multiplication by `t * c`.
  have hφ (t : O) : φ t 1 = Ideal.Quotient.mk _ (t * c) :=
    congrArg (Ideal.Quotient.mk _) (by simp)
  have h_ext {g g' : QuotSpan d →ₗ[O] QuotSpan (d * c)} (h_one : g 1 = g' 1) : g = g' :=
    linearMap_qext _ (LinearMap.ext_ring h_one)
  have h_ker : φ.ker = Ideal.span {d} := by
    ext t
    rw [LinearMap.mem_ker, Ideal.mem_span_singleton, ← mul_dvd_mul_iff_right
      (right_ne_zero_of_mul ha), ← Ideal.Quotient.eq_zero_iff_dvd, ← hφ]
    exact ⟨fun h ↦ by rw [h, LinearMap.zero_apply], fun h ↦ h_ext h⟩
  have h_surj : Function.Surjective φ := fun g ↦ by
    -- The value `y` of `g` at `1` is killed by `d`, so `d * c ∣ d * y`.
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (g 1)
    have h_zero : Ideal.Quotient.mk (Ideal.span {d * c}) (d * y) = 0 := by
      change d • Ideal.Quotient.mk (Ideal.span {d * c}) y = 0
      rw [hy, ← map_smul, smul_quot_eq_zero_of_dvd dvd_rfl, map_zero]
    obtain ⟨t, rfl⟩ : c ∣ y := by
      rwa [Ideal.Quotient.eq_zero_iff_dvd, mul_dvd_mul_iff_left (left_ne_zero_of_mul ha)] at h_zero
    exact ⟨t, h_ext (by rw [hφ, mul_comm t, hy])⟩
  exact ((quotEquivOfEq _ _ h_ker.symm).trans (φ.quotKerEquivOfSurjective h_surj)).length_eq.symm

/-- Over a discrete valuation ring `O`, a finitely generated module `Q` that `a ≠ 0` annihilates
has the same length as the module of its linear maps to `QuotSpan a`, that is, `O / a`. This
follows from the structure theorem for such modules. -/
lemma length_linearMap_quotSpan {Q : Type*} [AddCommGroup Q] [Module O Q] [Module.Finite O Q]
    {a : O} (ha : a ≠ 0) (h_kill : ∀ x : Q, a • x = 0) :
    length O (Q →ₗ[O] QuotSpan a) = length O Q := by
  classical
  -- `Q` is a product of cyclic modules `O / d i`, and `d i ∣ a` as `a` kills each factor.
  have h_torsion : IsTorsion O Q := fun x ↦ ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, h_kill x⟩
  -- The structure theorem: `e` maps `Q` onto the sum of the modules `O / p i ^ n i`.
  obtain ⟨ι, _, p, -, n, ⟨e⟩⟩ := equiv_directSum_of_isTorsion h_torsion
  let d (i : ι) : O := p i ^ n i
  let e' : Q ≃ₗ[O] ∀ i, QuotSpan (d i) := e.trans DFinsupp.linearEquivFunOnFintype
  have h_dvd (i : ι) : d i ∣ a := by
    have h_one : a • (1 : QuotSpan (d i)) = 0 := by
      simpa using congrFun (congrArg e' (h_kill (e'.symm (Pi.single i 1)))) i
    simpa [← Ideal.Quotient.eq_zero_iff_dvd, Algebra.smul_def] using h_one
  calc length O (Q →ₗ[O] QuotSpan a) = length O (∀ i, QuotSpan (d i) →ₗ[O] QuotSpan a) :=
      ((LinearMap.lsum O _ O).trans (e'.symm.congrLeft _ O)).length_eq.symm
    _ = length O Q := by
      simp [e'.length_eq, length_pi_of_fintype, length_linearMap_quotSpan_of_dvd ha (h_dvd _)]

omit [DVR O] in
/-- A vector is a combination of the rows of `U * diagonal d * V`, with `U` and `V` invertible,
exactly if `d i` divides the coordinate `i` of its product with `V⁻¹` for every `i`. -/
lemma mem_span_row_mul_diagonal_mul_iff {U V : GL k O} {d v : k → O} :
    v ∈ span O (Set.range (U.val * diagonal d * V.val).row) ↔
      ∀ i : k, d i ∣ (v ᵥ* (V⁻¹).val) i := by
  simp only [← range_vecMulLinear, LinearMap.mem_range, vecMulLinear_apply]
  constructor
  · rintro ⟨u, rfl⟩ i
    rw [vecMul_vecMul, V.mul_inv_cancel_right, ← vecMul_vecMul, vecMul_diagonal]
    exact dvd_mul_left _ _
  · intro h_dvd
    choose u hu using h_dvd
    have h_diag : u ᵥ* diagonal d = v ᵥ* (V⁻¹).val := funext fun i ↦ by
      rw [vecMul_diagonal, mul_comm, hu i]
    refine ⟨u ᵥ* (U⁻¹).val, ?_⟩
    calc u ᵥ* (U⁻¹).val ᵥ* (U.val * diagonal d * V.val) = u ᵥ* diagonal d ᵥ* V.val := by
          rw [vecMul_vecMul, ← mul_assoc, ← mul_assoc, U.inv_mul, one_mul, ← vecMul_vecMul]
      _ = v := by rw [h_diag, vecMul_vecMul, V.inv_mul, vecMul_one]

/-- Elementary divisors: over a discrete valuation ring `O`, the quotient of `O ^ k` by the rows of
a square matrix `N` has the valuation of `det N` as its length. -/
lemma length_quotient_span_row (N : Matrix k k O) :
    length O ((k → O) ⧸ span O (Set.range N.row)) = addVal O N.det := by
  -- The Smith normal form is stated for the classical decidable equality on `k`.
  obtain rfl : ‹DecidableEq k› = Classical.decEq k := Subsingleton.elim _ _
  let : DecidableEq k := Classical.decEq k
  -- For `N = Q * diagonal d * P` the rows span the kernel of the surjection onto the product of
  -- the `O / d i` that sends `v` to the classes of the coordinates of `v P⁻¹`.
  obtain ⟨Q, -, P, -, d, rfl⟩ : ∃ᵉ (Q ∈ intGL k (⊤ : Subring O)) (P ∈ intGL k (⊤ : Subring O))
      (d : k → O), N = Q.val * diagonal d * P.val := isValuationPair_top.smith_normal_form N
  let π : (k → O) →ₗ[O] ∀ i, QuotSpan (d i) :=
    LinearMap.piMap (fun i ↦ (Ideal.span {d i}).mkQ) ∘ₗ P⁻¹.1.vecMulLinear
  have h_surj : Function.Surjective π :=
    (Function.Surjective.piMap fun _ ↦ mkQ_surjective _).comp fun v ↦ ⟨v ᵥ* P.1, by simp⟩
  have h_ker : π.ker = span O (Set.range (Q.1 * diagonal d * P.1).row) := by
    ext v
    rw [mem_span_row_mul_diagonal_mul_iff, LinearMap.mem_ker, funext_iff]
    exact forall_congr' fun i ↦ Ideal.Quotient.eq_zero_iff_dvd (d i) _
  have h_unit (U : GL k O) : addVal O U.1.det = 0 :=
    addVal_eq_zero_iff.2 ((isUnit_iff_isUnit_det _).1 U.isUnit)
  calc length O ((k → O) ⧸ span O (Set.range (Q.1 * diagonal d * P.1).row))
    _ = length O (∀ i, QuotSpan (d i)) := by
        rw [← h_ker, (π.quotKerEquivOfSurjective h_surj).length_eq]
    _ = addVal O (∏ i, d i) := by
        simp only [length_pi_of_fintype, length_quot_span_eq_addVal, addVal_prod]
    _ = addVal O (Q.1 * diagonal d * P.1).det := by simp [h_unit]

/-- Over a discrete valuation ring and for `a ≠ 0` the lattice `rowLattice A a` of the rows of
`A` and `a • 1` is free of full rank, so it is spanned by the rows of a square matrix. -/
lemma exists_span_row_eq_rowLattice (A : Matrix r k O) {a : O} (ha : a ≠ 0) :
    ∃ N : Matrix k k O, span O (Set.range N.row) = rowLattice A a := by
  -- Multiplication by `a` embeds `O ^ k` into the lattice, so the lattice has rank `card k`.
  let g : (k → O) →ₗ[O] rowLattice A a :=
    (LinearMap.lsmul O _ a).codRestrict _ (smul_mem_rowLattice A a)
  have h_inj : Function.Injective g := (LinearMap.lsmul_injective ha).codRestrict _
  have h_rank : finrank O (k → O) = finrank O (rowLattice A a) :=
    (g.finrank_le_finrank_of_injective h_inj).antisymm (finrank_le _)
  let b : Basis k O (rowLattice A a) := (Pi.basisFun O k).map (.ofFinrankEq _ _ h_rank)
  refine ⟨of fun i ↦ (b i : k → O), ?_⟩
  change span O (Set.range ((rowLattice A a).subtype ∘ b)) = rowLattice A a
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, map_subtype_top]

omit [DVR O] in
/-- If every row of the square matrix `N` is a combination of the rows of `M`, then `det N` is a
combination of the determinants of choices of rows of `M`, so each common divisor `x` of these
divides it. -/
lemma dvd_det_of_forall_row_mem_span {m : Type*} {M : Matrix m k O} {N : Matrix k k O} {x : O}
    (h_minor : ∀ f : k → m, x ∣ (M.submatrix f id).det)
    (h_row : ∀ i : k, N.row i ∈ span O (Set.range M.row)) : x ∣ N.det := by
  choose c hc using fun i : k ↦ Finsupp.mem_span_range_iff_exists_finsupp.1 (h_row i)
  have h_det : N.det =
      detRowAlternating.toMultilinearMap fun i ↦ ∑ t ∈ (c i).support, c i t • M.row t :=
    congrArg det (funext fun i ↦ (hc i).symm)
  simp only [h_det, MultilinearMap.map_sum_finset, MultilinearMap.map_smul_univ]
  exact Finset.dvd_sum fun f _ ↦ (h_minor f).mul_left _

/-- Over a discrete valuation ring and for `a ≠ 0`, the quotient of `O ^ k` by `rowLattice A a`,
the span of the rows of `A` and `a • 1`, has as its length the least valuation of a maximal minor
of these rows. -/
lemma isLeast_length_quotient_rowLattice (A : Matrix r k O) {a : O} (ha : a ≠ 0) :
    IsLeast (addVal O '' maximalMinors A a) (length O ((k → O) ⧸ rowLattice A a)) := by
  let M : Matrix (r ⊕ k) k O := A.fromRows (a • 1)
  let v (f : k → r ⊕ k) : ℕ∞ := addVal O (M.submatrix f id).det
  -- The rows chosen by `f` span a sublattice, whose quotient is at least as long.
  have h_lower (f : k → r ⊕ k) : length O ((k → O) ⧸ rowLattice A a) ≤ v f := by
    have h_le : span O (Set.range (M.submatrix f id).row) ≤ rowLattice A a :=
      span_mono (Set.range_comp_subset_range f M.row)
    simpa only [length_quotient_span_row] using length_le_of_surjective _ (factor_surjective h_le)
  -- The length is the valuation of `det N`, for a matrix `N` whose rows span the lattice. These
  -- rows are combinations of the rows of `M`, so `det N` is a combination of minors, and the
  -- minor of least valuation `v (Function.argmin v)` divides it.
  obtain ⟨N, hN⟩ := exists_span_row_eq_rowLattice A ha
  have : Nonempty (k → r ⊕ k) := ⟨.inr⟩
  let f₀ : k → r ⊕ k := Function.argmin v
  have h_dvd : (M.submatrix f₀ id).det ∣ N.det :=
    dvd_det_of_forall_row_mem_span (fun f ↦ addVal_le_iff_dvd.1 (Function.argmin_le v f))
      fun i ↦ hN.le (subset_span ⟨i, rfl⟩)
  have h_upper : v f₀ ≤ length O ((k → O) ⧸ rowLattice A a) :=
    (addVal_le_iff_dvd.2 h_dvd).trans_eq (by rw [← hN, length_quotient_span_row])
  exact ⟨⟨(M.submatrix f₀ id).det, ⟨f₀, rfl⟩, h_upper.antisymm (h_lower f₀)⟩,
    Set.forall_mem_image.2 (Set.forall_mem_range.2 h_lower)⟩

/-- Let `A` be a matrix over `Λ` with columns indexed by `k`, let `ev : Λ →+* O` be a ring
homomorphism to a discrete valuation ring (`[DVR O]`), and let `ev a ≠ 0`. The length of
`matrixKernel (A.map ev) (QuotSpan (ev a))`, the kernel of `A.map ev` on `(O / ev a) ^ k`, is the
least `addVal (ev P)`, where `P` runs over `maximalMinors A a`, the maximal minors of the matrix
formed by the rows of `A` and of `a • 1`. -/
theorem isLeast_length_matrixKernel (A : Matrix r k Λ) (a : Λ) (ev : Λ →+* O) (ha : ev a ≠ 0) :
    IsLeast ((fun P : Λ ↦ addVal O (ev P)) '' maximalMinors A a)
      (length O (matrixKernel (A.map ev) (QuotSpan (ev a)))) := by
  have h_kill (x : (k → O) ⧸ rowLattice (A.map ev) (ev a)) : ev a • x = 0 := by
    obtain ⟨v, rfl⟩ := mkQ_surjective _ x
    simpa [← Quotient.mk_smul] using smul_mem_rowLattice _ _ v
  rw [length_matrixKernel_eq_length_linearMap, length_linearMap_quotSpan ha h_kill,
    ← Set.image_image (addVal O) ev, image_maximalMinors]
  exact isLeast_length_quotient_rowLattice _ ha

end New.Selmer

end
