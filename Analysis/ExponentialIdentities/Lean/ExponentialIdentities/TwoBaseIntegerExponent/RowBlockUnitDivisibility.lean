import ExponentialIdentities.TwoBaseIntegerExponent.RowBlockLaplaceExpansion
import ExponentialIdentities.TwoBaseIntegerExponent.UnitOrderingGain

/-!
# Unit fixed divisors throughout the row-block cascade

Every row-block assignment has the prescribed column-fiber sizes.  Hence a
fixed-divisor bound for each square block gives the same divisor for every
minor product in the Laplace expansion.  The resulting exponent depends on
the block sizes, but not on the assignment or its tropical excess.  It is
therefore a uniform lower bound on every truncated cascade sum; it does not
distinguish higher layers or upper-bound their remaining cancellation.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset Matrix

/-- The total fixed-divisor weight obtained by summing a degree weight over
all columns in all blocks. -/
def rowBlockOrderingExponent
    {o : Type*} [Fintype o] (s : o → ℕ) (w : ℕ → ℕ) : ℕ :=
  ∑ k : o, ∑ j : Fin (s k), w (j : ℕ)

theorem rowBlockOrderingExponent_two_eq_sum_blockGain
    {o : Type*} [Fintype o] (s : o → ℕ) :
    rowBlockOrderingExponent s twoUnitOrderingWeight =
      ∑ k : o, twoUnitBlockGain (s k) := by
  simp only [rowBlockOrderingExponent, twoUnitBlockGain,
    Fin.sum_univ_eq_sum_range]

theorem rowBlockOrderingExponent_three_eq_sum_blockGain
    {o : Type*} [Fintype o] (s : o → ℕ) :
    rowBlockOrderingExponent s threeUnitOrderingWeight =
      ∑ k : o, threeUnitBlockGain (s k) := by
  simp only [rowBlockOrderingExponent, threeUnitBlockGain,
    Fin.sum_univ_eq_sum_range]

/-- Blockwise divisibility multiplies to divisibility of the signed minor
product associated with any row-block assignment. -/
theorem pow_rowBlockOrderingExponent_dvd_minorProduct_of_block_dvd
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (b : Fin N → o) (A : Matrix (Fin N) (Fin N) ℤ)
    (a : RowBlockAssignment b) (p : ℤ) (s : o → ℕ) (w : ℕ → ℕ)
    (hblock : ∀ k : o,
      p ^ (∑ j : Fin (s k), w (j : ℕ)) ∣
        ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det) :
    p ^ rowBlockOrderingExponent s w ∣ rowBlockMinorProduct b A a := by
  classical
  rw [rowBlockOrderingExponent, ← Finset.prod_pow_eq_pow_sum Finset.univ
    (fun k : o ↦ ∑ j : Fin (s k), w (j : ℕ)) p]
  apply Dvd.dvd.mul_left
  exact Finset.prod_dvd_prod_of_dvd
    (fun k : o ↦ p ^ (∑ j : Fin (s k), w (j : ℕ)))
    (fun k : o ↦ ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det)
    (fun k _ ↦ hblock k)

/-- A common divisor of every row-block minor product divides every weighted
subsum of the assignment cascade. -/
theorem pow_dvd_weighted_rowBlockAssignmentSum
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {b : Fin N → o} (p : ℤ) (W : ℕ)
    (S : Finset (RowBlockAssignment b))
    (e : RowBlockAssignment b → ℕ) (c : RowBlockAssignment b → ℤ)
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hminor : ∀ a ∈ S, p ^ W ∣ rowBlockMinorProduct b A a) :
    p ^ W ∣ ∑ a ∈ S, p ^ e a * c a * rowBlockMinorProduct b A a := by
  classical
  apply Finset.dvd_sum
  intro a ha
  exact (hminor a ha).mul_left (p ^ e a * c a)

/-- A divisor common to every unit-minor product adds directly to the
tropical minimum in the determinant of a rank-one power matrix. -/
theorem pow_minCost_add_commonMinorExponent_dvd_det_rankOnePowerMatrix
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (p : ℤ) {depth : Fin N → ℕ} {b : Fin N → o} {value : o → ℕ}
    (A : Matrix (Fin N) (Fin N) ℤ)
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : Monotone value)
    (W : ℕ) (hminor : ∀ a : RowBlockAssignment b,
      p ^ W ∣ rowBlockMinorProduct b A a) :
    p ^ (rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) + W) ∣
      (rankOnePowerMatrix p depth b value A).det := by
  classical
  let tau := rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _)
  let S : ℤ := ∑ a : RowBlockAssignment b,
    p ^ (rowBlockAssignmentCost depth value a - tau) *
      rowBlockMinorProduct b A a
  have hS : p ^ W ∣ S := by
    apply Finset.dvd_sum
    intro a _
    exact (hminor a).mul_left _
  obtain ⟨Q, hQ⟩ := hS
  refine ⟨Q, ?_⟩
  rw [det_rankOnePowerMatrix_eq_minPow_mul_sum_assignmentExcess
    p A hdepth hb hvalue]
  change p ^ tau * S = p ^ (tau + W) * Q
  rw [hQ, pow_add]
  ring

/-- A variable-size consecutive-power matrix with a row factor that
may depend on the target column block.  In the mixed determinant this is the
factor `M^(k*u)` at `p=2` or `A^(k*v)` at `p=3`. -/
def fiberScaledConsecutivePowerMatrix
    {N : ℕ} {o R : Type*} [CommRing R]
    (b : Fin N → o) (degree : Fin N → ℕ)
    (scale x : o → Fin N → R) : Matrix (Fin N) (Fin N) R :=
  fun row col ↦ scale (b col) row * x (b col) row ^ degree col

/-- An arbitrary row-assignment block of the scaled matrix is a row-scaled
ordinary Vandermonde matrix. -/
theorem reindex_rowBlockMinor_fiberScaledConsecutivePowerMatrix
    {N : ℕ} {o R : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    [CommRing R] (b : Fin N → o) (s : o → ℕ)
    (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (scale x : o → Fin N → R) (a : RowBlockAssignment b) (k : o) :
    Matrix.reindex (e k) (e k)
        (((fiberScaledConsecutivePowerMatrix b degree scale x).submatrix
          (rowBlockAlignment b a) id).toSquareBlock b k) =
      Matrix.of fun i j : Fin (s k) ↦
        scale k (rowBlockAlignment b a ((e k).symm i).1) *
          x k (rowBlockAlignment b a ((e k).symm i).1) ^ (j : ℕ) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.toSquareBlock_def,
    Matrix.submatrix_apply, Matrix.of_apply,
    fiberScaledConsecutivePowerMatrix, id_eq]
  rw [((e k).symm j).property, hdegree]

/-- Dyadic p-ordering divisibility for every scaled unit-minor product.  The
scale factors are arbitrary integers and therefore include the blockwise row
units occurring in the mixed determinant. -/
theorem two_pow_rowBlockOrderingExponent_dvd_minorProduct_fiberScaledConsecutivePowers
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (b : Fin N → o) (s : o → ℕ)
    (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (scale : o → Fin N → ℤ) (z : o → Fin N → ℕ)
    (a : RowBlockAssignment b) :
    (2 : ℤ) ^ rowBlockOrderingExponent s twoUnitOrderingWeight ∣
      rowBlockMinorProduct b
        (fiberScaledConsecutivePowerMatrix b degree scale
          (fun k i ↦ 2 * (z k i : ℤ) + 1)) a := by
  let A : Matrix (Fin N) (Fin N) ℤ :=
    fiberScaledConsecutivePowerMatrix b degree scale
      (fun k i ↦ 2 * (z k i : ℤ) + 1)
  apply pow_rowBlockOrderingExponent_dvd_minorProduct_of_block_dvd
    b A a 2 s twoUnitOrderingWeight
  intro k
  let zk : Fin (s k) → ℕ :=
    fun i ↦ z k (rowBlockAlignment b a ((e k).symm i).1)
  let ck : Fin (s k) → ℤ :=
    fun i ↦ scale k (rowBlockAlignment b a ((e k).symm i).1)
  have hV := two_pow_sum_degree_add_factorialVal_dvd_det_vandermonde zk
  calc
    (2 : ℤ) ^ (∑ j : Fin (s k), twoUnitOrderingWeight (j : ℕ)) ∣
        (Matrix.vandermonde (fun i ↦ 2 * (zk i : ℤ) + 1)).det := hV
    _ ∣ (∏ i, ck i) *
        (Matrix.vandermonde (fun i ↦ 2 * (zk i : ℤ) + 1)).det :=
      dvd_mul_left _ _
    _ = ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det := by
      rw [← Matrix.det_mul_column]
      rw [← Matrix.det_reindex_self (e k)]
      rw [reindex_rowBlockMinor_fiberScaledConsecutivePowerMatrix
        b s e degree hdegree scale
        (fun k i ↦ 2 * (z k i : ℤ) + 1) a k]
      rfl

/-- Triadic p-ordering divisibility for every scaled unit-minor product. -/
theorem three_pow_rowBlockOrderingExponent_dvd_minorProduct_fiberScaledConsecutivePowers
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (b : Fin N → o) (s : o → ℕ)
    (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (scale : o → Fin N → ℤ)
    (z : o → Fin N → ℕ) (residue : o → Fin N → Fin 2)
    (a : RowBlockAssignment b) :
    (3 : ℤ) ^ rowBlockOrderingExponent s threeUnitOrderingWeight ∣
      rowBlockMinorProduct b
        (fiberScaledConsecutivePowerMatrix b degree scale
          (fun k i ↦ 3 * (z k i : ℤ) + ((residue k i : ℕ) : ℤ) + 1)) a := by
  let A : Matrix (Fin N) (Fin N) ℤ :=
    fiberScaledConsecutivePowerMatrix b degree scale
      (fun k i ↦ 3 * (z k i : ℤ) + ((residue k i : ℕ) : ℤ) + 1)
  apply pow_rowBlockOrderingExponent_dvd_minorProduct_of_block_dvd
    b A a 3 s threeUnitOrderingWeight
  intro k
  let zk : Fin (s k) → ℕ :=
    fun i ↦ z k (rowBlockAlignment b a ((e k).symm i).1)
  let rk : Fin (s k) → Fin 2 :=
    fun i ↦ residue k (rowBlockAlignment b a ((e k).symm i).1)
  let ck : Fin (s k) → ℤ :=
    fun i ↦ scale k (rowBlockAlignment b a ((e k).symm i).1)
  have hV := three_pow_sum_halfDegree_add_factorialVal_dvd_det_vandermonde zk rk
  calc
    (3 : ℤ) ^ (∑ j : Fin (s k), threeUnitOrderingWeight (j : ℕ)) ∣
        (Matrix.vandermonde
          (fun i ↦ 3 * (zk i : ℤ) + ((rk i : ℕ) : ℤ) + 1)).det := hV
    _ ∣ (∏ i, ck i) *
        (Matrix.vandermonde
          (fun i ↦ 3 * (zk i : ℤ) + ((rk i : ℕ) : ℤ) + 1)).det :=
      dvd_mul_left _ _
    _ = ((A.submatrix (rowBlockAlignment b a) id).toSquareBlock b k).det := by
      rw [← Matrix.det_mul_column]
      rw [← Matrix.det_reindex_self (e k)]
      rw [reindex_rowBlockMinor_fiberScaledConsecutivePowerMatrix
        b s e degree hdegree scale
        (fun k i ↦ 3 * (z k i : ℤ) + ((residue k i : ℕ) : ℤ) + 1) a k]
      rfl

/-! ## Direct block-diagonal monic column change -/

/-- The coefficient matrix for changing, separately in each fiber, from
monomials to prescribed polynomial columns. -/
def fiberMonicBasisChange
    {N : ℕ} {o R : Type*} [DecidableEq o] [CommRing R]
    (b : Fin N → o) (degree : Fin N → ℕ)
    (P : Fin N → Polynomial R) :
    Matrix (Fin N) (Fin N) R :=
  fun oldDegree newColumn ↦
    if b oldDegree = b newColumn then
      (P newColumn).coeff (degree oldDegree)
    else 0

theorem fiberMonicBasisChange_blockTriangular
    {N : ℕ} {o R : Type*} [DecidableEq o] [LinearOrder o] [CommRing R]
    (b : Fin N → o) (degree : Fin N → ℕ)
    (P : Fin N → Polynomial R) :
    (fiberMonicBasisChange b degree P).BlockTriangular b := by
  intro i j hij
  simp [fiberMonicBasisChange, ne_of_gt hij]

theorem reindex_toSquareBlock_fiberMonicBasisChange
    {N : ℕ} {o R : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    [CommRing R] (b : Fin N → o) (s : o → ℕ)
    (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (P : Fin N → Polynomial R) (k : o) :
    Matrix.reindex (e k) (e k)
        ((fiberMonicBasisChange b degree P).toSquareBlock b k) =
      Matrix.of fun i j : Fin (s k) ↦
        (P ((e k).symm j).1).coeff (i : ℕ) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.toSquareBlock_def, Matrix.of_apply,
    fiberMonicBasisChange, hdegree, ((e k).symm i).property,
    ((e k).symm j).property]

/-- The block-diagonal coefficient change attached to monic, correctly
graded polynomials is unimodular. -/
theorem det_fiberMonicBasisChange_eq_one
    {N : ℕ} {o R : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    [CommRing R] (b : Fin N → o) (s : o → ℕ)
    (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (P : Fin N → Polynomial R)
    (hdeg : ∀ j, (P j).natDegree = degree j)
    (hmonic : ∀ j, (P j).Monic) :
    (fiberMonicBasisChange b degree P).det = 1 := by
  classical
  rw [(fiberMonicBasisChange_blockTriangular b degree P).det_fintype]
  apply Finset.prod_eq_one
  intro k _
  let Pk : Fin (s k) → Polynomial R := fun j ↦ P ((e k).symm j).1
  have hPkdeg : ∀ j, (Pk j).natDegree = (j : ℕ) := by
    intro j
    rw [hdeg, hdegree]
  have hPkmonic : ∀ j, (Pk j).Monic := by
    intro j
    exact hmonic _
  calc
    ((fiberMonicBasisChange b degree P).toSquareBlock b k).det =
        (Matrix.reindex (e k) (e k)
          ((fiberMonicBasisChange b degree P).toSquareBlock b k)).det :=
      (Matrix.det_reindex_self (e k) _).symm
    _ = (Matrix.of fun i j : Fin (s k) ↦ (Pk j).coeff (i : ℕ)).det := by
      rw [reindex_toSquareBlock_fiberMonicBasisChange b s e degree hdegree]
    _ = 1 := Matrix.det_matrixOfPolynomials Pk hPkdeg hPkmonic

theorem sum_ite_fiber_eq_sum_reindex
    {N : ℕ} {o R : Type*} [Fintype o] [DecidableEq o] [AddCommMonoid R]
    (b : Fin N → o) (s : o → ℕ)
    (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (k : o) (f : Fin N → R) :
    (∑ i : Fin N, if b i = k then f i else 0) =
      ∑ j : Fin (s k), f ((e k).symm j).1 := by
  classical
  calc
    (∑ i : Fin N, if b i = k then f i else 0) =
        ∑ i ∈ (Finset.univ.filter fun i : Fin N ↦ b i = k), f i := by
      rw [Finset.sum_filter]
    _ = ∑ i : {i : Fin N // b i = k}, f i.1 := by
      apply Finset.sum_subtype
      intro i
      simp
    _ = ∑ j : Fin (s k), f ((e k).symm j).1 := by
      simpa using (Equiv.sum_comp (e k).symm (fun i ↦ f i.1)).symm

/-- The same determinant-one column change works in the presence of a
block-dependent row scale, because the change never mixes column fibers. -/
theorem fiberScaledConsecutivePowerMatrix_mul_fiberMonicBasisChange
    {N : ℕ} {o R : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    [CommRing R] (b : Fin N → o) (s : o → ℕ)
    (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (scale x : o → Fin N → R) (P : Fin N → Polynomial R)
    (hdeg : ∀ j, (P j).natDegree = degree j) :
    fiberScaledConsecutivePowerMatrix b degree scale x *
        fiberMonicBasisChange b degree P =
      Matrix.of fun row col ↦
        scale (b col) row * (P col).eval (x (b col) row) := by
  classical
  ext row col
  rw [Matrix.mul_apply, Matrix.of_apply]
  have hcolDegree : degree col < s (b col) := by
    let j : Fin (s (b col)) := e (b col) ⟨col, rfl⟩
    calc
      degree col = degree ((e (b col)).symm j).1 := by simp [j]
      _ = (j : ℕ) := hdegree (b col) j
      _ < s (b col) := j.isLt
  have hPdeg : (P col).natDegree < s (b col) := by
    rw [hdeg]
    exact hcolDegree
  calc
    (∑ d : Fin N,
        fiberScaledConsecutivePowerMatrix b degree scale x row d *
          fiberMonicBasisChange b degree P d col) =
      ∑ d : Fin N, if b d = b col then
        scale (b col) row * x (b col) row ^ degree d *
          (P col).coeff (degree d) else 0 := by
        apply Finset.sum_congr rfl
        intro d _
        by_cases hd : b d = b col
        · simp [fiberScaledConsecutivePowerMatrix, fiberMonicBasisChange, hd]
        · simp [fiberScaledConsecutivePowerMatrix, fiberMonicBasisChange, hd]
    _ = ∑ j : Fin (s (b col)),
        scale (b col) row *
          x (b col) row ^ degree ((e (b col)).symm j).1 *
          (P col).coeff (degree ((e (b col)).symm j).1) := by
      exact sum_ite_fiber_eq_sum_reindex b s e (b col)
        (fun d ↦ scale (b col) row * x (b col) row ^ degree d *
          (P col).coeff (degree d))
    _ = ∑ j : Fin (s (b col)),
        scale (b col) row * x (b col) row ^ (j : ℕ) *
          (P col).coeff (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hdegree]
    _ = scale (b col) row * (P col).eval (x (b col) row) := by
      rw [Polynomial.eval_eq_sum_range' hPdeg]
      rw [← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem sum_degreeWeight_eq_rowBlockOrderingExponent
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o]
    (b : Fin N → o) (s : o → ℕ)
    (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (w : ℕ → ℕ) :
    (∑ col : Fin N, w (degree col)) = rowBlockOrderingExponent s w := by
  classical
  rw [rowBlockOrderingExponent, ← Fintype.sum_fiberwise b (fun col ↦ w (degree col))]
  apply Finset.sum_congr rfl
  intro k _
  simpa [hdegree] using
    (Equiv.sum_comp (e k).symm
      (fun col : {i : Fin N // b i = k} ↦ w (degree col.1))).symm

/-- Direct whole-matrix fixed divisor with the block-dependent row scales
present in the mixed Alaoglu--Erdős determinant. -/
theorem pow_sum_dvd_det_fiberScaledConsecutivePowerMatrix_of_monicBasis
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (b : Fin N → o) (s : o → ℕ)
    (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (scale x : o → Fin N → ℤ) (P : Fin N → Polynomial ℤ)
    (hdeg : ∀ j, (P j).natDegree = degree j)
    (hmonic : ∀ j, (P j).Monic) (p : ℤ) (w : Fin N → ℕ)
    (hdiv : ∀ row col,
      p ^ w col ∣ scale (b col) row * (P col).eval (x (b col) row)) :
    p ^ (∑ col : Fin N, w col) ∣
      (fiberScaledConsecutivePowerMatrix b degree scale x).det := by
  let A := fiberScaledConsecutivePowerMatrix b degree scale x
  let U := fiberMonicBasisChange b degree P
  apply pow_sum_columnWeight_dvd_det_of_unimodular_mul A U p w
  · exact det_fiberMonicBasisChange_eq_one b s e degree hdegree P hdeg hmonic
  · intro row col
    rw [show A * U = Matrix.of (fun row col ↦
      scale (b col) row * (P col).eval (x (b col) row)) by
        exact fiberScaledConsecutivePowerMatrix_mul_fiberMonicBasisChange
          b s e degree hdegree scale x P hdeg]
    simpa using hdiv row col

/-- Dyadic p-ordering divisor for the full scaled mixed matrix. -/
theorem two_pow_rowBlockOrderingExponent_dvd_det_fiberScaledConsecutivePowers
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (b : Fin N → o) (s : o → ℕ)
    (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (scale : o → Fin N → ℤ) (z : o → Fin N → ℕ) :
    (2 : ℤ) ^ rowBlockOrderingExponent s twoUnitOrderingWeight ∣
      (fiberScaledConsecutivePowerMatrix b degree scale
        (fun k i ↦ 2 * (z k i : ℤ) + 1)).det := by
  rw [← sum_degreeWeight_eq_rowBlockOrderingExponent
    b s e degree hdegree twoUnitOrderingWeight]
  apply pow_sum_dvd_det_fiberScaledConsecutivePowerMatrix_of_monicBasis
    b s e degree hdegree scale
    (fun k i ↦ 2 * (z k i : ℤ) + 1)
    (fun col ↦ twoUnitOrderingPolynomial (degree col))
    (fun col ↦ twoUnitOrderingPolynomial_natDegree _)
    (fun col ↦ twoUnitOrderingPolynomial_monic _)
    2 (fun col ↦ twoUnitOrderingWeight (degree col))
  intro row col
  exact (twoUnitOrderingPolynomial_fixedDivisor
    (degree col) (z (b col) row)).mul_left _

/-- Triadic p-ordering divisor for the full scaled mixed matrix. -/
theorem three_pow_rowBlockOrderingExponent_dvd_det_fiberScaledConsecutivePowers
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    (b : Fin N → o) (s : o → ℕ)
    (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (scale : o → Fin N → ℤ)
    (z : o → Fin N → ℕ) (residue : o → Fin N → Fin 2) :
    (3 : ℤ) ^ rowBlockOrderingExponent s threeUnitOrderingWeight ∣
      (fiberScaledConsecutivePowerMatrix b degree scale
        (fun k i ↦ 3 * (z k i : ℤ) + ((residue k i : ℕ) : ℤ) + 1)).det := by
  rw [← sum_degreeWeight_eq_rowBlockOrderingExponent
    b s e degree hdegree threeUnitOrderingWeight]
  apply pow_sum_dvd_det_fiberScaledConsecutivePowerMatrix_of_monicBasis
    b s e degree hdegree scale
    (fun k i ↦ 3 * (z k i : ℤ) + ((residue k i : ℕ) : ℤ) + 1)
    (fun col ↦ threeUnitOrderingPolynomial (degree col))
    (fun col ↦ threeUnitOrderingPolynomial_natDegree _)
    (fun col ↦ threeUnitOrderingPolynomial_monic _)
    3 (fun col ↦ threeUnitOrderingWeight (degree col))
  intro row col
  exact (threeUnitOrderingPolynomial_fixedDivisor
    (degree col) (z (b col) row) (residue (b col) row)).mul_left _

/-! ## Additive gain beyond the tropical minimum -/

/-- For dyadic positive-unit nodes, the block-size p-ordering exponent is a
common divisor of every row-assignment coefficient, so it adds to the exact
rank-one tropical minimum in the full determinant. -/
theorem two_pow_minCost_add_rowBlockOrderingExponent_dvd_det_rankOnePowerMatrix
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {depth : Fin N → ℕ} (b : Fin N → o) {value : o → ℕ}
    (s : o → ℕ) (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (scale : o → Fin N → ℤ) (z : o → Fin N → ℕ)
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : Monotone value) :
    (2 : ℤ) ^
        (rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) +
          rowBlockOrderingExponent s twoUnitOrderingWeight) ∣
      (rankOnePowerMatrix 2 depth b value
        (fiberScaledConsecutivePowerMatrix b degree scale
          (fun k i ↦ 2 * (z k i : ℤ) + 1))).det := by
  apply pow_minCost_add_commonMinorExponent_dvd_det_rankOnePowerMatrix
    2 (fiberScaledConsecutivePowerMatrix b degree scale
      (fun k i ↦ 2 * (z k i : ℤ) + 1))
    hdepth hb hvalue (rowBlockOrderingExponent s twoUnitOrderingWeight)
  intro a
  exact two_pow_rowBlockOrderingExponent_dvd_minorProduct_fiberScaledConsecutivePowers
    b s e degree hdegree scale z a

/-- The symmetric additive theorem for triadic positive-unit nodes. -/
theorem three_pow_minCost_add_rowBlockOrderingExponent_dvd_det_rankOnePowerMatrix
    {N : ℕ} {o : Type*} [Fintype o] [DecidableEq o] [LinearOrder o]
    {depth : Fin N → ℕ} (b : Fin N → o) {value : o → ℕ}
    (s : o → ℕ) (e : ∀ k : o, {i : Fin N // b i = k} ≃ Fin (s k))
    (degree : Fin N → ℕ)
    (hdegree : ∀ (k : o) (j : Fin (s k)), degree ((e k).symm j).1 = (j : ℕ))
    (scale : o → Fin N → ℤ)
    (z : o → Fin N → ℕ) (residue : o → Fin N → Fin 2)
    (hdepth : StrictAnti depth) (hb : Monotone b) (hvalue : Monotone value) :
    (3 : ℤ) ^
        (rankOneAssignmentCost depth (value ∘ b) (Equiv.refl _) +
          rowBlockOrderingExponent s threeUnitOrderingWeight) ∣
      (rankOnePowerMatrix 3 depth b value
        (fiberScaledConsecutivePowerMatrix b degree scale
          (fun k i ↦ 3 * (z k i : ℤ) + ((residue k i : ℕ) : ℤ) + 1))).det := by
  apply pow_minCost_add_commonMinorExponent_dvd_det_rankOnePowerMatrix
    3 (fiberScaledConsecutivePowerMatrix b degree scale
      (fun k i ↦ 3 * (z k i : ℤ) + ((residue k i : ℕ) : ℤ) + 1))
    hdepth hb hvalue (rowBlockOrderingExponent s threeUnitOrderingWeight)
  intro a
  exact three_pow_rowBlockOrderingExponent_dvd_minorProduct_fiberScaledConsecutivePowers
    b s e degree hdegree scale z residue a

end LeanProofs.TwoBaseIntegerExponent
