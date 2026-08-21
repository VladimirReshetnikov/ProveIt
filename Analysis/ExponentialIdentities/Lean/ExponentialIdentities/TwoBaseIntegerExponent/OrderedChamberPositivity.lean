import ExponentialIdentities.TwoBaseIntegerExponent.ExponentialPolynomialZeros
import ExponentialIdentities.TwoBaseIntegerExponent.SemigroupDeterminant
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue

/-!
# Positivity of the generalized Vandermonde determinant in the ordered chamber

`ExponentialPolynomialZeros` proves that the generalized Vandermonde determinant
`det (x i ^ λ j)` is *nonzero* whenever the nodes `x 0 < ⋯ < x r` are positive and strictly
increasing and the real exponents `λ 0 < ⋯ < λ r` are strictly increasing.  This module
supplies the missing sign: the determinant is strictly *positive* on that ordered chamber.
This is the report's lemma "Generalized Vandermonde positivity", whose paper proof is the
appendix "Detailed proof of the generalized Vandermonde sign".

## Proof

The report offers two routes: the Karlin–Studden characterization of extended complete
Chebyshev systems through initial Wronskians, and an elementary argument combining
connectedness of the chamber with a coalescing-node limit.  The formalization follows a
third route which uses the same two ingredients — nonvanishing on a connected set plus one
explicit positive point — but deforms the *exponents* instead of the nodes, so that no
coalescing limit and no Wronskian bookkeeping are needed:

* `exponentPath lam t j = (1 - t) * j + t * lam j` is the straight-line homotopy from the
  classical exponents `0, 1, …, r` to the given exponents `lam j`.  It is strictly increasing
  in `j` for every `t ∈ [0, 1]` (`strictMono_exponentPath`): both summands are monotone in
  `j`, and at least one of the weights `1 - t`, `t` is strictly positive.
* At `t = 0` the matrix is the classical Vandermonde matrix (`pathVandermonde_zero`), whose
  determinant is the product of the positive differences `x j - x i` (`det_vandermonde_pos`).
* At `t = 1` it is the given generalized Vandermonde matrix (`pathVandermonde_one`).
* `t ↦ det` is continuous (`continuous_det_pathVandermonde`): each entry is
  `exp (log (x i) * exponentPath lam t j)` because `x i > 0`, and the determinant is a
  polynomial in the entries (`Continuous.matrix_det`).
* By `det_rpowVandermonde_ne_zero` the determinant never vanishes along the path.  A negative
  value at `t = 1` would place `0` between the endpoint values, so the intermediate value
  theorem (`intermediate_value_Icc'`) would produce a zero of the determinant inside `[0, 1]`,
  a contradiction.  Hence the determinant is positive at `t = 1`.

Unlike the statement in the report, no nonnegativity of the exponents is required here:
`Real.rpow` of a positive base is defined and continuous for every real exponent, and the
homotopy argument never leaves the positive-node chamber.

## Consequences

The positivity hypothesis that `SemigroupDeterminant.one_le_det_semigroupMatrix` had to
assume is discharged (`det_semigroupMatrix_pos`), which turns the report's semigroup integer
determinant theorem into the unconditional lower bound `D_λ(m) ≥ 1`
(`one_le_det_semigroupMatrix_of_strictMono`).
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set

noncomputable section

/-! ### The classical Vandermonde determinant in the ordered chamber -/

/-- **Positivity of the classical Vandermonde determinant.**  For strictly increasing real
nodes the determinant of `x i ^ j` is the product of the strictly positive differences
`x j - x i` over `i < j`, hence strictly positive.  No positivity of the nodes is needed at
this stage; it enters only when the natural-number exponents are deformed to real ones. -/
theorem det_vandermonde_pos {m : ℕ} (x : Fin m → ℝ) (hx : StrictMono x) :
    0 < (Matrix.vandermonde x).det := by
  rw [Matrix.det_vandermonde]
  refine Finset.prod_pos fun i _ ↦ Finset.prod_pos fun j hj ↦ ?_
  exact sub_pos.mpr (hx (Finset.mem_Ioi.mp hj))

/-! ### The straight-line homotopy of exponents -/

/-- The straight-line homotopy from the classical exponents `0, 1, …, r` (at `t = 0`) to the
prescribed real exponents `lam` (at `t = 1`). -/
def exponentPath {m : ℕ} (lam : Fin m → ℝ) (t : ℝ) (j : Fin m) : ℝ :=
  (1 - t) * ((j : ℕ) : ℝ) + t * lam j

/-- Unfolding lemma for `exponentPath`. -/
theorem exponentPath_apply {m : ℕ} (lam : Fin m → ℝ) (t : ℝ) (j : Fin m) :
    exponentPath lam t j = (1 - t) * ((j : ℕ) : ℝ) + t * lam j := rfl

/-- At `t = 0` the homotopy is the classical exponent family `j ↦ j`. -/
@[simp] theorem exponentPath_zero {m : ℕ} (lam : Fin m → ℝ) (j : Fin m) :
    exponentPath lam 0 j = ((j : ℕ) : ℝ) := by
  rw [exponentPath_apply, sub_zero, one_mul, zero_mul, add_zero]

/-- At `t = 1` the homotopy is the prescribed exponent family `lam`. -/
@[simp] theorem exponentPath_one {m : ℕ} (lam : Fin m → ℝ) (j : Fin m) :
    exponentPath lam 1 j = lam j := by
  rw [exponentPath_apply, sub_self, zero_mul, zero_add, one_mul]

/-- **The homotopy stays in the ordered exponent chamber.**  For every `t ∈ [0, 1]` the
exponents `exponentPath lam t` are again strictly increasing.  This is pure algebra: the
`j`-part contributes `(1 - t) * (j' - j) ≥ 0`, the `lam`-part contributes
`t * (lam j' - lam j) ≥ 0`, and at least one of the weights `1 - t` and `t` is positive. -/
theorem strictMono_exponentPath {m : ℕ} {lam : Fin m → ℝ} (hlam : StrictMono lam)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : StrictMono (exponentPath lam t) := by
  intro a b hab
  simp only [exponentPath_apply]
  have hval : (a : ℕ) < (b : ℕ) := Fin.lt_def.mp hab
  have hnat : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hval
  have hl : lam a < lam b := hlam hab
  have h1 : (0 : ℝ) ≤ 1 - t := by linarith
  have hA : (1 - t) * ((a : ℕ) : ℝ) ≤ (1 - t) * ((b : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hnat.le h1
  have hB : t * lam a ≤ t * lam b := mul_le_mul_of_nonneg_left hl.le ht0
  rcases eq_or_lt_of_le ht0 with ht | ht
  · have hstrict : (1 - t) * ((a : ℕ) : ℝ) < (1 - t) * ((b : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_left hnat (by linarith)
    linarith
  · have hstrict : t * lam a < t * lam b := mul_lt_mul_of_pos_left hl ht
    linarith

/-! ### The determinant along the homotopy -/

/-- The generalized Vandermonde matrix carried along the exponent homotopy: at `t = 0` it is
the classical Vandermonde matrix of the nodes, at `t = 1` the prescribed generalized
Vandermonde matrix. -/
def pathVandermonde {m : ℕ} (x lam : Fin m → ℝ) (t : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  rpowVandermonde x (exponentPath lam t)

/-- Unfolding lemma for `pathVandermonde`. -/
@[simp] theorem pathVandermonde_apply {m : ℕ} (x lam : Fin m → ℝ) (t : ℝ) (i j : Fin m) :
    pathVandermonde x lam t i j = x i ^ exponentPath lam t j := rfl

/-- The homotopy starts at the classical Vandermonde matrix. -/
theorem pathVandermonde_zero {m : ℕ} (x lam : Fin m → ℝ) :
    pathVandermonde x lam 0 = Matrix.vandermonde x := by
  ext i j
  rw [pathVandermonde_apply, exponentPath_zero, Real.rpow_natCast, Matrix.vandermonde_apply]

/-- The homotopy ends at the prescribed generalized Vandermonde matrix. -/
theorem pathVandermonde_one {m : ℕ} (x lam : Fin m → ℝ) :
    pathVandermonde x lam 1 = rpowVandermonde x lam := by
  ext i j
  rw [pathVandermonde_apply, exponentPath_one, rpowVandermonde_apply]

/-- **Continuity of the determinant along the homotopy.**  Each entry of
`pathVandermonde x lam t` equals `exp (log (x i) * exponentPath lam t j)` because the node
`x i` is positive, and that is a continuous function of `t`; the determinant is a polynomial
in the entries. -/
theorem continuous_det_pathVandermonde {m : ℕ} (x lam : Fin m → ℝ) (hx : ∀ i, 0 < x i) :
    Continuous fun t : ℝ ↦ (pathVandermonde x lam t).det := by
  refine Continuous.matrix_det (continuous_matrix fun i j ↦ ?_)
  show Continuous fun t : ℝ ↦ pathVandermonde x lam t i j
  have hlin : Continuous fun t : ℝ ↦
      Real.log (x i) * ((1 - t) * ((j : ℕ) : ℝ) + t * lam j) :=
    continuous_const.mul
      (((continuous_const.sub continuous_id').mul continuous_const).add
        (continuous_id'.mul continuous_const))
  have hfun : (fun t : ℝ ↦ pathVandermonde x lam t i j)
      = fun t : ℝ ↦ Real.exp (Real.log (x i) * ((1 - t) * ((j : ℕ) : ℝ) + t * lam j)) := by
    funext t
    rw [pathVandermonde_apply, exponentPath_apply, Real.rpow_def_of_pos (hx i)]
  rw [hfun]
  exact Real.continuous_exp.comp' hlin

/-! ### The positivity theorem -/

/-- **Generalized Vandermonde positivity in the ordered chamber.**  For strictly increasing
positive nodes `x 0 < ⋯ < x r` and strictly increasing real exponents `lam 0 < ⋯ < lam r`,
`det (x i ^ lam j) > 0`.

This is the report's lemma `sg:lem-generalized-vandermonde`, and it strengthens
`det_rpowVandermonde_ne_zero` from nonvanishing to a sign.  The proof deforms the exponents
along `exponentPath`: the determinant is continuous in the deformation parameter, is
nonvanishing throughout because `strictMono_exponentPath` keeps the exponents ordered, and is
positive at the classical Vandermonde endpoint.  A negative value at the other endpoint would
force a zero in between by the intermediate value theorem.

The exponents are not assumed nonnegative; only the nodes must be positive. -/
theorem det_rpowVandermonde_pos {n : ℕ} (x lam : Fin (n + 1) → ℝ)
    (hx : StrictMono x) (hx0 : 0 < x 0) (hlam : StrictMono lam) :
    0 < (rpowVandermonde x lam).det := by
  have hxpos : ∀ i, 0 < x i := fun i ↦ hx0.trans_le (hx.monotone (Fin.zero_le i))
  have hcont : Continuous fun t : ℝ ↦ (pathVandermonde x lam t).det :=
    continuous_det_pathVandermonde x lam hxpos
  have hpos0 : 0 < (pathVandermonde x lam 0).det := by
    rw [pathVandermonde_zero]
    exact det_vandermonde_pos x hx
  have hne : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (pathVandermonde x lam t).det ≠ 0 := fun t ht0 ht1 ↦
    det_rpowVandermonde_ne_zero x (exponentPath lam t) hx hx0
      (strictMono_exponentPath hlam ht0 ht1)
  rw [← pathVandermonde_one x lam]
  rcases lt_trichotomy ((pathVandermonde x lam 1).det) 0 with hlt | heq | hgt
  · exfalso
    have hmem : (0 : ℝ) ∈
        Icc ((pathVandermonde x lam 1).det) ((pathVandermonde x lam 0).det) := ⟨hlt.le, hpos0.le⟩
    obtain ⟨t, ht, hteq⟩ :=
      intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont.continuousOn hmem
    exact hne t ht.1 ht.2 hteq
  · exact absurd heq (hne 1 zero_le_one le_rfl)
  · exact hgt

/-- **Generalized Vandermonde positivity, uniform in the size.**  The `Fin m` form of
`det_rpowVandermonde_pos`, valid for every `m` including `m = 0`, where the determinant of the
empty matrix is `1`. -/
theorem det_rpowVandermonde_pos_of_forall {m : ℕ} (x lam : Fin m → ℝ)
    (hx : StrictMono x) (hxpos : ∀ i, 0 < x i) (hlam : StrictMono lam) :
    0 < (rpowVandermonde x lam).det := by
  cases m with
  | zero =>
      rw [Matrix.det_fin_zero]
      exact zero_lt_one
  | succ n => exact det_rpowVandermonde_pos x lam hx (hxpos 0) hlam

/-! ### The semigroup determinant of the report -/

/-- **Positivity of the semigroup generalized Vandermonde determinant.**  For strictly
increasing positive natural nodes and strictly increasing mixed exponents
`λ_j = a_j + b_j * (log 3 / log 2)`, the determinant `det (m i ^ λ_j)` is strictly positive.
This discharges the positivity hypothesis of
`SemigroupDeterminant.one_le_det_semigroupMatrix`. -/
theorem det_semigroupMatrix_pos (r : ℕ) (m : Fin (r + 1) → ℕ) (ab : Fin (r + 1) → ℕ × ℕ)
    (hm : StrictMono m) (hm0 : 0 < m 0)
    (hlam : StrictMono fun j ↦ mixedExponent (ab j)) :
    0 < (semigroupMatrix r m ab).det := by
  have hmat : semigroupMatrix r m ab
      = rpowVandermonde (fun i ↦ ((m i : ℕ) : ℝ)) (fun j ↦ mixedExponent (ab j)) := rfl
  rw [hmat]
  refine det_rpowVandermonde_pos _ _ ?_ ?_ hlam
  · intro a b hab
    show ((m a : ℕ) : ℝ) < ((m b : ℕ) : ℝ)
    exact_mod_cast hm hab
  · show (0 : ℝ) < ((m 0 : ℕ) : ℝ)
    exact_mod_cast hm0

/-- **The report's semigroup integer determinant theorem, unconditionally.**  For strictly
increasing natural candidates `m 0 < ⋯ < m r` and strictly increasing mixed exponents, the
semigroup generalized Vandermonde determinant is a positive rational integer, hence at least
`1`.  The integrality half is `SemigroupDeterminant.one_le_det_semigroupMatrix`; the
positivity half is `det_semigroupMatrix_pos`. -/
theorem one_le_det_semigroupMatrix_of_strictMono (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hm : ∀ i, TwoBaseNaturalCandidate (m i)) (ab : Fin (r + 1) → ℕ × ℕ)
    (hmono : StrictMono m) (hlam : StrictMono fun j ↦ mixedExponent (ab j)) :
    1 ≤ (semigroupMatrix r m ab).det :=
  one_le_det_semigroupMatrix r m hm ab (det_semigroupMatrix_pos r m ab hmono (hm 0).1 hlam)

/-- **The report's semigroup integer determinant theorem, packaged.**  Under the same
hypotheses the determinant is the real image of a positive rational integer. -/
theorem exists_pos_int_det_semigroupMatrix_of_strictMono (r : ℕ) (m : Fin (r + 1) → ℕ)
    (hm : ∀ i, TwoBaseNaturalCandidate (m i)) (ab : Fin (r + 1) → ℕ × ℕ)
    (hmono : StrictMono m) (hlam : StrictMono fun j ↦ mixedExponent (ab j)) :
    ∃ z : ℤ, 0 < z ∧ (z : ℝ) = (semigroupMatrix r m ab).det :=
  exists_pos_int_det_semigroupMatrix r m hm ab
    (det_semigroupMatrix_pos r m ab hmono (hm 0).1 hlam)

end

end LeanProofs.TwoBaseIntegerExponent
