import IPRADerivations.Core.LinearAlgebra

/-!
# Euler–Rodrigues rotations (`docs/proofs/geometry/euler_rodrigues_ipra`)

For an integer scalar `a` and an integer vector `v`, the Euler–Rodrigues matrix
`R = (a² − v·v) I + 2 v vᵀ + 2a [v]×` (`euler_rodrigues_ipra.tex`) satisfies, as
identities over the integers,

* `Rᵀ R = (a² + v·v)² I`, so `R` is a rotation (scaled) and, when
  `a² + v·v = 1`, orthogonal;
* `det R = (a² + v·v)³`;
* `R v = (a² + v·v) v`: the axis `v` is fixed.

For `3 × 3` integer matrices `B`, the shift identities behind the packet's
Cayley-transform argument are also derived:
`adj (I − B) = (1 − tr B) I + B + adj B`,
`det (I − B) = 1 − tr B + tr (adj B) − det B` and `adj (adj B) = (det B) B`.
-/

namespace LeanProofs.IPRA.Geometry.EulerRodrigues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn Matrix
open scoped Fm

/-! ## The Euler–Rodrigues matrix -/

section Rodrigues

variable {m : ℕ}

/-- The cross-product matrix `[v]×`, with `[v]× w = v × w`. -/
def crossMat (v : Vec 3 m) : Mat 3 m :=
  ![![ZT.natLit 0, -v 2, v 1], ![v 2, ZT.natLit 0, -v 0], ![-v 1, v 0, ZT.natLit 0]]

/-- `v vᵀ`. -/
def outer (v w : Vec 3 m) : Mat 3 m := fun i j => v i * w j

/-- `R = (a² − v·v) I + 2 v vᵀ + 2a [v]×`. -/
def rodrigues (a : ZT m) (v : Vec 3 m) : Mat 3 m :=
  Mat.add (Mat.add (Mat.smul (a * a - Vec.dot v v) Mat.one)
    (Mat.smul (ZT.natLit 2) (outer v v))) (Mat.smul (ZT.natLit 2 * a) (crossMat v))

/-- `a² + v·v`. -/
def quatNorm (a : ZT m) (v : Vec 3 m) : ZT m := a * a + Vec.dot v v

end Rodrigues

abbrev a : ZT 8 := .var2 0 1
abbrev v : Vec 3 8 := Vec.vars 3 2 (by norm_num)

/-- `Rᵀ R = (a² + v·v)² I`. -/
def orthogonalFormula : Fm PTm 8 :=
  Mat.eqFm (Mat.mul (Mat.transpose (rodrigues a v)) (rodrigues a v))
    (Mat.smul (quatNorm a v * quatNorm a v) Mat.one)

theorem rodrigues_orthogonal : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8 orthogonalFormula := by
  refine closeUniv 8 (Mat.derive ?_)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [orthogonalFormula, rodrigues, quatNorm, crossMat, outer, Mat.mul, Mat.add, Mat.smul,
      Mat.one, Mat.transpose, Vec.dot, Vec.vars, ZT.sumFin] <;> ring

/-- `det R = (a² + v·v)³`. -/
def detFormula : Fm PTm 8 :=
  ZT.eq (Mat.det (rodrigues a v)) (quatNorm a v * quatNorm a v * quatNorm a v)

theorem rodrigues_det : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8 detFormula := by
  refine closeUniv 8 (ZT.derive ?_)
  rw [Mat.toZ_det, Matrix.det_fin_three]
  simp [rodrigues, quatNorm, crossMat, outer, Mat.add, Mat.smul, Mat.one, Vec.dot, Vec.vars,
    ZT.sumFin]
  ring

/-- `R v = (a² + v·v) v`. -/
def axisFormula : Fm PTm 8 :=
  Vec.eqFm (Mat.mulVec (rodrigues a v) v) (Vec.smul (quatNorm a v) v)

theorem rodrigues_axis : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8 axisFormula := by
  refine closeUniv 8 (Vec.derive ?_)
  funext i
  fin_cases i <;>
    simp [rodrigues, quatNorm, crossMat, outer, Mat.mulVec, Mat.add, Mat.smul, Mat.one, Vec.dot,
      Vec.smul, Vec.vars, ZT.sumFin, Vec.toZ] <;> ring

/-! ## Shift identities for `3 × 3` matrices -/

section Shift

abbrev B : Mat 3 18 := fun i j => ZT.var2 ⟨2 * (3 * i + j), by omega⟩ ⟨2 * (3 * i + j) + 1, by omega⟩

private theorem adj_shift {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    (1 - M).adjugate = (1 - M.trace) • (1 : Matrix (Fin 3) (Fin 3) R) + M + M.adjugate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.trace_fin_three, Matrix.one_apply] <;> ring

private theorem det_shift {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    (1 - M).det = 1 - M.trace + M.adjugate.trace - M.det := by
  simp [Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.trace_fin_three, Matrix.one_apply]
  ring

private theorem adj_adj {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M.adjugate.adjugate = M.det • M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.det_fin_three] <;> ring

/-- `adj (I − B) = (1 − tr B) I + B + adj B`. -/
def adjShiftFormula : Fm PTm 18 :=
  Mat.eqFm (Mat.adj (Mat.sub Mat.one B))
    (Mat.add (Mat.add (Mat.smul (ZT.natLit 1 - Mat.trace B) Mat.one) B) (Mat.adj B))

theorem adjugate_shift : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 adjShiftFormula :=
  closeUniv 18 (Mat.derive (by simpa using adj_shift _))

/-- `det (I − B) = 1 − tr B + tr (adj B) − det B`. -/
def detShiftFormula : Fm PTm 18 :=
  ZT.eq (Mat.det (Mat.sub Mat.one B))
    (ZT.natLit 1 - Mat.trace B + Mat.trace (Mat.adj B) - Mat.det B)

theorem det_shift_formula : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 detShiftFormula :=
  closeUniv 18 (ZT.derive (by simpa using det_shift _))

/-- `adj (adj B) = (det B) B`. -/
def adjAdjFormula : Fm PTm 18 := Mat.eqFm (Mat.adj (Mat.adj B)) (Mat.smul (Mat.det B) B)

theorem adjugate_adjugate : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 adjAdjFormula :=
  closeUniv 18 (Mat.derive (by simpa using adj_adj _))

end Shift

end LeanProofs.IPRA.Geometry.EulerRodrigues
