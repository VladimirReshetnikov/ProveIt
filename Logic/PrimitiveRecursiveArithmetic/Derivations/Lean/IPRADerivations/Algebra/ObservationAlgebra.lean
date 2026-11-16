import IPRADerivations.Algebra.CayleyHamilton

/-!
# Observation algebra: Newton identities and companion matrices

Packet: `algebra/ipra_observation_algebra_2026-11-16` (the theorems "Observation and resultant",
"Newton identities without denominators" and "Continuous unlabeled polynomial observation").
The observation polynomial of an output `g` for a monic `f` is the characteristic polynomial
`det(T I − g(M_y))`, where `M_y` is the companion matrix of `f`. For integer matrices:

* `newton2`: for a `2 × 2` matrix `B`, `p₂ − e₁ p₁ + 2 e₂ = 0`, with `p_k = tr(B^k)`,
  `e₁ = tr B`, `e₂ = det B`;
* `newton3a`, `newton3b`: for a `3 × 3` matrix, `p₂ − e₁ p₁ + 2 e₂ = 0` and
  `p₃ − e₁ p₂ + e₂ p₁ − 3 e₃ = 0`, with `e₂ = tr(adj B)` (the sum of the principal `2 × 2`
  minors) and `e₃ = det B`;
* `companion2`, `companion3`: the companion matrix of a monic quadratic or cubic has that
  polynomial as its characteristic polynomial, i.e. the observation of `Y` is `f(T)`;
* `quad_observation`, `quad_observation_sq`: for `M_y = [[0, t² + a], [1, 0]]`,
  `det(T I − M_y) = T² − (t² + a)` and `det(U I − M_y²) = (U − (t² + a))²`.

Subtracted terms are moved across the equation where that keeps the statement free of negative
literals. The general degree and the guarded specialization theorem are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.ObservationAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Algebra.CayleyHamilton (matVar)
open Syn Matrix
open scoped Fm

/-! ## Newton identities -/

private theorem nw2 {R : Type*} [CommRing R] (B : Matrix (Fin 2) (Fin 2) R) :
    (B * B).trace + 2 * B.det = B.trace * B.trace := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, Matrix.trace_fin_two]; ring

/-- `tr(B²) + 2 det B = (tr B)²` for `2 × 2` integer matrices. -/
def newton2Formula : Fm PTm (2 * (2 * 2)) :=
  let B := matVar 2
  ZT.eq (Mat.trace (Mat.mul B B) + ZT.natLit 2 * Mat.det B) (Mat.trace B * Mat.trace B)

theorem newton2 : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ _ newton2Formula :=
  closeUniv _ (ZT.derive (by simpa [newton2Formula] using nw2 _))

private theorem nw3a {R : Type*} [CommRing R] (B : Matrix (Fin 3) (Fin 3) R) :
    (B * B).trace + 2 * B.adjugate.trace = B.trace * B.trace := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace_fin_three, Matrix.adjugate_fin_three]; ring

private theorem nw3b {R : Type*} [CommRing R] (B : Matrix (Fin 3) (Fin 3) R) :
    (B * B * B).trace + B.adjugate.trace * B.trace = B.trace * (B * B).trace + 3 * B.det := by
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.det_fin_three, Matrix.trace_fin_three,
    Matrix.adjugate_fin_three]; ring

/-- `tr(B²) + 2 tr(adj B) = (tr B)²` for `3 × 3` integer matrices. -/
def newton3aFormula : Fm PTm (2 * (3 * 3)) :=
  let B := matVar 3
  ZT.eq (Mat.trace (Mat.mul B B) + ZT.natLit 2 * Mat.trace (Mat.adj B)) (Mat.trace B * Mat.trace B)

/-- `tr(B³) + tr(adj B) tr B = tr B · tr(B²) + 3 det B` for `3 × 3` integer matrices. -/
def newton3bFormula : Fm PTm (2 * (3 * 3)) :=
  let B := matVar 3
  ZT.eq (Mat.trace (Mat.mul (Mat.mul B B) B) + Mat.trace (Mat.adj B) * Mat.trace B)
    (Mat.trace B * Mat.trace (Mat.mul B B) + ZT.natLit 3 * Mat.det B)

theorem newton3a : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ _ newton3aFormula :=
  closeUniv _ (ZT.derive (by simpa [newton3aFormula] using nw3a _))

theorem newton3b : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ _ newton3bFormula :=
  closeUniv _ (ZT.derive (by simpa [newton3bFormula] using nw3b _))

/-! ## Companion matrices -/

section Companion

abbrev c₀ : ZT 8 := .var2 0 1
abbrev c₁ : ZT 8 := .var2 2 3
abbrev c₂ : ZT 8 := .var2 4 5
abbrev T : ZT 8 := .var2 6 7

/-- `T I − C_f` for `f = Y² + c₁ Y + c₀`. -/
def char2 : Mat 2 8 := ![![T, c₀], ![-(ZT.natLit 1), T + c₁]]

/-- `T I − C_f` for `f = Y³ + c₂ Y² + c₁ Y + c₀`. -/
def char3 : Mat 3 8 :=
  ![![T, ZT.natLit 0, c₀], ![-(ZT.natLit 1), T, c₁], ![ZT.natLit 0, -(ZT.natLit 1), T + c₂]]

def companion2Formula : Fm PTm 8 := ZT.eq (Mat.det char2) (T * T + c₁ * T + c₀)

def companion3Formula : Fm PTm 8 := ZT.eq (Mat.det char3) (T * T * T + c₂ * (T * T) + c₁ * T + c₀)

theorem companion2_open : ([] : List (Fm PTm 8)) ⊢[PRAAx] companion2Formula := by
  apply ZT.derive
  simp [char2, Matrix.det_fin_two, Mat.toZ]
  ring

theorem companion3_open : ([] : List (Fm PTm 8)) ⊢[PRAAx] companion3Formula := by
  apply ZT.derive
  simp [char3, Matrix.det_fin_three, Mat.toZ]
  ring

/-- The characteristic polynomial of the companion matrix of a monic quadratic. -/
theorem companion2 : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 8 companion2Formula := closeAll 8 companion2_open

/-- The characteristic polynomial of the companion matrix of a monic cubic. -/
theorem companion3 : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 8 companion3Formula := closeAll 8 companion3_open

end Companion

/-! ## The quadratic example -/

section Quadratic

abbrev t : ZT 6 := .var2 0 1
abbrev a : ZT 6 := .var2 2 3
abbrev U : ZT 6 := .var2 4 5

/-- `M_y = [[0, t² + a], [1, 0]]`, multiplication by `y` in `ℤ[a, t][Y]/(Y² − t² − a)`. -/
def My : Mat 2 6 := ![![ZT.natLit 0, t * t + a], ![ZT.natLit 1, ZT.natLit 0]]

def quadFormula : Fm PTm 6 :=
  ZT.eq (Mat.det (Mat.sub (Mat.smul U Mat.one) My)) (U * U - (t * t + a))

def quadSqFormula : Fm PTm 6 :=
  ZT.eq (Mat.det (Mat.sub (Mat.smul U Mat.one) (Mat.mul My My))) (ZT.sq (U - (t * t + a)))

theorem quad_open : ([] : List (Fm PTm 6)) ⊢[PRAAx] quadFormula := by
  apply ZT.derive
  simp [My, Matrix.det_fin_two, Mat.toZ, Mat.sub, Mat.smul, Mat.one, Mat.mul, ZT.sumFin]
  all_goals ring

theorem quad_sq_open : ([] : List (Fm PTm 6)) ⊢[PRAAx] quadSqFormula := by
  apply ZT.derive
  simp [My, Matrix.det_fin_two, Mat.toZ, Mat.sub, Mat.smul, Mat.one, Mat.mul, ZT.sumFin]
  all_goals ring

/-- `det(U I − M_y) = U² − (t² + a)`. -/
theorem quad_observation : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 6 quadFormula := closeAll 6 quad_open

/-- `det(U I − M_y²) = (U − (t² + a))²`. -/
theorem quad_observation_sq : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 6 quadSqFormula := closeAll 6 quad_sq_open

end Quadratic

end LeanProofs.IPRA.Algebra.ObservationAlgebra
