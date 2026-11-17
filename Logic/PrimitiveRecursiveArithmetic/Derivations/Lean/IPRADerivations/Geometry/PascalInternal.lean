import IPRADerivations.Geometry.DesarguesInternal

/-!
# Internal Pascal

Packet: `desargues_pascal_ipra`, `sections/05_pascal.tex`, Theorem `thm:pas-summary`.

* `pascal_universal` (`eq:pascal-universal`): over every commutative ring,
  `[X Y Z] = det(ν(P₁), …, ν(P₆))` with `ν(x, y, z) = (x², y², z², xy, xz, yz)` and the Pascal points
  `X = (P₁×P₂)×(P₄×P₅)`, `Y = (P₂×P₃)×(P₅×P₆)`, `Z = (P₃×P₄)×(P₆×P₁)`, by expansion;
* `conic_det` (`eq:conic-certificate`): if `Q(Pᵢ) = 0` for all six points and a specified coefficient
  `q_j` is nonzero, then `det M = 0` for the Veronese matrix `M`, from `adj(M) M = det(M) I`;
* `pascal_det`, `pascal_axis` (`thm:pas-summary`): `[X Y Z] = 0`, and for `X ≠ 0` the explicit
  `axis(X, Y, Z)` is a nonzero line through the three points.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.PascalInternal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Geometry.CevaMenelaus (nz zt_cancel)
open LeanProofs.IPRA.Geometry.DesarguesInternal (nzV axis kernel axis_spec meet)
open Syn Matrix
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The universal identity over a commutative ring -/

/-- The Veronese vector `(x², y², z², xy, xz, yz)`. -/
def nu {R : Type*} [CommRing R] (P : Fin 3 → R) : Fin 6 → R :=
  ![P 0 * P 0, P 1 * P 1, P 2 * P 2, P 0 * P 1, P 0 * P 2, P 1 * P 2]

/-- Expansion of a triple product of three two-term combinations of four vectors. -/
theorem trilinear4 {R : Type*} [CommRing R] (s₁ s₂ s₃ s₄ s₅ s₆ : R) (A B C D : Fin 3 → R) :
    (s₁ • A - s₂ • B) ⬝ᵥ ((s₃ • B - s₄ • C) ⨯₃ (s₅ • C - s₆ • D))
      = s₁ * s₃ * s₅ * (A ⬝ᵥ (B ⨯₃ C)) - s₁ * s₃ * s₆ * (A ⬝ᵥ (B ⨯₃ D))
        + s₁ * s₄ * s₆ * (A ⬝ᵥ (C ⨯₃ D)) - s₂ * s₄ * s₆ * (B ⬝ᵥ (C ⨯₃ D)) := by
  simp [crossProduct, dotProduct, Fin.sum_univ_three]
  ring

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- The four-term bracket form of `[X Y Z]` equals the Veronese determinant. -/
theorem four_term {R : Type*} [CommRing R] (P₁ P₂ P₃ P₄ P₅ P₆ : Fin 3 → R) :
    (P₁ ⬝ᵥ (P₂ ⨯₃ P₅)) * (P₂ ⬝ᵥ (P₃ ⨯₃ P₆)) * (P₃ ⬝ᵥ (P₄ ⨯₃ P₁)) * (P₄ ⬝ᵥ (P₅ ⨯₃ P₆))
      - (P₁ ⬝ᵥ (P₂ ⨯₃ P₅)) * (P₂ ⬝ᵥ (P₃ ⨯₃ P₆)) * (P₃ ⬝ᵥ (P₄ ⨯₃ P₆)) * (P₄ ⬝ᵥ (P₅ ⨯₃ P₁))
      + (P₁ ⬝ᵥ (P₂ ⨯₃ P₅)) * (P₂ ⬝ᵥ (P₃ ⨯₃ P₅)) * (P₃ ⬝ᵥ (P₄ ⨯₃ P₆)) * (P₄ ⬝ᵥ (P₆ ⨯₃ P₁))
      - (P₁ ⬝ᵥ (P₂ ⨯₃ P₄)) * (P₂ ⬝ᵥ (P₃ ⨯₃ P₅)) * (P₃ ⬝ᵥ (P₄ ⨯₃ P₆)) * (P₅ ⬝ᵥ (P₆ ⨯₃ P₁)) =
      Matrix.det (Matrix.of ![nu P₁, nu P₂, nu P₃, nu P₄, nu P₅, nu P₆]) := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.det_isEmpty,
    Matrix.submatrix_apply, Matrix.of_apply, Fin.succAbove_zero, Fin.succ_succAbove_zero,
    Fin.succ_succAbove_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.val_zero, Fin.val_succ, pow_zero, pow_succ]
  simp only [nu, crossProduct, dotProduct, Fin.sum_univ_three, LinearMap.mk₂_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

/-- `eq:pascal-universal`: `[X Y Z] = det(ν(P₁), …, ν(P₆))`. As in the packet, the double cross
identity writes `X = [125]P₄ − [124]P₅`, `Y = [236]P₅ − [235]P₆`, `Z = [341]P₆ − [346]P₁`, and
multilinearity leaves four bracket products. -/
theorem pascal_universal {R : Type*} [CommRing R] (P₁ P₂ P₃ P₄ P₅ P₆ : Fin 3 → R) :
    ((P₁ ⨯₃ P₂) ⨯₃ (P₄ ⨯₃ P₅)) ⬝ᵥ (((P₂ ⨯₃ P₃) ⨯₃ (P₅ ⨯₃ P₆)) ⨯₃ ((P₃ ⨯₃ P₄) ⨯₃ (P₆ ⨯₃ P₁))) =
      Matrix.det (Matrix.of ![nu P₁, nu P₂, nu P₃, nu P₄, nu P₅, nu P₆]) := by
  rw [Projective.doubleCross P₁ P₂ P₄ P₅, Projective.doubleCross P₂ P₃ P₅ P₆,
    Projective.doubleCross P₃ P₄ P₆ P₁, trilinear4, ← four_term]

/-- `q_j det M = ∑_i adj(M)_{j i} (M q)_i`. -/
theorem cofactor_cert {R : Type*} [CommRing R] (M : Matrix (Fin 6) (Fin 6) R) (q : Fin 6 → R) (j : Fin 6) :
    M.det * q j = (M.adjugate *ᵥ (M *ᵥ q)) j := by
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]; rfl


/-! ## The iPRA theorems -/

/-- `ν(P)` for an integer triple. -/
def nuV (P : Vec 3 n) : Vec 6 n := ![P 0 * P 0, P 1 * P 1, P 2 * P 2, P 0 * P 1, P 0 * P 2, P 1 * P 2]

/-- The Veronese matrix with rows `ν(P₁), …, ν(P₆)`. -/
def VM (P₁ P₂ P₃ P₄ P₅ P₆ : Vec 3 n) : Mat 6 n := fun i k => (![nuV P₁, nuV P₂, nuV P₃, nuV P₄, nuV P₅, nuV P₆] i) k

theorem toZ_nuV (P : Vec 3 n) : Vec.toZ Γ (nuV P) = nu (Vec.toZ Γ P) := by
  funext i; fin_cases i <;> simp [nuV, nu, Vec.toZ]

theorem toZ_VM (P₁ P₂ P₃ P₄ P₅ P₆ : Vec 3 n) : Mat.toZ Γ (VM P₁ P₂ P₃ P₄ P₅ P₆) =
    Matrix.of ![nu (Vec.toZ Γ P₁), nu (Vec.toZ Γ P₂), nu (Vec.toZ Γ P₃), nu (Vec.toZ Γ P₄),
      nu (Vec.toZ Γ P₅), nu (Vec.toZ Γ P₆)] := by
  ext i k; fin_cases i <;> simp [VM, ← toZ_nuV, Mat.toZ, Vec.toZ]

section Conic

variable {P₁ P₂ P₃ P₄ P₅ P₆ : Vec 3 n} {q : Vec 6 n}

/-- `Q(P) = q · ν(P) = 0`. -/
abbrev onConic (q : Vec 6 n) (P : Vec 3 n) : Fm PTm n := ZT.eq (Vec.dot (nuV P) q) (ZT.natLit 0)

theorem conic_zero {P : Vec 3 n} (h : Γ ⊢[PRAAx] onConic q P) : nu (Vec.toZ Γ P) ⬝ᵥ Vec.toZ Γ q = 0 := by
  have e := ZT.toZ_eq h
  rw [Vec.toZ_dot, toZ_nuV, ZT.toZ_natLit] at e
  simpa using e

/-- `eq:conic-certificate`: six points on a conic with a nonzero coefficient `q_j` have a singular
Veronese matrix. -/
theorem conic_det (j : Fin 6) (hq : Γ ⊢[PRAAx] nz (q j)) (h₁ : Γ ⊢[PRAAx] onConic q P₁)
    (h₂ : Γ ⊢[PRAAx] onConic q P₂) (h₃ : Γ ⊢[PRAAx] onConic q P₃) (h₄ : Γ ⊢[PRAAx] onConic q P₄)
    (h₅ : Γ ⊢[PRAAx] onConic q P₅) (h₆ : Γ ⊢[PRAAx] onConic q P₆) :
    Γ ⊢[PRAAx] ZT.eq (Mat.det (VM P₁ P₂ P₃ P₄ P₅ P₆)) (ZT.natLit 0) := by
  have mq : Mat.toZ Γ (VM P₁ P₂ P₃ P₄ P₅ P₆) *ᵥ Vec.toZ Γ q = 0 := by
    rw [toZ_VM]
    funext i
    fin_cases i
    · exact conic_zero h₁
    · exact conic_zero h₂
    · exact conic_zero h₃
    · exact conic_zero h₄
    · exact conic_zero h₅
    · exact conic_zero h₆
  refine zt_cancel hq (ZT.derive ?_)
  rw [ZT.toZ_mul, ZT.toZ_mul, Mat.toZ_det, ZT.toZ_natLit, _root_.mul_comm]
  have c := cofactor_cert (Mat.toZ Γ (VM P₁ P₂ P₃ P₄ P₅ P₆)) (Vec.toZ Γ q) j
  rw [mq, Matrix.mulVec_zero] at c
  simpa using c

/-- `thm:pas-summary`: the Pascal points of six points on a conic are collinear, `[X Y Z] = 0`. -/
theorem pascal_det (j : Fin 6) (hq : Γ ⊢[PRAAx] nz (q j)) (h₁ : Γ ⊢[PRAAx] onConic q P₁)
    (h₂ : Γ ⊢[PRAAx] onConic q P₂) (h₃ : Γ ⊢[PRAAx] onConic q P₃) (h₄ : Γ ⊢[PRAAx] onConic q P₄)
    (h₅ : Γ ⊢[PRAAx] onConic q P₅) (h₆ : Γ ⊢[PRAAx] onConic q P₆) :
    Γ ⊢[PRAAx] ZT.eq (Vec.triple (meet P₁ P₂ P₄ P₅) (meet P₂ P₃ P₅ P₆) (meet P₃ P₄ P₆ P₁)) (ZT.natLit 0) := by
  have d := ZT.toZ_eq (conic_det j hq h₁ h₂ h₃ h₄ h₅ h₆)
  rw [Mat.toZ_det, toZ_VM] at d
  refine ZT.derive ?_
  simp only [Vec.toZ_triple, Vec.toZ_cross]
  rw [pascal_universal, d]

/-- `thm:pas-summary`, with the witness: for `X ≠ 0`, `axis(X, Y, Z)` is a nonzero common line. -/
theorem pascal_axis (j : Fin 6) (hq : Γ ⊢[PRAAx] nz (q j)) (h₁ : Γ ⊢[PRAAx] onConic q P₁)
    (h₂ : Γ ⊢[PRAAx] onConic q P₂) (h₃ : Γ ⊢[PRAAx] onConic q P₃) (h₄ : Γ ⊢[PRAAx] onConic q P₄)
    (h₅ : Γ ⊢[PRAAx] onConic q P₅) (h₆ : Γ ⊢[PRAAx] onConic q P₆) (hX : Γ ⊢[PRAAx] nzV (meet P₁ P₂ P₄ P₅)) :
    Γ ⊢[PRAAx] kernel (axis (meet P₁ P₂ P₄ P₅) (meet P₂ P₃ P₅ P₆) (meet P₃ P₄ P₆ P₁))
      (meet P₁ P₂ P₄ P₅) (meet P₂ P₃ P₅ P₆) (meet P₃ P₄ P₆ P₁) :=
  axis_spec hX (pascal_det j hq h₁ h₂ h₃ h₄ h₅ h₆)

end Conic

end LeanProofs.IPRA.Geometry.PascalInternal
