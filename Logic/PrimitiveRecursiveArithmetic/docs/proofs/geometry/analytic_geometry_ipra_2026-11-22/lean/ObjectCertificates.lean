import IPRADerivations.Core.Tactic

/-!
# Analytic geometry: candidate object-iPRA polynomial certificates

STATUS: NOT TYPECHECKED IN THIS DELIVERY. No Lean executable was available.
These statements have actual `Prf PRAAx` types; they are not merely theorems
about Mathlib's real numbers. Their proofs use the repository's `ipra_ring`
reflection interface, inspected at commit
bbb85238dac533fc4b7b84a750cca864fe35fed5.

Each signed integer is a difference of two natural-number variables. Rational
versions require the separately described positive-denominator bridge. The
identities alone do not prove the classification or analytic existence results.
-/

namespace LeanProofs.IPRA.Geometry.AnalyticGeometryPacket

open LeanProofs.ConciseIPRA
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def N2 (x y : ZT n) : ZT n := x.sq + y.sq
def D2 (x y u v : ZT n) : ZT n := x * u + y * v
def W2 (x y u v : ZT n) : ZT n := x * v - y * u
def N3 (x y z : ZT n) : ZT n := x.sq + y.sq + z.sq
def D3 (x y z u v w : ZT n) : ZT n := x*u + y*v + z*w
def Q2 (a b c x y : ZT n) : ZT n := a*x*x + b*x*y + c*y*y
def F2 (a b c d e f x y : ZT n) : ZT n := Q2 a b c x y + d*x + e*y + f

/-- Two natural variables for each signed integer; no universal evaluator. -/
def zvar {k : ℕ} (i : Fin k) : ZT (2*k) :=
  .var2 ⟨2*i.val, by omega⟩ ⟨2*i.val+1, by omega⟩

/-- Two-dimensional Lagrange identity. -/
def lagrange2 {n : ℕ} (v : Fin 4 → ZT n) : Fm PTm n :=
  (N2 (v 0) (v 1) * N2 (v 2) (v 3)).eq
    ((D2 (v 0) (v 1) (v 2) (v 3)).sq + (W2 (v 0) (v 1) (v 2) (v 3)).sq)

theorem lagrange2_open (v : Fin 4 → ZT n) :
    Γ ⊢[PRAAx] lagrange2 v := by
  unfold lagrange2 N2 D2 W2
  ipra_ring

def lagrange2_sentence : Fm PTm 0 :=
  univ 8 (lagrange2 (fun i : Fin 4 => zvar i))

theorem lagrange2_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] lagrange2_sentence :=
  closeUniv 8 (lagrange2_open _)

/-- Parallelogram identity, including degenerate vectors. -/
def parallelogram {n : ℕ} (v : Fin 4 → ZT n) : Fm PTm n :=
  (N2 (v 0+v 2) (v 1+v 3) + N2 (v 0-v 2) (v 1-v 3)).eq
    (ZT.natLit 2 * (N2 (v 0) (v 1) + N2 (v 2) (v 3)))

theorem parallelogram_open (v : Fin 4 → ZT n) :
    Γ ⊢[PRAAx] parallelogram v := by
  unfold parallelogram N2
  ipra_ring

def parallelogram_sentence : Fm PTm 0 :=
  univ 8 (parallelogram (fun i : Fin 4 => zvar i))

theorem parallelogram_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] parallelogram_sentence :=
  closeUniv 8 (parallelogram_open _)

/-- Squared-distance cosine identity. -/
def cosine {n : ℕ} (v : Fin 4 → ZT n) : Fm PTm n :=
  (N2 (v 0-v 2) (v 1-v 3)).eq
    (N2 (v 0) (v 1) + N2 (v 2) (v 3) - ZT.natLit 2*D2 (v 0) (v 1) (v 2) (v 3))

theorem cosine_open (v : Fin 4 → ZT n) :
    Γ ⊢[PRAAx] cosine v := by
  unfold cosine N2 D2
  ipra_ring

def cosine_sentence : Fm PTm 0 :=
  univ 8 (cosine (fun i : Fin 4 => zvar i))

theorem cosine_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] cosine_sentence :=
  closeUniv 8 (cosine_open _)

/-- First Cramer numerator identity: aX+bY=det(A)e. -/
def cramer_row1 {n : ℕ} (v : Fin 6 → ZT n) : Fm PTm n :=
  (v 0*(v 4*v 3-v 1*v 5)+v 1*(v 0*v 5-v 4*v 2)).eq
    ((v 0*v 3-v 1*v 2)*v 4)

theorem cramer_row1_open (v : Fin 6 → ZT n) :
    Γ ⊢[PRAAx] cramer_row1 v := by
  unfold cramer_row1
  ipra_ring

def cramer_row1_sentence : Fm PTm 0 :=
  univ 12 (cramer_row1 (fun i : Fin 6 => zvar i))

theorem cramer_row1_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] cramer_row1_sentence :=
  closeUniv 12 (cramer_row1_open _)

/-- Second Cramer numerator identity: cX+dY=det(A)f. -/
def cramer_row2 {n : ℕ} (v : Fin 6 → ZT n) : Fm PTm n :=
  (v 2*(v 4*v 3-v 1*v 5)+v 3*(v 0*v 5-v 4*v 2)).eq
    ((v 0*v 3-v 1*v 2)*v 5)

theorem cramer_row2_open (v : Fin 6 → ZT n) :
    Γ ⊢[PRAAx] cramer_row2 v := by
  unfold cramer_row2
  ipra_ring

def cramer_row2_sentence : Fm PTm 0 :=
  univ 12 (cramer_row2 (fun i : Fin 6 => zvar i))

theorem cramer_row2_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] cramer_row2_sentence :=
  closeUniv 12 (cramer_row2_open _)

/-- Adjugate recovery of both coordinates; uniqueness after guarded cancellation. -/
def cramer_recover {n : ℕ} (v : Fin 6 → ZT n) : Fm PTm n :=
  ((v 3*(v 0*v 4+v 1*v 5)-v 1*(v 2*v 4+v 3*v 5)).eq
      ((v 0*v 3-v 1*v 2)*v 4)) ⋏
    ((v 0*(v 2*v 4+v 3*v 5)-v 2*(v 0*v 4+v 1*v 5)).eq
      ((v 0*v 3-v 1*v 2)*v 5))

theorem cramer_recover_open (v : Fin 6 → ZT n) :
    Γ ⊢[PRAAx] cramer_recover v := by
  unfold cramer_recover
  refine Prf.andI ?_ ?_ <;> ipra_ring

def cramer_recover_sentence : Fm PTm 0 :=
  univ 12 (cramer_recover (fun i : Fin 6 => zvar i))

theorem cramer_recover_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] cramer_recover_sentence :=
  closeUniv 12 (cramer_recover_open _)

/-- Norm under a scaled rotation; set c²+s²=1 for a rotation. -/
def rotation_norm {n : ℕ} (v : Fin 4 → ZT n) : Fm PTm n :=
  (N2 (v 0*v 2-v 1*v 3) (v 1*v 2+v 0*v 3)).eq
    (N2 (v 0) (v 1)*N2 (v 2) (v 3))

theorem rotation_norm_open (v : Fin 4 → ZT n) :
    Γ ⊢[PRAAx] rotation_norm v := by
  unfold rotation_norm N2
  ipra_ring

def rotation_norm_sentence : Fm PTm 0 :=
  univ 8 (rotation_norm (fun i : Fin 4 => zvar i))

theorem rotation_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] rotation_norm_sentence :=
  closeUniv 8 (rotation_norm_open _)

/-- Dot product under the same scaled rotation. -/
def rotation_dot {n : ℕ} (v : Fin 6 → ZT n) : Fm PTm n :=
  (D2 (v 0*v 2-v 1*v 3) (v 1*v 2+v 0*v 3)
      (v 0*v 4-v 1*v 5) (v 1*v 4+v 0*v 5)).eq
    (N2 (v 0) (v 1)*D2 (v 2) (v 3) (v 4) (v 5))

theorem rotation_dot_open (v : Fin 6 → ZT n) :
    Γ ⊢[PRAAx] rotation_dot v := by
  unfold rotation_dot N2 D2
  ipra_ring

def rotation_dot_sentence : Fm PTm 0 :=
  univ 12 (rotation_dot (fun i : Fin 6 => zvar i))

theorem rotation_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] rotation_dot_sentence :=
  closeUniv 12 (rotation_dot_open _)

/-- An invertible linear map scales oriented doubled areas by its determinant. -/
def affine_determinant {n : ℕ} (v : Fin 8 → ZT n) : Fm PTm n :=
  (W2 (v 0*v 4+v 1*v 5) (v 2*v 4+v 3*v 5)
      (v 0*v 6+v 1*v 7) (v 2*v 6+v 3*v 7)).eq
    ((v 0*v 3-v 1*v 2)*W2 (v 4) (v 5) (v 6) (v 7))

theorem affine_determinant_open (v : Fin 8 → ZT n) :
    Γ ⊢[PRAAx] affine_determinant v := by
  unfold affine_determinant W2
  ipra_ring

def affine_determinant_sentence : Fm PTm 0 :=
  univ 16 (affine_determinant (fun i : Fin 8 => zvar i))

theorem affine_determinant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] affine_determinant_sentence :=
  closeUniv 16 (affine_determinant_open _)

/-- Cleared-denominator reflection identity. -/
def reflection_norm {n : ℕ} (v : Fin 4 → ZT n) : Fm PTm n :=
  let q := N2 (v 0) (v 1)
  let h := D2 (v 0) (v 1) (v 2) (v 3)
  (N2 (q*v 2-ZT.natLit 2*h*v 0) (q*v 3-ZT.natLit 2*h*v 1)).eq
    (q.sq*N2 (v 2) (v 3))

theorem reflection_norm_open (v : Fin 4 → ZT n) :
    Γ ⊢[PRAAx] reflection_norm v := by
  unfold reflection_norm N2 D2
  ipra_ring

def reflection_norm_sentence : Fm PTm 0 :=
  univ 8 (reflection_norm (fun i : Fin 4 => zvar i))

theorem reflection_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] reflection_norm_sentence :=
  closeUniv 8 (reflection_norm_open _)

/-- Cleared squared norm of the orthogonal residual. -/
def projection_remainder {n : ℕ} (v : Fin 4 → ZT n) : Fm PTm n :=
  let q := N2 (v 0) (v 1)
  let h := D2 (v 0) (v 1) (v 2) (v 3)
  (N2 (q*v 2-h*v 0) (q*v 3-h*v 1)).eq
    (q*(q*N2 (v 2) (v 3)-h.sq))

theorem projection_remainder_open (v : Fin 4 → ZT n) :
    Γ ⊢[PRAAx] projection_remainder v := by
  unfold projection_remainder N2 D2
  ipra_ring

def projection_remainder_sentence : Fm PTm 0 :=
  univ 8 (projection_remainder (fun i : Fin 4 => zvar i))

theorem projection_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] projection_remainder_sentence :=
  closeUniv 8 (projection_remainder_open _)

/-- Rational parametrization of the unit circle after clearing 1+t². -/
def circle_parameter {n : ℕ} (v : Fin 1 → ZT n) : Fm PTm n :=
  (N2 (ZT.natLit 1-(v 0).sq) (ZT.natLit 2*v 0)).eq
    ((ZT.natLit 1+(v 0).sq).sq)

theorem circle_parameter_open (v : Fin 1 → ZT n) :
    Γ ⊢[PRAAx] circle_parameter v := by
  unfold circle_parameter N2
  ipra_ring

def circle_parameter_sentence : Fm PTm 0 :=
  univ 2 (circle_parameter (fun i : Fin 1 => zvar i))

theorem circle_parameter_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] circle_parameter_sentence :=
  closeUniv 2 (circle_parameter_open _)

/-- Stereographic rational parametrization of the unit sphere. -/
def sphere_parameter {n : ℕ} (v : Fin 2 → ZT n) : Fm PTm n :=
  (N3 (ZT.natLit 2*v 0) (ZT.natLit 2*v 1)
      (ZT.natLit 1-(v 0).sq-(v 1).sq)).eq
    ((ZT.natLit 1+(v 0).sq+(v 1).sq).sq)

theorem sphere_parameter_open (v : Fin 2 → ZT n) :
    Γ ⊢[PRAAx] sphere_parameter v := by
  unfold sphere_parameter N3
  ipra_ring

def sphere_parameter_sentence : Fm PTm 0 :=
  univ 4 (sphere_parameter (fun i : Fin 2 => zvar i))

theorem sphere_parameter_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] sphere_parameter_sentence :=
  closeUniv 4 (sphere_parameter_open _)

/-- 4a(ax²+bx+c)=(2ax+b)²-(b²-4ac). -/
def quadratic_completion {n : ℕ} (v : Fin 4 → ZT n) : Fm PTm n :=
  (ZT.natLit 4*v 0*(v 0*(v 3).sq+v 1*v 3+v 2)).eq
    ((ZT.natLit 2*v 0*v 3+v 1).sq-((v 1).sq-ZT.natLit 4*v 0*v 2))

theorem quadratic_completion_open (v : Fin 4 → ZT n) :
    Γ ⊢[PRAAx] quadratic_completion v := by
  unfold quadratic_completion
  ipra_ring

def quadratic_completion_sentence : Fm PTm 0 :=
  univ 8 (quadratic_completion (fun i : Fin 4 => zvar i))

theorem quadratic_completion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] quadratic_completion_sentence :=
  closeUniv 8 (quadratic_completion_open _)

/-- Focus/directrix squared-distance identity for y²=4px. -/
def parabola_focus {n : ℕ} (v : Fin 3 → ZT n) : Fm PTm n :=
  (N2 (v 1-v 0) (v 2)-(v 1+v 0).sq).eq
    ((v 2).sq-ZT.natLit 4*v 0*v 1)

theorem parabola_focus_open (v : Fin 3 → ZT n) :
    Γ ⊢[PRAAx] parabola_focus v := by
  unfold parabola_focus N2
  ipra_ring

def parabola_focus_sentence : Fm PTm 0 :=
  univ 6 (parabola_focus (fun i : Fin 3 => zvar i))

theorem parabola_focus_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] parabola_focus_sentence :=
  closeUniv 6 (parabola_focus_open _)

/-- Exact second-order expansion of a conic on a line. -/
def conic_line_expansion {n : ℕ} (v : Fin 11 → ZT n) : Fm PTm n :=
  (F2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
      (v 6+v 10*v 8) (v 7+v 10*v 9)).eq
    (F2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) +
     v 10*((ZT.natLit 2*v 0*v 6+v 1*v 7+v 3)*v 8 +
           (v 1*v 6+ZT.natLit 2*v 2*v 7+v 4)*v 9) +
     (v 10).sq*Q2 (v 0) (v 1) (v 2) (v 8) (v 9))

theorem conic_line_expansion_open (v : Fin 11 → ZT n) :
    Γ ⊢[PRAAx] conic_line_expansion v := by
  unfold conic_line_expansion F2 Q2
  ipra_ring

def conic_line_expansion_sentence : Fm PTm 0 :=
  univ 22 (conic_line_expansion (fun i : Fin 11 => zvar i))

theorem conic_line_expansion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] conic_line_expansion_sentence :=
  closeUniv 22 (conic_line_expansion_open _)

/-- Conic discriminant multiplies by the square of the linear determinant. -/
def discriminant_congruence {n : ℕ} (v : Fin 7 → ZT n) : Fm PTm n :=
  let a' := v 0*(v 3).sq+v 1*v 3*v 5+v 2*(v 5).sq
  let b' := ZT.natLit 2*v 0*v 3*v 4+v 1*(v 3*v 6+v 4*v 5)+ZT.natLit 2*v 2*v 5*v 6
  let c' := v 0*(v 4).sq+v 1*v 4*v 6+v 2*(v 6).sq
  (b'.sq-ZT.natLit 4*a'*c').eq
    ((v 3*v 6-v 4*v 5).sq*((v 1).sq-ZT.natLit 4*v 0*v 2))

theorem discriminant_congruence_open (v : Fin 7 → ZT n) :
    Γ ⊢[PRAAx] discriminant_congruence v := by
  unfold discriminant_congruence
  ipra_ring

def discriminant_congruence_sentence : Fm PTm 0 :=
  univ 14 (discriminant_congruence (fun i : Fin 7 => zvar i))

theorem discriminant_congruence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] discriminant_congruence_sentence :=
  closeUniv 14 (discriminant_congruence_open _)

/-- The cross product is perpendicular to both original vectors. -/
def cross_orthogonal {n : ℕ} (v : Fin 6 → ZT n) : Fm PTm n :=
  let a := v 1*v 5-v 2*v 4
  let b := v 2*v 3-v 0*v 5
  let c := v 0*v 4-v 1*v 3
  ((D3 a b c (v 0) (v 1) (v 2)).eq (ZT.natLit 0)) ⋏
    ((D3 a b c (v 3) (v 4) (v 5)).eq (ZT.natLit 0))

theorem cross_orthogonal_open (v : Fin 6 → ZT n) :
    Γ ⊢[PRAAx] cross_orthogonal v := by
  unfold cross_orthogonal D3
  refine Prf.andI ?_ ?_ <;> ipra_ring

def cross_orthogonal_sentence : Fm PTm 0 :=
  univ 12 (cross_orthogonal (fun i : Fin 6 => zvar i))

theorem cross_orthogonal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] cross_orthogonal_sentence :=
  closeUniv 12 (cross_orthogonal_open _)

/-- Three-dimensional Lagrange identity. -/
def lagrange3 {n : ℕ} (v : Fin 6 → ZT n) : Fm PTm n :=
  (N3 (v 0) (v 1) (v 2)*N3 (v 3) (v 4) (v 5)).eq
    ((D3 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)).sq+
     N3 (v 1*v 5-v 2*v 4) (v 2*v 3-v 0*v 5) (v 0*v 4-v 1*v 3))

theorem lagrange3_open (v : Fin 6 → ZT n) :
    Γ ⊢[PRAAx] lagrange3 v := by
  unfold lagrange3 N3 D3
  ipra_ring

def lagrange3_sentence : Fm PTm 0 :=
  univ 12 (lagrange3 (fun i : Fin 6 => zvar i))

theorem lagrange3_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] lagrange3_sentence :=
  closeUniv 12 (lagrange3_open _)

/-- u×(v×w)=v(u·w)-w(u·v), with all three coordinates stated. -/
def vector_triple {n : ℕ} (v : Fin 9 → ZT n) : Fm PTm n :=
  let a := v 4*v 8-v 5*v 7
  let b := v 5*v 6-v 3*v 8
  let c := v 3*v 7-v 4*v 6
  let h := D3 (v 0) (v 1) (v 2) (v 6) (v 7) (v 8)
  let k := D3 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)
  ((v 1*c-v 2*b).eq (v 3*h-v 6*k)) ⋏
    (((v 2*a-v 0*c).eq (v 4*h-v 7*k)) ⋏
      ((v 0*b-v 1*a).eq (v 5*h-v 8*k)))

theorem vector_triple_open (v : Fin 9 → ZT n) :
    Γ ⊢[PRAAx] vector_triple v := by
  unfold vector_triple D3
  refine Prf.andI ?_ (Prf.andI ?_ ?_) <;> ipra_ring

def vector_triple_sentence : Fm PTm 0 :=
  univ 18 (vector_triple (fun i : Fin 9 => zvar i))

theorem vector_triple_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] vector_triple_sentence :=
  closeUniv 18 (vector_triple_open _)

/-- The normal component of an interpoint displacement is constant along two lines. -/
def skew_line_invariant {n : ℕ} (v : Fin 11 → ZT n) : Fm PTm n :=
  let a := v 1*v 5-v 2*v 4
  let b := v 2*v 3-v 0*v 5
  let c := v 0*v 4-v 1*v 3
  (D3 (v 6+v 9*v 0-v 10*v 3) (v 7+v 9*v 1-v 10*v 4)
      (v 8+v 9*v 2-v 10*v 5) a b c).eq
    (D3 (v 6) (v 7) (v 8) a b c)

theorem skew_line_invariant_open (v : Fin 11 → ZT n) :
    Γ ⊢[PRAAx] skew_line_invariant v := by
  unfold skew_line_invariant D3
  ipra_ring

def skew_line_invariant_sentence : Fm PTm 0 :=
  univ 22 (skew_line_invariant (fun i : Fin 11 => zvar i))

theorem skew_line_invariant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] skew_line_invariant_sentence :=
  closeUniv 22 (skew_line_invariant_open _)

/-- Three-point weighted variance identity; positivity is a separate guarded result. -/
def weighted_variance {n : ℕ} (v : Fin 9 → ZT n) : Fm PTm n :=
  ((v 0+v 1+v 2)*(v 0*N2 (v 3) (v 4)+v 1*N2 (v 5) (v 6)+v 2*N2 (v 7) (v 8))-
      N2 (v 0*v 3+v 1*v 5+v 2*v 7) (v 0*v 4+v 1*v 6+v 2*v 8)).eq
    (v 0*v 1*N2 (v 3-v 5) (v 4-v 6)+v 0*v 2*N2 (v 3-v 7) (v 4-v 8)+
      v 1*v 2*N2 (v 5-v 7) (v 6-v 8))

theorem weighted_variance_open (v : Fin 9 → ZT n) :
    Γ ⊢[PRAAx] weighted_variance v := by
  unfold weighted_variance N2
  ipra_ring

def weighted_variance_sentence : Fm PTm 0 :=
  univ 18 (weighted_variance (fun i : Fin 9 => zvar i))

theorem weighted_variance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] weighted_variance_sentence :=
  closeUniv 18 (weighted_variance_open _)

/-- Subtracting two circle powers gives an affine linear expression. -/
def radical_axis {n : ℕ} (v : Fin 8 → ZT n) : Fm PTm n :=
  ((N2 (v 0-v 2) (v 1-v 3)-v 6)-(N2 (v 0-v 4) (v 1-v 5)-v 7)).eq
    (ZT.natLit 2*((v 4-v 2)*v 0+(v 5-v 3)*v 1)+
      N2 (v 2) (v 3)-N2 (v 4) (v 5)-v 6+v 7)

theorem radical_axis_open (v : Fin 8 → ZT n) :
    Γ ⊢[PRAAx] radical_axis v := by
  unfold radical_axis N2
  ipra_ring

def radical_axis_sentence : Fm PTm 0 :=
  univ 16 (radical_axis (fun i : Fin 8 => zvar i))

theorem radical_axis_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] radical_axis_sentence :=
  closeUniv 16 (radical_axis_open _)

/-- Symmetric second difference of a quadratic is twice its homogeneous quadratic part. -/
def conic_midpoint {n : ℕ} (v : Fin 10 → ZT n) : Fm PTm n :=
  (F2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6+v 8) (v 7+v 9)+
      F2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6-v 8) (v 7-v 9)).eq
    (ZT.natLit 2*F2 (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)+
      ZT.natLit 2*Q2 (v 0) (v 1) (v 2) (v 8) (v 9))

theorem conic_midpoint_open (v : Fin 10 → ZT n) :
    Γ ⊢[PRAAx] conic_midpoint v := by
  unfold conic_midpoint F2 Q2
  ipra_ring

def conic_midpoint_sentence : Fm PTm 0 :=
  univ 20 (conic_midpoint (fun i : Fin 10 => zvar i))

theorem conic_midpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] conic_midpoint_sentence :=
  closeUniv 20 (conic_midpoint_open _)

end LeanProofs.IPRA.Geometry.AnalyticGeometryPacket

/-! Audit all intended closed object-language endpoints after a successful build. -/
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.lagrange2_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.parallelogram_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.cosine_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.cramer_row1_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.cramer_row2_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.cramer_recover_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.rotation_norm_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.rotation_dot_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.affine_determinant_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.reflection_norm_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.projection_remainder_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.circle_parameter_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.sphere_parameter_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.quadratic_completion_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.parabola_focus_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.conic_line_expansion_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.discriminant_congruence_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.cross_orthogonal_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.lagrange3_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.vector_triple_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.skew_line_invariant_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.weighted_variance_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.radical_axis_closed
#print axioms LeanProofs.IPRA.Geometry.AnalyticGeometryPacket.conic_midpoint_closed
