import DiophantineConsistency.ShortSystem
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The literal fourteen-variable Carrier65 front

This is the arithmetic front printed on the decimal 2011 page.  The four
ports are parameters, ordered `beta, K, MC, MF_source`; the last port
already includes the single beta shift.  The coordinate order is
`J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma`.

The sign theorem applies to every positive zero of this actual polynomial.
It assumes only a positive beta, and does not assume a native interpretation,
positivity of the carrier tau, positivity of C, or bounds on the rank.
No native compiler correctness or Con(ZFC) theorem is asserted here.
-/

namespace DiophantineConsistency.Carrier65

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The displayed arithmetic blocks, with `rank` denoting the printed R. -/
structure Core (R : Type*) where
  q : R
  C : R
  X : R
  Y : R
  E : R
  k : R
  ell : R
  c : R
  a : R
  H : R
  delta : R
  D : R
  rank : R
  tau : R
  V : R
  S : R
  P : R
  Q : R
  U : R
  W : R
  Z : R
  f : R
  i : R
  y : R

/-- The literal page, with its fourteen independent coordinates and four ports. -/
def core (p : Fin 4 → R) (v : Fin 14 → R) : Core R :=
  let J := v 0
  let F := v 1
  let alpha := v 2
  let z := v 3
  let f := v 4
  let i := v 5
  let T := v 6
  let s := v 7
  let w := v 8
  let n := v 9
  let eta := v 10
  let zeta := v 11
  let y := v 12
  let gamma := v 13
  let b := p 0 * J
  let q := b + 1
  let C := q - F - alpha
  let X := w * q
  let Y := s * q ^ 3
  let E := X * Y
  let k := eta + zeta
  let ell := E * k * Y
  let c := k * Y + eta
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + gamma * H
  let rank := (b * (q - F) + alpha) * (q ^ 2 - 1) + (p 2 + q * p 3) * J
  let tau := E * n + k - rank
  let V := f ^ 2 * (c * T - rank) - c
  let S := i * delta * c ^ 2
  let P := tau ^ 2 - ell * (ell + k)
  let Q := D ^ 2 - delta * c ^ 2
  let U := S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2
  let W := (p 1 + w) * C + (q - F) - z * b
  let Z := delta * f ^ 2 - S ^ 2
  ⟨q, C, X, Y, E, k, ell, c, a, H, delta, D, rank, tau, V, S,
    P, Q, U, W, Z, f, i, y⟩

/-- The complete polynomial value, without division or additional variables. -/
def value (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  let b := core p v
  b.P * b.Q * b.U * b.W * b.Z - b.delta

/-- The unscaled strong Pell norm. -/
def strong (b : Core R) : R := b.f ^ 2 - b.delta * (b.i * b.c ^ 2) ^ 2

theorem q_sub_one (p : Fin 4 → R) (v : Fin 14 → R) :
    (core p v).q - 1 = p 0 * v 0 := by
  change p 0 * v 0 + 1 - 1 = _
  ring

theorem scale_shape (p : Fin 4 → R) (v : Fin 14 → R) :
    (core p v).E = v 8 * v 7 * (core p v).q ^ 4 := by
  change (v 8 * (core p v).q) * (v 7 * (core p v).q ^ 3) = _
  ring

theorem rank_shape (p : Fin 4 → R) (v : Fin 14 → R) :
    (core p v).rank =
      (((core p v).q - 1) * ((core p v).q - v 1) + v 2) *
        ((core p v).q ^ 2 - 1) + (p 2 + (core p v).q * p 3) * v 0 := by
  rw [q_sub_one]
  rfl

theorem transport_shape (p : Fin 4 → R) (v : Fin 14 → R) :
    (core p v).W = (p 1 + v 8) * ((core p v).q - v 1 - v 2) +
      ((core p v).q - v 1) - v 3 * ((core p v).q - 1) := by
  rw [q_sub_one]
  rfl

theorem carrier_shape (p : Fin 4 → R) (v : Fin 14 → R) :
    (core p v).tau = (core p v).E * v 9 + (core p v).k - (core p v).rank := rfl

theorem delta_shape (p : Fin 4 → R) (v : Fin 14 → R) :
    (core p v).delta = ((core p v).a + 2) ^ 2 - 1 := by
  change (core p v).a ^ 2 + (4 * (core p v).a + 3) = _
  ring

/-- No sign of tau is used in this consecutive-product Pell identity. -/
theorem first_shape (p : Fin 4 → R) (v : Fin 14 → R) :
    (core p v).P = (core p v).tau ^ 2 -
      ((core p v).E * (core p v).Y) * ((core p v).E * (core p v).Y + 1) *
        (core p v).k ^ 2 := by
  change (core p v).tau ^ 2 -
    ((core p v).E * (core p v).k * (core p v).Y) *
      ((core p v).E * (core p v).k * (core p v).Y + (core p v).k) = _
  ring

theorem strong_scale (p : Fin 4 → R) (v : Fin 14 → R) :
    (core p v).Z = (core p v).delta * strong (core p v) := by
  change (core p v).delta * (core p v).f ^ 2 -
    ((core p v).i * (core p v).delta * (core p v).c ^ 2) ^ 2 = _
  unfold strong
  ring

/-- Exact normalization, before imposing any zero or positivity condition. -/
theorem scaled_identity (p : Fin 4 → R) (v : Fin 14 → R) :
    value p v = (core p v).delta *
      ((core p v).P * (core p v).Q * (core p v).U * (core p v).W *
        strong (core p v) - 1) := by
  dsimp only [value]
  rw [strong_scale]
  ring

/-- The literal formula commutes with every ring homomorphism. -/
theorem value_map (φ : R →+* S) (p : Fin 4 → R) (v : Fin 14 → R) :
    φ (value p v) = value (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value, core, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]

/-- The actual fourteen-variable multivariate polynomial over the integers. -/
noncomputable def polynomial (p : Fin 4 → ℤ) : MvPolynomial (Fin 14) ℤ :=
  value (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) :
    MvPolynomial.eval v (polynomial p) = value p v := by
  simpa only [polynomial, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem q_ge_two (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) : 2 ≤ (core p v).q := by
  change 2 ≤ p 0 * v 0 + 1
  have := mul_pos hbeta (hv 0)
  omega

theorem scales_pos (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) :
    0 < (core p v).X ∧ 0 < (core p v).Y ∧ 0 < (core p v).E ∧
      0 < (core p v).a := by
  have hq : 0 < (core p v).q := lt_of_lt_of_le (by norm_num) (q_ge_two p v hbeta hv)
  have hX : 0 < (core p v).X := mul_pos (hv 8) hq
  have hY : 0 < (core p v).Y := mul_pos (hv 7) (pow_pos hq 3)
  have hE : 0 < (core p v).E := mul_pos hX hY
  exact ⟨hX, hY, hE, add_pos hE hY⟩

theorem delta_pos (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) : 0 < (core p v).delta := by
  have ha := (scales_pos p v hbeta hv).2.2.2
  rw [delta_shape]
  nlinarith

theorem firstParameter_ge_two (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) :
    2 ≤ (core p v).E * (core p v).Y := by
  have hq := q_ge_two p v hbeta hv
  have hw := hv 8
  have hX : 2 ≤ (core p v).X := by
    change 2 ≤ v 8 * (core p v).q
    nlinarith
  have hY := (scales_pos p v hbeta hv).2.1
  have hY1 : 1 ≤ (core p v).Y := hY
  have hE : 2 ≤ (core p v).E := by
    change 2 ≤ (core p v).X * (core p v).Y
    nlinarith
  nlinarith

/-- Cancellation of the positive discriminant exposes a product of integer units. -/
theorem value_zero_iff_product (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hdelta : (core p v).delta ≠ 0) :
    value p v = 0 ↔
      (core p v).P * (core p v).Q * (core p v).U * (core p v).W *
        strong (core p v) = 1 := by
  rw [scaled_identity, mul_eq_zero]
  simp only [hdelta, false_or, sub_eq_zero]

/-- All signs are derived on every positive actual zero; tau and rank are unrestricted. -/
theorem value_zero_iff_norms (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v = 0 ↔
      (core p v).P = 1 ∧ (core p v).Q = 1 ∧ (core p v).U = 1 ∧
        strong (core p v) = 1 ∧ (core p v).W = 1 := by
  have hP : (core p v).P ≠ -1 := by
    rw [first_shape]
    exact ConsecutivePell.norm_ne_neg_one _ _ _ (firstParameter_ge_two p v hbeta hv)
  have hQ : (core p v).Q ≠ -1 := by
    change (core p v).D ^ 2 - (core p v).delta * (core p v).c ^ 2 ≠ -1
    rw [delta_shape]
    exact ShortEquation.strong_ne_neg_one _ _ _
  have hs : strong (core p v) ≠ -1 := by
    unfold strong
    rw [delta_shape]
    exact ShortEquation.strong_ne_neg_one _ _ _
  have hU : (core p v).U ≠ -1 :=
    ShortSystem.square_aux_ne_neg_one (core p v).S (core p v).V (core p v).y
  rw [value_zero_iff_product p v (ne_of_gt (delta_pos p v hbeta hv))]
  simpa only [mul_one, one_mul] using
    ShortSystem.product_eq_one_iff (core p v).P (core p v).Q (core p v).U
      1 (core p v).W (strong (core p v)) hP hQ hs (fun _ => hU)

/-- The scaled strong factor has the prescribed positive value at any positive zero. -/
theorem scaled_strong_eq_delta (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) (hzero : value p v = 0) :
    (core p v).Z = (core p v).delta := by
  have hs := ((value_zero_iff_norms p v hbeta hv).mp hzero).2.2.2.1
  rw [strong_scale, hs, mul_one]

theorem eval_polynomial_zero_iff_norms (p : Fin 4 → ℤ) (v : Fin 14 → ℤ)
    (hbeta : 0 < p 0) (hv : ∀ j, 0 < v j) :
    MvPolynomial.eval v (polynomial p) = 0 ↔
      (core p v).P = 1 ∧ (core p v).Q = 1 ∧ (core p v).U = 1 ∧
        strong (core p v) = 1 ∧ (core p v).W = 1 := by
  rw [eval_polynomial]
  exact value_zero_iff_norms p v hbeta hv

#print axioms eval_polynomial_zero_iff_norms

end DiophantineConsistency.Carrier65
