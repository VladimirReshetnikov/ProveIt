import DiophantineConsistency.ShortEquation
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Fin.VecNotation

/-!
# Literal thirteen-coordinate carrier variants and their local equivalence

The coordinates are `J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma` and the
ports are `beta,K,MC,MF_source`. These are the accepted 69/174, 70/140
and 71/128 arithmetic formulas, rather than the historical fifteen-variable
`ShortCircuit`. This file proves their whole positive zero sets agree.
The fresh-seed map and native consistency calibration remain separate.
-/

namespace DiophantineConsistency.ThirteenCarrier

variable {R S : Type*} [CommRing R] [CommRing S]

structure Core (R : Type*) where
  a : R
  delta : R
  t : R
  f : R
  gap : R
  y : R
  P : R
  Q : R

def core (p : Fin 4 → R) (v : Fin 13 → R) : Core R :=
  let b := p 0 * v 0
  let q := b + 1
  let C := q - v 1 - v 2
  let X := v 7 * q
  let Y := v 6 * q ^ 3
  let E := X * Y
  let k := v 9 + v 10
  let ell := E * k * Y
  let c := k * Y + v 9
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + v 12 * H
  let rank := (b * (q - v 1) + v 2) * (q ^ 2 - 1) + (p 2 + q * p 3) * v 0
  let tau := E * v 8 + k - rank
  let f := v 3
  let V := f ^ 2 * (c * v 5 - rank) - c
  let G := (p 1 + v 7) * C - v 1
  let y := 1 + 4 * (b * (v 11 - V ^ 2 * G) - G)
  ⟨a, delta, b * v 4 * c ^ 2, f, V ^ 2 - y ^ 2, y,
    tau ^ 2 - ell * (ell + k), D ^ 2 - delta * c ^ 2⟩

def value69 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  let b := core p v
  let S := b.delta * b.t
  b.P * b.Q * (S ^ 2 * b.gap + b.y ^ 2) * (b.delta * b.f ^ 2 - S ^ 2) - b.delta

def value70 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  let b := core p v
  b.P * b.Q * (b.delta * (b.f ^ 2 - 1) * b.gap + b.y ^ 2) *
    (b.delta * b.f ^ 2 - (b.delta * b.t) ^ 2) - b.delta

def value71 (p : Fin 4 → R) (v : Fin 13 → R) : R :=
  let b := core p v
  b.P * b.Q * (b.delta * (b.f ^ 2 - 1) * b.gap + b.y ^ 2) *
    (b.f ^ 2 - b.delta * b.t ^ 2) - 1

theorem delta_shape (p : Fin 4 → R) (v : Fin 13 → R) :
    (core p v).delta = ((core p v).a + 2) ^ 2 - 1 := by
  change (core p v).a ^ 2 + (4 * (core p v).a + 3) = _
  ring

theorem scaled_identity (p : Fin 4 → R) (v : Fin 13 → R) :
    value70 p v = (core p v).delta * value71 p v := by
  dsimp only [value70, value71]
  ring

theorem value69_zero_iff_value71_zero (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hd : (core p v).delta ≠ 0) : value69 p v = 0 ↔ value71 p v = 0 := by
  have he := ShortEquation.scaled_zero_iff_reduced
    (m := (core p v).P * (core p v).Q) (f := (core p v).f)
    (t := (core p v).t) (gap := (core p v).gap) (y := (core p v).y)
    (a := (core p v).a) (by rwa [← delta_shape] : ((core p v).a + 2) ^ 2 - 1 ≠ 0)
  dsimp only at he
  rw [← delta_shape] at he
  have hleft : value69 p v =
      ((core p v).P * (core p v).Q) *
        ((core p v).delta ^ 2 * (core p v).t ^ 2 * (core p v).gap + (core p v).y ^ 2) *
        ((core p v).delta * (core p v).f ^ 2 - (core p v).delta ^ 2 * (core p v).t ^ 2) -
        (core p v).delta := by
    dsimp only [value69]
    ring
  rw [hleft]
  exact he

theorem value70_zero_iff_value71_zero (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hd : (core p v).delta ≠ 0) : value70 p v = 0 ↔ value71 p v = 0 := by
  rw [scaled_identity, mul_eq_zero]
  simp only [hd, false_or]

theorem delta_pos (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) : 0 < (core p v).delta := by
  have hJ := hv 0
  have hq : 0 < p 0 * v 0 + 1 := by positivity
  have hX : 0 < v 7 * (p 0 * v 0 + 1) := mul_pos (hv 7) hq
  have hY : 0 < v 6 * (p 0 * v 0 + 1) ^ 3 := mul_pos (hv 6) (pow_pos hq _)
  have ha : 0 < (core p v).a := add_pos (mul_pos hX hY) hY
  rw [delta_shape]
  nlinarith

/-- The accepted three arithmetic profiles have identical whole positive zero sets. -/
theorem positive_zero_sets (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    (value69 p v = 0 ↔ value71 p v = 0) ∧
      (value70 p v = 0 ↔ value71 p v = 0) := by
  have hd := ne_of_gt (delta_pos p v hb hv)
  exact ⟨value69_zero_iff_value71_zero p v hd, value70_zero_iff_value71_zero p v hd⟩

theorem value69_map (φ : R →+* S) (p : Fin 4 → R) (v : Fin 13 → R) :
    φ (value69 p v) = value69 (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value69, core, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]

theorem value70_map (φ : R →+* S) (p : Fin 4 → R) (v : Fin 13 → R) :
    φ (value70 p v) = value70 (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value70, core, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]

theorem value71_map (φ : R →+* S) (p : Fin 4 → R) (v : Fin 13 → R) :
    φ (value71 p v) = value71 (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value71, core, map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]

noncomputable def polynomial69 (p : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value69 (fun j => MvPolynomial.C (p j)) MvPolynomial.X

noncomputable def polynomial70 (p : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value70 (fun j => MvPolynomial.C (p j)) MvPolynomial.X

noncomputable def polynomial71 (p : Fin 4 → ℤ) : MvPolynomial (Fin 13) ℤ :=
  value71 (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial69 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial69 p) = value69 p v := by
  simpa only [polynomial69, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value69_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial70 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial70 p) = value70 p v := by
  simpa only [polynomial70, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value70_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem eval_polynomial71 (p : Fin 4 → ℤ) (v : Fin 13 → ℤ) :
    MvPolynomial.eval v (polynomial71 p) = value71 p v := by
  simpa only [polynomial71, MvPolynomial.eval_C, MvPolynomial.eval_X] using
    value71_map (MvPolynomial.eval v) (fun j => MvPolynomial.C (p j)) MvPolynomial.X

theorem positive_polynomial_zero_sets (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    (MvPolynomial.eval v (polynomial69 p) = 0 ↔ MvPolynomial.eval v (polynomial71 p) = 0) ∧
      (MvPolynomial.eval v (polynomial70 p) = 0 ↔ MvPolynomial.eval v (polynomial71 p) = 0) := by
  simpa only [eval_polynomial69, eval_polynomial70, eval_polynomial71] using
    positive_zero_sets p v hb hv

end DiophantineConsistency.ThirteenCarrier
