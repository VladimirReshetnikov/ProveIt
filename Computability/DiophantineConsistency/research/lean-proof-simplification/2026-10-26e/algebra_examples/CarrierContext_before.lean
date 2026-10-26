import Mathlib.Tactic

namespace DiophantineConsistency.Carrier65
variable {R : Type*} [CommRing R]

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


end DiophantineConsistency.Carrier65

namespace DiophantineConsistency.Carrier66
variable {R : Type*} [CommRing R]

def drop (v : Fin 15 → R) (n : R) (j : Fin 14) : R :=
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | 4 => v 4
  | 5 => v 6
  | 6 => v 7
  | 7 => v 8
  | 8 => v 9
  | 9 => n
  | 10 => v 11
  | 11 => v 12
  | 12 => v 13
  | _ => v 14

def core (p : Fin 4 → R) (v : Fin 15 → R) : Carrier65.Core R :=
  let b := Carrier65.core p (drop v 1)
  { b with tau := v 10, P := (v 10) ^ 2 - b.ell * (b.ell + b.k) }

def index (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  (core p v).k - v 5 * (core p v).E - (core p v).rank

def value (p : Fin 4 → R) (v : Fin 15 → R) : R :=
  let b := core p v
  b.P * b.Q * b.U * index p v * b.W * b.Z - b.delta

def restore (p : Fin 4 → R) (v : Fin 14 → R) (h : R) (j : Fin 15) : R :=
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => v 3
  | 4 => v 4
  | 5 => h
  | 6 => v 5
  | 7 => v 6
  | 8 => v 7
  | 9 => v 8
  | 10 => (Carrier65.core p v).tau
  | 11 => v 10
  | 12 => v 11
  | 13 => v 12
  | _ => v 13

def Canonical (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) : Prop :=
  (core p v).P = 1 ∧ (core p v).Q = 1 ∧ (core p v).U = 1 ∧
    index p v = 1 ∧ (core p v).W = 1 ∧ (core p v).Z = (core p v).delta ∧
      0 < (core p v).rank

theorem canonical_zero (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) (hc : Canonical p v) :
    value p v = 0 := by
  obtain ⟨hP, hQ, hU, hi, hW, hZ, _⟩ := hc
  dsimp only [value]
  rw [hP, hQ, hU, hi, hW, hZ]
  ring

#print axioms canonical_zero

theorem drop_pos (v : Fin 15 → ℤ) (n : ℤ)
    (hv : ∀ j, 0 < v j) (hn : 0 < n) : ∀ j, 0 < drop v n j := by
  intro j
  fin_cases j <;> first
    | exact hn
    | exact hv 0
    | exact hv 1
    | exact hv 2
    | exact hv 3
    | exact hv 4
    | exact hv 6
    | exact hv 7
    | exact hv 8
    | exact hv 9
    | exact hv 11
    | exact hv 12
    | exact hv 13
    | exact hv 14

#print axioms drop_pos

theorem restore_pos (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (h : ℤ)
    (hv : ∀ j, 0 < v j) (hh : 0 < h) (ht : 0 < (Carrier65.core p v).tau) :
    ∀ j, 0 < restore p v h j := by
  intro j
  fin_cases j <;> first
    | exact hh
    | exact ht
    | exact hv 0
    | exact hv 1
    | exact hv 2
    | exact hv 3
    | exact hv 4
    | exact hv 5
    | exact hv 6
    | exact hv 7
    | exact hv 8
    | exact hv 10
    | exact hv 11
    | exact hv 12
    | exact hv 13

#print axioms restore_pos

end DiophantineConsistency.Carrier66
