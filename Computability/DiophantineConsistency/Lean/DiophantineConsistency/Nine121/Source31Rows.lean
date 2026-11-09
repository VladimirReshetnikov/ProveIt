import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # The literal 31-input positive parent source and its ring consequences

`rows` is the package-31 parent source (`parent_quartic31`, SHA-256
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`) with the old
positive transport coordinate, in the input order
`J F α z f h i o j s w τ η ζ y γ N E P c a X D C2 L F2 V g I Baux Δ` and ports
`β K MC MF`. It is a verbatim copy of `SplitCertificate59.sourceRows`, so that
this directory does not import the polynomial-coding stack; the record checker
compares both with the pinned JSON.

`facts` derives, in an arbitrary commutative ring, the sixteen register
identities used by the internal Pell argument (see
`55-congruence-norms/native/SOURCE31_ADAPTER.md`). -/
set_option autoImplicit false
namespace Nine121.Source31Rows

variable {R : Type*} [CommRing R]

/-- Original31 parent source, with the literal old-z transport. -/
def rows (ports : Fin 4 → R) (x : Fin 31 → R) : Fin 22 → R :=
  ![(x 24 + ((-2) * ports 0) * (x 0) + ((-(ports 0 ^ 2))) * (x 0 ^ 2)),
    ((-1) + (-1) * (x 24) + x 16 + ((-(ports 0))) * (x 0) + ((-(ports 0))) * (x 0 * x 24)),
    (x 21 + (-1) * (x 10) + ((-(ports 0))) * (x 0 * x 10)),
    (x 20 + (-1) * (x 17) + (-1) * (x 9 * x 16)),
    ((-1) * (x 20 * x 21) + x 17 + x 17 * x 21),
    (x 19 + (-1) * (x 13 * x 20) + x 13 * x 17 + (-1) * (x 12) + (-1) * (x 12 * x 20) + x 12 * x 17),
    (x 18 + (-1) * (x 17 * x 19) + (-1) * (x 13) + (-1) * (x 12) + x 12 * x 17),
    ((-1) + (-1) * (x 18 ^ 2) + x 13 * x 18 + x 12 * x 18 + x 11 ^ 2),
    (x 22 + (-1) * (x 21) + (-1) * (x 19 * x 20) + (-3) * (x 15) + (-4) * (x 15 * x 20)),
    ((-3) + x 30 + (-4) * (x 20) + (-1) * (x 20 ^ 2)),
    (x 23 + (-1) * (x 19 ^ 2)),
    ((-1) + (-1) * (x 23 * x 30) + x 22 ^ 2),
    ((-1) + x 26 + x 13 + x 12 + (-1) * (x 8 * x 19) + (-1) * (x 5 * x 17)),
    ((1) + (-1) * (x 26) + x 24 + (-1) * (x 16) + x 8 * x 19 + (-1) * (x 2 * x 24) + (-1) * (x 1) + (-1) * (x 1 * x 24) + x 1 * x 16 + ((-(ports 3)) + (-(ports 2)) + (2) * ports 0) * (x 0) + (ports 0) * (x 0 * x 24) + ((-(ports 0))) * (x 0 * x 16) + ((-(ports 0))) * (x 0 * x 1) + ((-(ports 0 * ports 3)) + ports 0 ^ 2) * (x 0 ^ 2)),
    ((ports 1) + x 10 + ((-(ports 1))) * (x 2) + (-1) * (x 2 * x 10) + (-1 + (-(ports 1))) * (x 1) + (-1) * (x 1 * x 10) + (ports 0 + ports 0 * ports 1) * (x 0) + (ports 0) * (x 0 * x 10) + ((-(ports 0))) * (x 0 * x 3)),
    (x 25 + (-1) * (x 4 ^ 2)),
    (x 26 + x 19 + (-1) * (x 4 * x 7)),
    (x 27 + x 26 ^ 2 + (-1) * (x 14 ^ 2)),
    (x 28 + (-1) * (x 6 * x 23)),
    (x 29 + (-1) * (x 28 ^ 2)),
    (x 30 + x 29 + (-1) * (x 25 * x 30)),
    ((-1) + (-1) * (x 27 * x 29) + x 14 ^ 2)]

/-- The register identities implied by a common zero, in any commutative ring.
Here `q = βJ + 1`, `k = η + ζ`, `Y = sN` and `Rf` is the packing formula. -/
theorem facts (ports : Fin 4 → R) (x : Fin 31 → R) (h : ∀ k, rows ports x k = 0) :
    let q := ports 0 * x 0 + 1
    let k := x 12 + x 13
    let Y := x 9 * x 16
    x 24 + 1 = q * q ∧ x 16 = q * (q * q) ∧ x 21 = x 10 * q ∧ x 20 = x 17 + Y ∧
    x 17 = x 21 * Y ∧ x 19 = x 12 + Y * k ∧
    x 11 * x 11 = 1 + ((x 21 * Y) * Y) * ((x 21 * Y) * Y + 1) * k * k ∧
    x 22 = x 21 + x 20 * x 19 + x 15 * (4 * x 20 + 3) ∧
    x 30 = x 20 * x 20 + 4 * x 20 + 3 ∧
    x 22 * x 22 = 1 + x 30 * (x 19 * x 19) ∧
    x 26 + k = 1 + x 8 * x 19 + x 5 * x 17 ∧
    x 8 * x 19 - x 26 = ((q - 1) * (q - x 1) + x 2) * (q * q - 1) + (ports 2 + q * ports 3) * x 0 ∧
    (ports 1 + x 10) * (q - x 1 - x 2) = x 1 + (x 3 - 1) * (q - 1) ∧
    x 26 + x 19 = x 4 * x 7 ∧
    (x 6 * (x 19 * x 19)) * (x 6 * (x 19 * x 19)) + x 30 = x 30 * (x 4 * x 4) ∧
    (x 6 * (x 19 * x 19)) * (x 6 * (x 19 * x 19)) * x 26 * x 26 + x 14 * x 14 =
      1 + (x 6 * (x 19 * x 19)) * (x 6 * (x 19 * x 19)) * x 14 * x 14 := by
  intro q k Y
  have r0 : (x 24 + ((-2) * ports 0) * (x 0) + ((-(ports 0 ^ 2))) * (x 0 ^ 2)) = 0 := h 0
  have r1 : ((-1) + (-1) * (x 24) + x 16 + ((-(ports 0))) * (x 0) + ((-(ports 0))) * (x 0 * x 24)) = 0 := h 1
  have r2 : (x 21 + (-1) * (x 10) + ((-(ports 0))) * (x 0 * x 10)) = 0 := h 2
  have r3 : (x 20 + (-1) * (x 17) + (-1) * (x 9 * x 16)) = 0 := h 3
  have r4 : ((-1) * (x 20 * x 21) + x 17 + x 17 * x 21) = 0 := h 4
  have r5 : (x 19 + (-1) * (x 13 * x 20) + x 13 * x 17 + (-1) * (x 12) + (-1) * (x 12 * x 20) + x 12 * x 17) = 0 := h 5
  have r6 : (x 18 + (-1) * (x 17 * x 19) + (-1) * (x 13) + (-1) * (x 12) + x 12 * x 17) = 0 := h 6
  have r7 : ((-1) + (-1) * (x 18 ^ 2) + x 13 * x 18 + x 12 * x 18 + x 11 ^ 2) = 0 := h 7
  have r8 : (x 22 + (-1) * (x 21) + (-1) * (x 19 * x 20) + (-3) * (x 15) + (-4) * (x 15 * x 20)) = 0 := h 8
  have r9 : ((-3) + x 30 + (-4) * (x 20) + (-1) * (x 20 ^ 2)) = 0 := h 9
  have r10 : (x 23 + (-1) * (x 19 ^ 2)) = 0 := h 10
  have r11 : ((-1) + (-1) * (x 23 * x 30) + x 22 ^ 2) = 0 := h 11
  have r12 : ((-1) + x 26 + x 13 + x 12 + (-1) * (x 8 * x 19) + (-1) * (x 5 * x 17)) = 0 := h 12
  have r13 : ((1) + (-1) * (x 26) + x 24 + (-1) * (x 16) + x 8 * x 19 + (-1) * (x 2 * x 24) + (-1) * (x 1) + (-1) * (x 1 * x 24) + x 1 * x 16 + ((-(ports 3)) + (-(ports 2)) + (2) * ports 0) * (x 0) + (ports 0) * (x 0 * x 24) + ((-(ports 0))) * (x 0 * x 16) + ((-(ports 0))) * (x 0 * x 1) + ((-(ports 0 * ports 3)) + ports 0 ^ 2) * (x 0 ^ 2)) = 0 := h 13
  have r14 : ((ports 1) + x 10 + ((-(ports 1))) * (x 2) + (-1) * (x 2 * x 10) + (-1 + (-(ports 1))) * (x 1) + (-1) * (x 1 * x 10) + (ports 0 + ports 0 * ports 1) * (x 0) + (ports 0) * (x 0 * x 10) + ((-(ports 0))) * (x 0 * x 3)) = 0 := h 14
  have r15 : (x 25 + (-1) * (x 4 ^ 2)) = 0 := h 15
  have r16 : (x 26 + x 19 + (-1) * (x 4 * x 7)) = 0 := h 16
  have r17 : (x 27 + x 26 ^ 2 + (-1) * (x 14 ^ 2)) = 0 := h 17
  have r18 : (x 28 + (-1) * (x 6 * x 23)) = 0 := h 18
  have r19 : (x 29 + (-1) * (x 28 ^ 2)) = 0 := h 19
  have r20 : (x 30 + x 29 + (-1) * (x 25 * x 30)) = 0 := h 20
  have r21 : ((-1) + (-1) * (x 27 * x 29) + x 14 ^ 2) = 0 := h 21
  have hL : x 24 + 1 = q * q := by linear_combination r0
  have hN : x 16 = q * (q * q) := by linear_combination r1 + q * hL
  have hc : x 19 = x 12 + Y * k := by linear_combination r5 + (x 12 + x 13) * r3
  have hE : x 17 = x 21 * Y := by linear_combination r4 + x 21 * r3
  have hP : x 18 = x 17 * (Y * k) + k := by linear_combination r6 + x 17 * hc
  have hτ1 : x 11 * x 11 = 1 + x 18 * (x 18 - k) := by linear_combination r7
  refine ⟨hL, hN, by linear_combination r2, by linear_combination r3, hE, hc, ?_,
    by linear_combination r8, by linear_combination r9, by linear_combination r11 + x 30 * r10,
    by linear_combination r12,
    by linear_combination r13 + (x 2 + x 1 - 1 - ports 0 * x 0) * hL +
      (1 - x 1 + ports 0 * x 0) * hN,
    by linear_combination r14, by linear_combination r16,
    by linear_combination r20 + x 30 * r15 - r19 -
      (x 28 + x 6 * (x 19 * x 19)) * (r18 + x 6 * r10),
    by linear_combination r21 + (x 6 * (x 19 * x 19)) * (x 6 * (x 19 * x 19)) * r17 + x 27 * r19 +
      x 27 * (x 28 + x 6 * (x 19 * x 19)) * (r18 + x 6 * r10)⟩
  rw [hτ1, hP, hE]
  ring

end Nine121.Source31Rows
