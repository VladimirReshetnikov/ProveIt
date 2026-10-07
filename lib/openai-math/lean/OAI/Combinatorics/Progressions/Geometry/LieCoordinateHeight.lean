import OAI.Combinatorics.Progressions.Polynomial.LieCoordinatePolynomials

namespace OAI

section

namespace Erdos3

open MvPolynomial

def lieCoordinateHeight (d H n : ℕ) : ℕ :=
  (d ^ 2 + H + 2) ^ ((2 * d ^ 2 + 2) ^ n)

theorem lieCoordinateHeight_pos (d H n : ℕ) : 0 < lieCoordinateHeight d H n := by
  unfold lieCoordinateHeight
  positivity

theorem lieCoordinateHeight_mono_length (d H : ℕ) : Monotone (lieCoordinateHeight d H) := by
  intro m n hmn
  unfold lieCoordinateHeight
  exact Nat.pow_le_pow_right (by omega)
    (Nat.pow_le_pow_right (by omega) hmn)

theorem lieCoordinateHeight_step (d H n : ℕ) :
    (d ^ 2 + 1) * (H * lieCoordinateHeight d H n) ^ (d ^ 2) ≤
      lieCoordinateHeight d H (n + 1) := by
  let A := d ^ 2 + H + 2
  let N := d ^ 2
  let E := (2 * N + 2) ^ n
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hE : 1 ≤ E := Nat.one_le_pow _ _ (by dsimp [N]; omega)
  have hH : H ≤ A := by dsimp [A]; omega
  have hN : N + 1 ≤ A := by dsimp [A, N]; omega
  change (N + 1) * (H * A ^ E) ^ N ≤ A ^ ((2 * N + 2) ^ (n + 1))
  calc
    (N + 1) * (H * A ^ E) ^ N ≤ A * (A * A ^ E) ^ N :=
      Nat.mul_le_mul hN (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hH) _)
    _ = A ^ (1 + (1 + E) * N) := by
      rw [← pow_succ', ← pow_mul, ← pow_succ']
      congr 1
      ring
    _ ≤ A ^ ((2 * N + 2) ^ (n + 1)) := by
      apply Nat.pow_le_pow_right hA
      rw [pow_succ]
      change 1 + (1 + E) * N ≤ E * (2 * N + 2)
      nlinarith

variable {ι X : Type*} [Fintype ι]

theorem coordinateRightBracket_height (c : ι → ι → ι → ℚ) {H K : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (x : X)
    (p : ι → MvPolynomial (X × ι) ℚ)
    (hp : ∀ i, RationalPolynomialHeightLE (p i) K) (k : ι) :
    RationalPolynomialHeightLE (coordinateRightBracket c x p k)
      ((Fintype.card ι ^ 2 + 1) * (H * K) ^ (Fintype.card ι ^ 2)) := by
  have h := RationalPolynomialHeightLE.sum
    (fun ij : ι × ι => C (c ij.1 ij.2 k) * p ij.1 * MvPolynomial.X (x, ij.2))
    (fun ij => (RationalPolynomialHeightLE.C_mul (hc ij.1 ij.2 k) (hp ij.1)).mul_X (x, ij.2))
  simpa only [coordinateRightBracket, Fintype.card_prod, pow_two] using h

theorem coordinateBracketList_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (xs : List X)
    (p : ι → MvPolynomial (X × ι) ℚ) {n : ℕ}
    (hp : ∀ i, RationalPolynomialHeightLE (p i) (lieCoordinateHeight (Fintype.card ι) H n))
    (k : ι) :
    RationalPolynomialHeightLE (coordinateBracketList c xs p k)
      (lieCoordinateHeight (Fintype.card ι) H (n + xs.length)) := by
  induction xs generalizing p n with
  | nil => exact hp k
  | cons x xs ih =>
    have hstep : ∀ i, RationalPolynomialHeightLE (coordinateRightBracket c x p i)
        (lieCoordinateHeight (Fintype.card ι) H (n + 1)) := fun i =>
      (coordinateRightBracket_height c hc x p hp i).mono (lieCoordinateHeight_step _ _ _)
    simpa only [coordinateBracketList, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 xs.length] using ih (coordinateRightBracket c x p) hstep

theorem dynkinCoordinatePolynomial_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (w : FreeSemigroup X) (k : ι) :
    RationalPolynomialHeightLE (dynkinCoordinatePolynomial c w k)
      (lieCoordinateHeight (Fintype.card ι) H w.length) := by
  have h := coordinateBracketList_height c hc w.tail
    (fun i => MvPolynomial.X (w.head, i)) (n := 0)
    (fun i => (RationalPolynomialHeightLE.X (w.head, i)).mono
      (lieCoordinateHeight_pos (Fintype.card ι) H 0)) k
  apply h.mono
  apply lieCoordinateHeight_mono_length
  change 0 + w.tail.length ≤ w.tail.length + 1
  omega

noncomputable def bchCoordinateHeight (s d H : ℕ) : ℕ :=
  ((bchBracketSupport s).card + 1) *
    (bchCoefficientHeight s * lieCoordinateHeight d H s) ^ (bchBracketSupport s).card

theorem bchCoordinatePolynomial_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (s : ℕ) (k : ι) :
    RationalPolynomialHeightLE (bchCoordinatePolynomial c s k)
      (bchCoordinateHeight s (Fintype.card ι) H) := by
  apply RationalPolynomialHeightLE.sum_finset
  intro w hw
  exact RationalPolynomialHeightLE.C_mul (bchBracketCoefficient_height s hw)
    ((dynkinCoordinatePolynomial_height c hc w k).mono
      (lieCoordinateHeight_mono_length _ _ (bchBracketSupport_length s hw)))

end Erdos3

end

end OAI
