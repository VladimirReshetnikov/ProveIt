import Mathlib.LinearAlgebra.Basis.Defs
import OAI.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
import OAI.Combinatorics.Progressions.Polynomial.PolynomialIntegerInputs

namespace OAI

section

namespace Erdos3

open MvPolynomial Module

variable {ι X L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def lieStructureConstants (e : Basis ι ℚ L) (i j k : ι) : ℚ :=
  e.repr ⁅e i, e j⁆ k

theorem lie_coordinate_formula (e : Basis ι ℚ L) (a b : L) (k : ι) :
    e.repr ⁅a, b⁆ k =
      ∑ ij : ι × ι, lieStructureConstants e ij.1 ij.2 k * e.repr a ij.1 * e.repr b ij.2 := by
  classical
  conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    lieStructureConstants, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def coordinateRightBracket (c : ι → ι → ι → ℚ) (x : X)
    (p : ι → MvPolynomial (X × ι) ℚ) (k : ι) : MvPolynomial (X × ι) ℚ :=
  ∑ ij : ι × ι, C (c ij.1 ij.2 k) * p ij.1 * MvPolynomial.X (x, ij.2)

noncomputable def coordinateBracketList (c : ι → ι → ι → ℚ) :
    List X → (ι → MvPolynomial (X × ι) ℚ) → (ι → MvPolynomial (X × ι) ℚ)
  | [], p => p
  | x :: xs, p => coordinateBracketList c xs (coordinateRightBracket c x p)

noncomputable def dynkinCoordinatePolynomial (c : ι → ι → ι → ℚ)
    (w : FreeSemigroup X) : ι → MvPolynomial (X × ι) ℚ :=
  coordinateBracketList c w.tail (fun i => MvPolynomial.X (w.head, i))

theorem coordinateRightBracket_eval (e : Basis ι ℚ L) (f : X → L)
    (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (x : X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (coordinateRightBracket (lieStructureConstants e) x p k) = e.repr ⁅a, f x⁆ k := by
  simp only [coordinateRightBracket, map_sum, map_mul, aeval_C, aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply, hp]
  exact (lie_coordinate_formula e a (f x) k).symm

theorem coordinateBracketList_eval (e : Basis ι ℚ L) (f : X → L) (xs : List X)
    (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (coordinateBracketList (lieStructureConstants e) xs p k) =
      e.repr (rightBracketList f xs a) k := by
  induction xs generalizing p a with
  | nil => exact hp k
  | cons x xs ih =>
    exact ih (coordinateRightBracket (lieStructureConstants e) x p) ⁅a, f x⁆
      (coordinateRightBracket_eval e f p a hp x)

theorem dynkinCoordinatePolynomial_eval (e : Basis ι ℚ L) (f : X → L)
    (w : FreeSemigroup X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (dynkinCoordinatePolynomial (lieStructureConstants e) w k) =
      e.repr (dynkinWord f w) k := by
  apply coordinateBracketList_eval
  intro i
  simp only [aeval_X]

theorem coordinateRightBracket_totalDegree (c : ι → ι → ι → ℚ) (x : X)
    (p : ι → MvPolynomial (X × ι) ℚ) {n : ℕ}
    (hp : ∀ i, (p i).totalDegree ≤ n) (k : ι) :
    (coordinateRightBracket c x p k).totalDegree ≤ n + 1 := by
  apply totalDegree_finsetSum_le
  intro ij _
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_X]
    have h := totalDegree_mul (C (c ij.1 ij.2 k)) (p ij.1)
    rw [totalDegree_C, zero_add] at h
    exact Nat.add_le_add_right (h.trans (hp ij.1)) 1)

theorem coordinateBracketList_totalDegree (c : ι → ι → ι → ℚ) (xs : List X)
    (p : ι → MvPolynomial (X × ι) ℚ) {n : ℕ}
    (hp : ∀ i, (p i).totalDegree ≤ n) (k : ι) :
    (coordinateBracketList c xs p k).totalDegree ≤ n + xs.length := by
  induction xs generalizing p n with
  | nil => exact hp k
  | cons x xs ih =>
    simpa only [coordinateBracketList, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 xs.length] using
      ih (coordinateRightBracket c x p) (coordinateRightBracket_totalDegree c x p hp)

theorem dynkinCoordinatePolynomial_totalDegree (c : ι → ι → ι → ℚ)
    (w : FreeSemigroup X) (k : ι) :
    (dynkinCoordinatePolynomial c w k).totalDegree ≤ w.length := by
  have h := coordinateBracketList_totalDegree c w.tail
    (fun i => MvPolynomial.X (w.head, i)) (n := 1)
    (fun _ => (totalDegree_X _).le) k
  simpa only [dynkinCoordinatePolynomial, FreeSemigroup.length, Nat.add_comm] using h

noncomputable def bchCoordinatePolynomial (c : ι → ι → ι → ℚ) (s : ℕ)
    (k : ι) : MvPolynomial (Fin 2 × ι) ℚ :=
  ∑ w ∈ bchBracketSupport s,
    C (bchBracketCoefficient s w) * dynkinCoordinatePolynomial c w k

theorem bchCoordinatePolynomial_eval (e : Basis ι ℚ L) (s : ℕ) (a b : L) (k : ι) :
    aeval (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2)
        (bchCoordinatePolynomial (lieStructureConstants e) s k) = e.repr (lieBCH s a b) k := by
  rw [lieBCH_bracket_formula]
  simp only [bchCoordinatePolynomial, map_sum, map_mul, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply,
    dynkinCoordinatePolynomial_eval, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply,
    smul_eq_mul]

theorem bchCoordinatePolynomial_totalDegree (c : ι → ι → ι → ℚ) (s : ℕ) (k : ι) :
    (bchCoordinatePolynomial c s k).totalDegree ≤ s := by
  apply totalDegree_finsetSum_le
  intro w hw
  have h := totalDegree_mul (C (bchBracketCoefficient s w)) (dynkinCoordinatePolynomial c w k)
  rw [totalDegree_C, zero_add] at h
  exact h.trans ((dynkinCoordinatePolynomial_totalDegree c w k).trans (bchBracketSupport_length s hw))

end Erdos3

end

end OAI
