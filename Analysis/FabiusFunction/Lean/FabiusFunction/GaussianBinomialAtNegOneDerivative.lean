import FabiusFunction.GaussianBinomialAtNegOne
import FabiusFunction.QPochhammerElementaryIdentities
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The first Gaussian-binomial jet at `q = -1`

This module differentiates the denominator-free Gaussian identities at the
second root of unity.  Reciprocity is differentiated algebraically with dual
numbers, so no analytic calculus or division by a vanishing q-factor enters
the proof.

## Main results

* `gaussianBinomial_derivative_eval_neg_one_of_even_degree` gives the exact
  derivative of every even-degree Gaussian polynomial over any commutative
  ring.
* `gaussianBinomial_derivative_eval_neg_one_even_odd` gives the exceptional
  even-row/odd-column derivative, where the value itself vanishes.
* `gaussianBinomial_even_odd_rootMultiplicity_int` proves that this root is
  simple over the integers in the admissible range.
* `gaussianBinomial_even_odd_rootMultiplicity` transports simplicity to every
  characteristic-zero commutative ring.
-/

set_option autoImplicit false

open scoped DualNumber

namespace Fabius

private noncomputable abbrev gaussianPolynomialInt (n k : ℕ) : Polynomial ℤ :=
  gaussianBinomial (Polynomial.X : Polynomial ℤ) n k

private theorem gaussianPolynomialInt_aeval_dual_add_eps (n k : ℕ) :
    gaussianBinomial ((-1 : DualNumber ℤ) + ε) n k =
      algebraMap ℤ (DualNumber ℤ) (gaussianBinomial (-1 : ℤ) n k) +
        algebraMap ℤ (DualNumber ℤ)
            ((gaussianPolynomialInt n k).derivative.eval (-1)) * ε := by
  let q : DualNumber ℤ := (-1 : DualNumber ℤ) + ε
  change gaussianBinomial q n k = _
  have hmap := map_gaussianBinomial
    (Polynomial.aeval q).toRingHom (Polynomial.X : Polynomial ℤ) n k
  have hmap' :
      (gaussianPolynomialInt n k).aeval q = gaussianBinomial q n k := by
    change (Polynomial.aeval q).toRingHom
      (gaussianBinomial (Polynomial.X : Polynomial ℤ) n k) =
        gaussianBinomial q n k
    rw [hmap]
    simp
  have hq : q = algebraMap ℤ (DualNumber ℤ) (-1) + ε := by
    simp [q]
  have heval :
      (gaussianPolynomialInt n k).eval (-1) = gaussianBinomial (-1 : ℤ) n k := by
    simpa only [gaussianPolynomialInt, Polynomial.coe_evalRingHom,
      Polynomial.eval_X] using
      (map_gaussianBinomial (Polynomial.evalRingHom (-1))
        (Polynomial.X : Polynomial ℤ) n k)
  calc
    gaussianBinomial q n k = (gaussianPolynomialInt n k).aeval q := hmap'.symm
    _ = (gaussianPolynomialInt n k).aeval
            (algebraMap ℤ (DualNumber ℤ) (-1)) +
          (gaussianPolynomialInt n k).derivative.aeval
            (algebraMap ℤ (DualNumber ℤ) (-1)) * ε := by
      rw [hq]
      exact
        (Polynomial.aeval_add_of_sq_eq_zero
          (gaussianPolynomialInt n k)
          (algebraMap ℤ (DualNumber ℤ) (-1)) ε DualNumber.eps_pow_two)
    _ = algebraMap ℤ (DualNumber ℤ) (gaussianBinomial (-1 : ℤ) n k) +
          algebraMap ℤ (DualNumber ℤ)
              ((gaussianPolynomialInt n k).derivative.eval (-1)) * ε := by
      rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      rw [heval]

private theorem gaussianPolynomialInt_aeval_dual_sub_eps (n k : ℕ) :
    gaussianBinomial ((-1 : DualNumber ℤ) - ε) n k =
      algebraMap ℤ (DualNumber ℤ) (gaussianBinomial (-1 : ℤ) n k) -
        algebraMap ℤ (DualNumber ℤ)
            ((gaussianPolynomialInt n k).derivative.eval (-1)) * ε := by
  let q : DualNumber ℤ := (-1 : DualNumber ℤ) - ε
  change gaussianBinomial q n k = _
  have hmap := map_gaussianBinomial
    (Polynomial.aeval q).toRingHom (Polynomial.X : Polynomial ℤ) n k
  have hmap' :
      (gaussianPolynomialInt n k).aeval q = gaussianBinomial q n k := by
    change (Polynomial.aeval q).toRingHom
      (gaussianBinomial (Polynomial.X : Polynomial ℤ) n k) =
        gaussianBinomial q n k
    rw [hmap]
    simp
  have hq : q = algebraMap ℤ (DualNumber ℤ) (-1) - ε := by
    simp [q]
  have heval :
      (gaussianPolynomialInt n k).eval (-1) = gaussianBinomial (-1 : ℤ) n k := by
    simpa only [gaussianPolynomialInt, Polynomial.coe_evalRingHom,
      Polynomial.eval_X] using
      (map_gaussianBinomial (Polynomial.evalRingHom (-1))
        (Polynomial.X : Polynomial ℤ) n k)
  calc
    gaussianBinomial q n k = (gaussianPolynomialInt n k).aeval q := hmap'.symm
    _ = (gaussianPolynomialInt n k).aeval
            (algebraMap ℤ (DualNumber ℤ) (-1)) +
          (gaussianPolynomialInt n k).derivative.aeval
            (algebraMap ℤ (DualNumber ℤ) (-1)) * (-ε) := by
      rw [hq, sub_eq_add_neg]
      exact Polynomial.aeval_add_of_sq_eq_zero
        (gaussianPolynomialInt n k)
        (algebraMap ℤ (DualNumber ℤ) (-1)) (-ε)
        (by simp : (-ε : DualNumber ℤ) ^ 2 = 0)
    _ = algebraMap ℤ (DualNumber ℤ) (gaussianBinomial (-1 : ℤ) n k) -
          algebraMap ℤ (DualNumber ℤ)
              ((gaussianPolynomialInt n k).derivative.eval (-1)) * ε := by
      rw [Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      rw [heval]
      ring

private theorem dual_neg_one_add_eps_pow_even (d : ℕ) :
    ((-1 : DualNumber ℤ) + ε) ^ (d + d) =
      1 - algebraMap ℤ (DualNumber ℤ) ((2 * d : ℕ) : ℤ) * ε := by
  induction d with
  | zero => simp
  | succ d ih =>
      calc
        ((-1 : DualNumber ℤ) + ε) ^ (Nat.succ d + Nat.succ d) =
            ((-1 : DualNumber ℤ) + ε) ^ (d + d) *
              ((-1 : DualNumber ℤ) + ε) ^ 2 := by
          rw [show Nat.succ d + Nat.succ d = (d + d) + 2 by omega, pow_add]
        _ = (1 - algebraMap ℤ (DualNumber ℤ) ((2 * d : ℕ) : ℤ) * ε) *
              ((-1 : DualNumber ℤ) + ε) ^ 2 := by rw [ih]
        _ = 1 - algebraMap ℤ (DualNumber ℤ)
              ((2 * Nat.succ d : ℕ) : ℤ) * ε := by
          apply TrivSqZeroExt.ext
          · norm_num
          · simp [pow_two, TrivSqZeroExt.fst_natCast]
            have htwo : TrivSqZeroExt.fst (2 : DualNumber ℤ) = (2 : ℤ) :=
              TrivSqZeroExt.fst_natCast 2
            rw [htwo]
            ring

private theorem gaussianBinomial_derivative_eval_neg_one_of_even_degree_int
    (n k : ℕ) (hdegree : Even (k * (n - k))) :
    (gaussianPolynomialInt n k).derivative.eval (-1) =
      -((k * (n - k) / 2 : ℕ) : ℤ) * gaussianBinomial (-1 : ℤ) n k := by
  let q : DualNumber ℤ := (-1 : DualNumber ℤ) + ε
  let qinv : DualNumber ℤ := (-1 : DualNumber ℤ) - ε
  have hmul : q * qinv = 1 := by
    apply TrivSqZeroExt.ext <;> simp [q, qinv]
  let u : (DualNumber ℤ)ˣ := Units.mkOfMulEqOne q qinv hmul
  have hrec := gaussianBinomial_reciprocity_units u n k
  change q ^ (k * (n - k)) * gaussianBinomial qinv n k =
    gaussianBinomial q n k at hrec
  rcases hdegree with ⟨d, hd⟩
  have hqpow : q ^ (d + d) =
      1 - algebraMap ℤ (DualNumber ℤ) ((2 * d : ℕ) : ℤ) * ε := by
    exact dual_neg_one_add_eps_pow_even d
  rw [gaussianPolynomialInt_aeval_dual_add_eps,
    gaussianPolynomialInt_aeval_dual_sub_eps, hd, hqpow] at hrec
  have hsnd := congrArg (TrivSqZeroExt.snd (R := ℤ) (M := ℤ)) hrec
  simp [TrivSqZeroExt.fst_natCast] at hsnd
  change
    -(gaussianPolynomialInt n k).derivative.eval (-1) +
        -(2 * (d : ℤ) * gaussianBinomial (-1 : ℤ) n k) =
      (gaussianPolynomialInt n k).derivative.eval (-1) at hsnd
  have hhalf : (d + d) / 2 = d := by omega
  rw [hd, hhalf]
  linarith

/-- **Reciprocity derivative at the second root of unity.**  Let
`D = k(n-k)`.  Whenever `D` is even, over every commutative ring,

`G'_{n,k}(-1) = -(D/2) G_{n,k}(-1)`.

The statement is total, including columns above the row and degree zero. -/
theorem gaussianBinomial_derivative_eval_neg_one_of_even_degree
    {R : Type*} [CommRing R] (n k : ℕ) (hdegree : Even (k * (n - k))) :
    (gaussianBinomial (Polynomial.X : Polynomial R) n k).derivative.eval (-1) =
      -((k * (n - k) / 2 : ℕ) : R) * gaussianBinomial (-1 : R) n k := by
  have hint :=
    gaussianBinomial_derivative_eval_neg_one_of_even_degree_int n k hdegree
  let φ : ℤ →+* R := Int.castRingHom R
  have hpoly :
      (gaussianPolynomialInt n k).map φ =
        gaussianBinomial (Polynomial.X : Polynomial R) n k := by
    simpa only [gaussianPolynomialInt, Polynomial.coe_mapRingHom,
      Polynomial.map_X] using
      map_gaussianBinomial (Polynomial.mapRingHom φ)
        (Polynomial.X : Polynomial ℤ) n k
  have hvalue :
      φ (gaussianBinomial (-1 : ℤ) n k) = gaussianBinomial (-1 : R) n k := by
    simpa using map_gaussianBinomial φ (-1 : ℤ) n k
  have hderiv :
      φ ((gaussianPolynomialInt n k).derivative.eval (-1)) =
        (gaussianBinomial (Polynomial.X : Polynomial R) n k).derivative.eval (-1) := by
    calc
      φ ((gaussianPolynomialInt n k).derivative.eval (-1)) =
          ((gaussianPolynomialInt n k).derivative.map φ).eval (φ (-1)) := by
        symm
        exact Polynomial.eval_map_apply
          (p := (gaussianPolynomialInt n k).derivative) (f := φ) (-1)
      _ = (gaussianBinomial (Polynomial.X : Polynomial R) n k).derivative.eval (-1) := by
        rw [← Polynomial.derivative_map, hpoly]
        simp
  calc
    (gaussianBinomial (Polynomial.X : Polynomial R) n k).derivative.eval (-1) =
        φ ((gaussianPolynomialInt n k).derivative.eval (-1)) := hderiv.symm
    _ = φ (-((k * (n - k) / 2 : ℕ) : ℤ) *
        gaussianBinomial (-1 : ℤ) n k) := congrArg φ hint
    _ = -((k * (n - k) / 2 : ℕ) : R) * gaussianBinomial (-1 : R) n k := by
      rw [map_mul, map_neg, map_natCast, hvalue]

private theorem gaussianBinomial_derivative_eval_neg_one_even_odd_int
    (a b : ℕ) :
    (gaussianPolynomialInt (2 * a) (2 * b + 1)).derivative.eval (-1) =
      ((a - b : ℕ) : ℤ) * (a.choose b : ℤ) := by
  by_cases hb : b < a
  · have hadj := gaussianBinomial_adjacent_mul
      (Polynomial.X : Polynomial ℤ) (2 * a) (2 * b)
    have hderiv := congrArg Polynomial.derivative hadj
    have heval := congrArg (Polynomial.eval (-1)) hderiv
    have hoddval :
        Polynomial.eval (-1)
            (gaussianBinomial (Polynomial.X : Polynomial ℤ)
              (2 * a) (2 * b + 1)) = 0 := by
      calc
        Polynomial.eval (-1)
            (gaussianBinomial (Polynomial.X : Polynomial ℤ)
              (2 * a) (2 * b + 1)) =
            gaussianBinomial (-1 : ℤ) (2 * a) (2 * b + 1) := by
          simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_X] using
            (map_gaussianBinomial (Polynomial.evalRingHom (-1))
              (Polynomial.X : Polynomial ℤ) (2 * a) (2 * b + 1))
        _ = 0 := gaussianBinomial_neg_one_even_odd_eq_zero a b
    have hevenval :
        Polynomial.eval (-1)
            (gaussianBinomial (Polynomial.X : Polynomial ℤ)
              (2 * a) (2 * b)) = (a.choose b : ℤ) := by
      calc
        Polynomial.eval (-1)
            (gaussianBinomial (Polynomial.X : Polynomial ℤ)
              (2 * a) (2 * b)) =
            gaussianBinomial (-1 : ℤ) (2 * a) (2 * b) := by
          simpa only [Polynomial.coe_evalRingHom, Polynomial.eval_X] using
            (map_gaussianBinomial (Polynomial.evalRingHom (-1))
              (Polynomial.X : Polynomial ℤ) (2 * a) (2 * b))
        _ = (a.choose b : ℤ) := gaussianBinomial_neg_one_even_even a b
    have hgap : 2 * a - 2 * b = 2 * (a - b) := by omega
    have hcol_odd : Odd (2 * b + 1) := ⟨b, by omega⟩
    have hgap_even : Even (2 * (a - b)) := ⟨a - b, by omega⟩
    have hgap_pred_odd : Odd (2 * (a - b) - 1) :=
      ⟨a - b - 1, by omega⟩
    simp [Polynomial.derivative_mul, Polynomial.derivative_X_pow,
      hoddval, hevenval, hgap, hcol_odd.neg_one_pow,
      hgap_even.neg_one_pow, hgap_pred_odd.neg_one_pow] at heval
    change
      (gaussianPolynomialInt (2 * a) (2 * b + 1)).derivative.eval (-1) =
        ((a - b : ℕ) : ℤ) * (a.choose b : ℤ)
    linarith
  · have hba : a ≤ b := Nat.le_of_not_gt hb
    have hlt : 2 * a < 2 * b + 1 := by omega
    simp [gaussianPolynomialInt,
      gaussianBinomial_eq_zero_of_lt (Polynomial.X : Polynomial ℤ) hlt,
      Nat.sub_eq_zero_of_le hba]

/-- **Exceptional even-row/odd-column first jet.**  Over every commutative
ring, including above the diagonal,

`G'_{2a,2b+1}(-1) = (a-b) * choose(a,b)`.

The truncated subtraction and binomial zero-extension make the formula total.
The proof differentiates the denominator-free adjacent-column identity. -/
theorem gaussianBinomial_derivative_eval_neg_one_even_odd
    {R : Type*} [CommRing R] (a b : ℕ) :
    (gaussianBinomial (Polynomial.X : Polynomial R)
        (2 * a) (2 * b + 1)).derivative.eval (-1) =
      ((a - b : ℕ) : R) * (a.choose b : R) := by
  have hint := gaussianBinomial_derivative_eval_neg_one_even_odd_int a b
  let φ : ℤ →+* R := Int.castRingHom R
  have hpoly :
      (gaussianPolynomialInt (2 * a) (2 * b + 1)).map φ =
        gaussianBinomial (Polynomial.X : Polynomial R)
          (2 * a) (2 * b + 1) := by
    simpa only [gaussianPolynomialInt, Polynomial.coe_mapRingHom,
      Polynomial.map_X] using
      map_gaussianBinomial (Polynomial.mapRingHom φ)
        (Polynomial.X : Polynomial ℤ) (2 * a) (2 * b + 1)
  have hderiv :
      φ ((gaussianPolynomialInt (2 * a) (2 * b + 1)).derivative.eval (-1)) =
        (gaussianBinomial (Polynomial.X : Polynomial R)
          (2 * a) (2 * b + 1)).derivative.eval (-1) := by
    calc
      φ ((gaussianPolynomialInt (2 * a) (2 * b + 1)).derivative.eval (-1)) =
          ((gaussianPolynomialInt (2 * a) (2 * b + 1)).derivative.map φ).eval
            (φ (-1)) := by
        symm
        exact Polynomial.eval_map_apply
          (p := (gaussianPolynomialInt (2 * a) (2 * b + 1)).derivative)
          (f := φ) (-1)
      _ = (gaussianBinomial (Polynomial.X : Polynomial R)
          (2 * a) (2 * b + 1)).derivative.eval (-1) := by
        rw [← Polynomial.derivative_map, hpoly]
        simp
  calc
    (gaussianBinomial (Polynomial.X : Polynomial R)
        (2 * a) (2 * b + 1)).derivative.eval (-1) =
        φ ((gaussianPolynomialInt (2 * a) (2 * b + 1)).derivative.eval (-1)) :=
      hderiv.symm
    _ = φ (((a - b : ℕ) : ℤ) * (a.choose b : ℤ)) := congrArg φ hint
    _ = ((a - b : ℕ) : R) * (a.choose b : R) := by
      rw [map_mul, map_natCast, map_natCast]

/-- For `b < a`, the exceptional even-row/odd-column Gaussian polynomial has
root multiplicity exactly one at `q = -1` over the integers. -/
theorem gaussianBinomial_even_odd_rootMultiplicity_int
    (a b : ℕ) (hb : b < a) :
    (gaussianBinomial (Polynomial.X : Polynomial ℤ)
      (2 * a) (2 * b + 1)).rootMultiplicity (-1) = 1 := by
  let p : Polynomial ℤ :=
    gaussianBinomial (Polynomial.X : Polynomial ℤ) (2 * a) (2 * b + 1)
  have hab_pos : 0 < a - b := Nat.sub_pos_of_lt hb
  have hchoose_pos : 0 < a.choose b := Nat.choose_pos (Nat.le_of_lt hb)
  have hfactor : ((a - b : ℕ) : ℤ) * (a.choose b : ℤ) ≠ 0 := by
    positivity
  have hderiv_eval :
      p.derivative.eval (-1) =
        ((a - b : ℕ) : ℤ) * (a.choose b : ℤ) := by
    simpa only [p, gaussianPolynomialInt] using
      gaussianBinomial_derivative_eval_neg_one_even_odd_int a b
  have hderiv_ne : p.derivative.eval (-1) ≠ 0 := by
    rw [hderiv_eval]
    exact hfactor
  have hp : p ≠ 0 := by
    intro hp
    rw [hp] at hderiv_ne
    simp at hderiv_ne
  have hroot : p.IsRoot (-1) := by
    rw [Polynomial.IsRoot]
    have heval :
        p.eval (-1) = gaussianBinomial (-1 : ℤ) (2 * a) (2 * b + 1) := by
      simpa only [p, Polynomial.coe_evalRingHom, Polynomial.eval_X] using
        (map_gaussianBinomial (Polynomial.evalRingHom (-1))
          (Polynomial.X : Polynomial ℤ) (2 * a) (2 * b + 1))
    rw [heval, gaussianBinomial_neg_one_even_odd_eq_zero]
  have hpos : 0 < p.rootMultiplicity (-1) :=
    (Polynomial.rootMultiplicity_pos hp).2 hroot
  have hnot : ¬ 1 < p.rootMultiplicity (-1) := by
    intro hlt
    have hroots :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).1 hlt
    exact hderiv_ne hroots.2.eq_zero
  change p.rootMultiplicity (-1) = 1
  omega

/-- Over every characteristic-zero commutative ring, the exceptional
even-row/odd-column Gaussian polynomial has a simple root at `q = -1` whenever
`b < a`. -/
theorem gaussianBinomial_even_odd_rootMultiplicity
    {K : Type*} [CommRing K] [CharZero K] (a b : ℕ) (hb : b < a) :
    (gaussianBinomial (Polynomial.X : Polynomial K)
      (2 * a) (2 * b + 1)).rootMultiplicity (-1) = 1 := by
  let φ : ℤ →+* K := Int.castRingHom K
  have hpoly :
      (gaussianPolynomialInt (2 * a) (2 * b + 1)).map φ =
        gaussianBinomial (Polynomial.X : Polynomial K)
          (2 * a) (2 * b + 1) := by
    simpa only [gaussianPolynomialInt, Polynomial.coe_mapRingHom,
      Polynomial.map_X] using
      map_gaussianBinomial (Polynomial.mapRingHom φ)
        (Polynomial.X : Polynomial ℤ) (2 * a) (2 * b + 1)
  have hmult := Polynomial.eq_rootMultiplicity_map
    (p := gaussianPolynomialInt (2 * a) (2 * b + 1))
    (f := φ) Int.cast_injective (-1)
  rw [hpoly] at hmult
  calc
    (gaussianBinomial (Polynomial.X : Polynomial K)
        (2 * a) (2 * b + 1)).rootMultiplicity (-1) =
        (gaussianPolynomialInt (2 * a) (2 * b + 1)).rootMultiplicity (-1) := by
      simpa using hmult.symm
    _ = 1 := gaussianBinomial_even_odd_rootMultiplicity_int a b hb

end Fabius
