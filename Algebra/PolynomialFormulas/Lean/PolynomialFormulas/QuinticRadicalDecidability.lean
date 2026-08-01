import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
import Mathlib.Data.Int.Interval
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.RingTheory.Localization.Rat
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Executable arithmetic toward deciding radical solvability of quintics

This file isolates the computable, coefficient-level part of the quintic
decision procedure.  An input is six integer coefficients.  We implement:

* the integral monicization `F(Y) = a₅⁴ f(Y / a₅)`;
* the bounded searches for monic linear and quadratic factors;
* the rational translation to a depressed quintic;
* the bounded rational-root search used after clearing denominators in a
  sextic resolvent;
* primitive-recursive coding and recognition of well-formed quintic inputs.

The finite factor search is proved complete for monic quintics, using Cauchy
bounds, Vieta's formulas, and Gauss's lemma.  The rational-root search is also
proved complete for integer sextics with nonzero leading coefficient.  The
remaining mathematical bridge is intentionally not postulated here: one still
has to define the particular Frobenius--Dummit sextic resolvent and prove that
its rational-root test is equivalent to solvability of an irreducible quintic
by radicals.  Consequently no theorem below claims semantic correctness of a
radical-solvability decision.
-/

open scoped BigOperators Polynomial

namespace LeanProofs.PolynomialFormulas.QuinticRadicalDecidability

open Polynomial

/-! ## Six-coefficient inputs -/

/-- Coefficients `a₀, ..., a₅` of an integer polynomial, stored in ascending
degree order.  The proposition `isQuintic` and Boolean `isQuinticB` express the
required condition `a₅ ≠ 0`. -/
abbrev IntegerQuintic := Fin 6 → ℤ

namespace IntegerQuintic

/-- Evaluation of the represented polynomial without passing through the
finitely-supported `Polynomial` representation. -/
def eval (f : IntegerQuintic) (x : ℤ) : ℤ :=
  ∑ i : Fin 6, f i * x ^ (i : ℕ)

/-- The corresponding mathlib polynomial.  This is a mathematical view of the
coefficient tuple; all algorithms below work directly with integers. -/
noncomputable def polynomial (f : IntegerQuintic) : ℤ[X] :=
  Polynomial.C (f 5) * X ^ 5 + Polynomial.C (f 4) * X ^ 4 +
    Polynomial.C (f 3) * X ^ 3 + Polynomial.C (f 2) * X ^ 2 +
    Polynomial.C (f 1) * X + Polynomial.C (f 0)

@[simp] theorem polynomial_eval (f : IntegerQuintic) (x : ℤ) :
    f.polynomial.eval x = f.eval x := by
  simp [polynomial, eval, Fin.sum_univ_succ]
  ring

/-- A six-coefficient input has exact degree five precisely when its last
coefficient is nonzero. -/
def isQuintic (f : IntegerQuintic) : Prop := f 5 ≠ 0

/-- Executable recognition of exact degree-five inputs. -/
def isQuinticB (f : IntegerQuintic) : Bool := !decide (f 5 = 0)

@[simp] theorem isQuinticB_eq_true (f : IntegerQuintic) :
    f.isQuinticB = true ↔ f.isQuintic := by
  simp [isQuinticB, isQuintic]

/-- The tuple really represents a degree-five polynomial whenever its final
coefficient passes the executable nonzero check. -/
theorem natDegree_eq_five (f : IntegerQuintic) (hf : f.isQuintic) :
    f.polynomial.natDegree = 5 := by
  apply Nat.le_antisymm
  · simp only [polynomial]
    compute_degree
  · apply le_natDegree_of_ne_zero
    have hcoeff : f.polynomial.coeff 5 = f 5 := by
      unfold polynomial
      simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
      norm_num
    rwa [hcoeff]

/-! The `Primcodable.finArrow` instance gives a concrete natural-number
encoding of the six coefficients.  These lemmas certify that coefficient
projection and input validation are genuinely primitive recursive, rather
than merely propositionally decidable by classical choice. -/

theorem coeff_primrec (i : Fin 6) : Primrec fun f : IntegerQuintic ↦ f i :=
  Primrec.fin_app.comp Primrec.id (Primrec.const i)

theorem isQuinticB_primrec : Primrec isQuinticB := by
  have hzero : PrimrecPred (fun f : IntegerQuintic ↦ f 5 = 0) :=
    Primrec.eq.comp (coeff_primrec 5) (Primrec.const 0)
  change Primrec fun f : IntegerQuintic ↦ !decide (f 5 = 0)
  exact hzero.not.decide.of_eq fun f ↦ by simp

theorem isQuinticB_computable : Computable isQuinticB :=
  isQuinticB_primrec.to_comp

/-- Encode a six-coefficient input as a natural number, using the encoding
carried by the primitive-recursive coding instance. -/
def code (f : IntegerQuintic) : ℕ :=
  @Encodable.encode IntegerQuintic Primcodable.toEncodable f

/-- Decode a natural number into a possible six-coefficient input. -/
def decode (n : ℕ) : Option IntegerQuintic :=
  @Encodable.decode IntegerQuintic Primcodable.toEncodable n

theorem code_primrec : Primrec code := by
  exact (Primrec.encode : Primrec
    (@Encodable.encode IntegerQuintic Primcodable.toEncodable)).of_eq fun _ ↦ rfl

theorem decode_primrec : Primrec decode := by
  exact (Primrec.decode : Primrec
    (@Encodable.decode IntegerQuintic Primcodable.toEncodable)).of_eq fun _ ↦ rfl

@[simp] theorem decode_code (f : IntegerQuintic) : decode (code f) = some f := by
  simp [decode, code]

/-- Malformed codes and inputs with zero leading coefficient are rejected. -/
def validCode (n : ℕ) : Bool :=
  match decode n with
  | some f => f.isQuinticB
  | none => false

theorem validCode_primrec : Primrec validCode := by
  have hsome : Primrec₂ (fun _ : ℕ ↦ fun f : IntegerQuintic ↦ f.isQuinticB) :=
    isQuinticB_primrec.comp Primrec.snd
  exact (Primrec.option_casesOn decode_primrec (Primrec.const false) hsome).of_eq fun n ↦ by
    simp only [validCode]
    cases decode n <;> rfl

theorem validCode_computable : Computable validCode :=
  validCode_primrec.to_comp

@[simp] theorem validCode_code (f : IntegerQuintic) :
    validCode (code f) = f.isQuinticB := by
  simp [validCode]

end IntegerQuintic

/-! ## Integral monicization -/

/-- Coefficients of the monic polynomial obtained, when `a₅ ≠ 0`, from
`f(X) = a₅X⁵ + ⋯ + a₀` by the change `F(Y) = a₅⁴ f(Y / a₅)`. -/
structure MonicQuintic where
  B : ℤ
  C : ℤ
  D : ℤ
  E : ℤ
  H : ℤ
  deriving DecidableEq, Repr

namespace MonicQuintic

/-- `Y⁵ + B Y⁴ + C Y³ + D Y² + E Y + H`. -/
def eval (f : MonicQuintic) (y : ℤ) : ℤ :=
  y ^ 5 + f.B * y ^ 4 + f.C * y ^ 3 + f.D * y ^ 2 + f.E * y + f.H

/-- Polynomial form of `MonicQuintic.eval`. -/
noncomputable def polynomial (f : MonicQuintic) : ℤ[X] :=
  X ^ 5 + Polynomial.C f.B * X ^ 4 + Polynomial.C f.C * X ^ 3 +
    Polynomial.C f.D * X ^ 2 + Polynomial.C f.E * X + Polynomial.C f.H

@[simp] theorem polynomial_eval (f : MonicQuintic) (y : ℤ) :
    f.polynomial.eval y = f.eval y := by
  simp [polynomial, eval]

theorem polynomial_monic (f : MonicQuintic) : f.polynomial.Monic := by
  simp only [polynomial]
  monicity!

@[simp] theorem polynomial_natDegree (f : MonicQuintic) : f.polynomial.natDegree = 5 := by
  simp only [polynomial]
  compute_degree!

/-- The coefficient height used by the Cauchy root bound. -/
def height (f : MonicQuintic) : ℕ :=
  max f.B.natAbs (max f.C.natAbs (max f.D.natAbs (max f.E.natAbs f.H.natAbs)))

theorem polynomial_coeff_natAbs_le_height (f : MonicQuintic) (i : ℕ) (hi : i < 5) :
    (f.polynomial.coeff i).natAbs ≤ f.height := by
  interval_cases i <;>
    simp only [polynomial, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] <;>
    norm_num <;> simp [height]

/-- `1 + height`, a strict integral Cauchy bound for the complex roots. -/
def rootBound (f : MonicQuintic) : ℕ := f.height + 1

/-- Rational evaluation, used for the depressing translation. -/
def evalRat (f : MonicQuintic) (y : ℚ) : ℚ :=
  y ^ 5 + f.B * y ^ 4 + f.C * y ^ 3 + f.D * y ^ 2 + f.E * y + f.H

/-- The monic quintic after embedding its integer coefficients into `ℂ`. -/
noncomputable def complexPolynomial (f : MonicQuintic) : ℂ[X] :=
  f.polynomial.map (Int.castRingHom ℂ)

theorem complexPolynomial_monic (f : MonicQuintic) : f.complexPolynomial.Monic :=
  f.polynomial_monic.map _

@[simp] theorem complexPolynomial_natDegree (f : MonicQuintic) :
    f.complexPolynomial.natDegree = 5 := by
  rw [complexPolynomial, f.polynomial_monic.natDegree_map, polynomial_natDegree]

theorem complexPolynomial_cauchyBound_le (f : MonicQuintic) :
    f.complexPolynomial.cauchyBound ≤ f.rootBound := by
  rw [Polynomial.cauchyBound, complexPolynomial_natDegree,
    f.complexPolynomial_monic.leadingCoeff]
  simp only [nnnorm_one, div_one, rootBound, Nat.cast_add, Nat.cast_one, add_le_add_iff_right]
  apply Finset.sup_le
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [complexPolynomial, coeff_map]
  change ‖((f.polynomial.coeff i : ℤ) : ℂ)‖₊ ≤ (f.height : NNReal)
  rw [Complex.nnnorm_intCast, ← NNReal.natCast_natAbs]
  exact_mod_cast f.polynomial_coeff_natAbs_le_height i hi

theorem complexRoot_nnnorm_lt_rootBound (f : MonicQuintic) {z : ℂ}
    (hz : f.complexPolynomial.IsRoot z) : ‖z‖₊ < f.rootBound :=
  (hz.norm_lt_cauchyBound f.complexPolynomial_monic.ne_zero).trans_le
    f.complexPolynomial_cauchyBound_le

end MonicQuintic

/-- Compute the integral monicization coefficients. -/
def monicize (f : IntegerQuintic) : MonicQuintic where
  B := f 4
  C := f 3 * f 5
  D := f 2 * f 5 ^ 2
  E := f 1 * f 5 ^ 3
  H := f 0 * f 5 ^ 4

/-- Denominator-free correctness of monicization:
`F(a₅ x) = a₅⁴ f(x)`. -/
theorem monicize_eval_scale (f : IntegerQuintic) (x : ℤ) :
    (monicize f).eval (f 5 * x) = f 5 ^ 4 * f.eval x := by
  simp [monicize, MonicQuintic.eval, IntegerQuintic.eval, Fin.sum_univ_succ]
  ring

/-! ## Bounded factor search -/

/-- The candidate monic linear factor `X + c`. -/
noncomputable def linearFactor (c : ℤ) : ℤ[X] := X + Polynomial.C c

/-- The candidate monic quadratic factor `X² + bX + c`. -/
noncomputable def quadraticFactor (b c : ℤ) : ℤ[X] :=
  X ^ 2 + (Polynomial.C b * X + Polynomial.C c)

theorem linearFactor_monic (c : ℤ) : (linearFactor c).Monic := by
  simpa [linearFactor] using monic_X_add_C c

theorem quadraticFactor_monic (b c : ℤ) : (quadraticFactor b c).Monic := by
  apply monic_X_pow_add
  calc
    degree (C b * X + C c : ℤ[X]) ≤ max (degree (C b * X : ℤ[X])) (degree (C c : ℤ[X])) :=
      degree_add_le _ _
    _ ≤ 1 := max_le (degree_C_mul_X_le b) (degree_C_le.trans (by norm_num))
    _ < 2 := by norm_num

/-- Symmetric integer interval of radius `r`. -/
def symmetricInterval (r : ℕ) : Finset ℤ :=
  Int.instLocallyFiniteOrder.finsetIcc (-(r : ℤ)) (r : ℤ)

@[simp] theorem mem_symmetricInterval {r : ℕ} {z : ℤ} :
    z ∈ symmetricInterval r ↔ -(r : ℤ) ≤ z ∧ z ≤ (r : ℤ) :=
  Int.instLocallyFiniteOrder.finset_mem_Icc _ _ _

namespace MonicQuintic

/-- The coefficient-level remainder test for the candidate factor `X + c`.
It is simply evaluation at the candidate root `-c`. -/
def linearRemainderZero (f : MonicQuintic) (c : ℤ) : Prop := f.eval (-c) = 0

instance (f : MonicQuintic) (c : ℤ) : Decidable (linearRemainderZero f c) :=
  inferInstanceAs (Decidable (f.eval (-c) = 0))

/-- Search every possible bounded monic linear factor, using only integer
arithmetic. -/
def hasBoundedLinearFactor (f : MonicQuintic) : Bool :=
  decide (∃ c ∈ symmetricInterval f.rootBound, linearRemainderZero f c)

/-- Cubic quotient coefficient obtained by exact division by
`X² + bX + c`, starting at degree four. -/
def quadraticQ2 (f : MonicQuintic) (b : ℤ) : ℤ := f.B - b

/-- Cubic quotient coefficient obtained next, at degree three. -/
def quadraticQ1 (f : MonicQuintic) (b c : ℤ) : ℤ :=
  f.C - c - b * f.quadraticQ2 b

/-- Constant coefficient of the candidate cubic quotient. -/
def quadraticQ0 (f : MonicQuintic) (b c : ℤ) : ℤ :=
  f.D - b * f.quadraticQ1 b c - c * f.quadraticQ2 b

/-- Both coefficients of the remainder after dividing by `X² + bX + c`
vanish.  The three quotient coefficients above are the synthetic-division
recurrence specialized to a monic quintic. -/
def quadraticRemainderZero (f : MonicQuintic) (b c : ℤ) : Prop :=
  f.E = b * f.quadraticQ0 b c + c * f.quadraticQ1 b c ∧
    f.H = c * f.quadraticQ0 b c

instance (f : MonicQuintic) (b c : ℤ) : Decidable (quadraticRemainderZero f b c) :=
  inferInstanceAs (Decidable
    (f.E = b * f.quadraticQ0 b c + c * f.quadraticQ1 b c ∧
      f.H = c * f.quadraticQ0 b c))

/-- The candidate cubic quotient determined by the three synthetic-division
steps.  It is used only in correctness proofs, not by the executable search. -/
noncomputable def quadraticQuotient (f : MonicQuintic) (b c : ℤ) : ℤ[X] :=
  X ^ 3 + Polynomial.C (f.quadraticQ2 b) * X ^ 2 +
    Polynomial.C (f.quadraticQ1 b c) * X + Polynomial.C (f.quadraticQ0 b c)

/-- The degree-less-than-two remainder determined by synthetic division. -/
noncomputable def quadraticRemainder (f : MonicQuintic) (b c : ℤ) : ℤ[X] :=
  Polynomial.C
      (f.E - b * f.quadraticQ0 b c - c * f.quadraticQ1 b c) * X +
    Polynomial.C (f.H - c * f.quadraticQ0 b c)

/-- The shared synthetic-division identity behind the quadratic search. -/
theorem quadratic_division_identity (f : MonicQuintic) (b c : ℤ) :
    f.polynomial = quadraticFactor b c * f.quadraticQuotient b c +
      f.quadraticRemainder b c := by
  simp [MonicQuintic.polynomial, quadraticFactor, quadraticQuotient, quadraticRemainder,
    quadraticQ2, quadraticQ1, quadraticQ0]
  ring

theorem quadraticRemainder_eq_zero_iff (f : MonicQuintic) (b c : ℤ) :
    f.quadraticRemainder b c = 0 ↔ f.quadraticRemainderZero b c := by
  constructor
  · intro h
    have h₁ := congrArg (fun p : ℤ[X] ↦ p.eval 1) h
    have h₀ := congrArg (fun p : ℤ[X] ↦ p.eval 0) h
    have hr₀ : f.H - c * f.quadraticQ0 b c = 0 := by
      simpa [quadraticRemainder] using h₀
    have hr₁ : f.E - b * f.quadraticQ0 b c - c * f.quadraticQ1 b c = 0 := by
      simp [quadraticRemainder] at h₁
      linarith
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hE, hH⟩
    simp [quadraticRemainder, hE, hH]

/-- Search every possible bounded monic quadratic factor.  If all roots have
absolute value at most `R`, Vieta bounds the candidates by `|b| ≤ 2R` and
`|c| ≤ R²`. -/
def hasBoundedQuadraticFactor (f : MonicQuintic) : Bool :=
  decide (∃ b ∈ symmetricInterval (2 * f.rootBound),
    ∃ c ∈ symmetricInterval (f.rootBound ^ 2), quadraticRemainderZero f b c)

/-- The executable bounded reducibility witness search. -/
def hasBoundedProperFactor (f : MonicQuintic) : Bool :=
  f.hasBoundedLinearFactor || f.hasBoundedQuadraticFactor

theorem hasBoundedLinearFactor_iff (f : MonicQuintic) :
    f.hasBoundedLinearFactor = true ↔
      ∃ c ∈ symmetricInterval f.rootBound, linearRemainderZero f c := by
  simp [hasBoundedLinearFactor]

theorem hasBoundedQuadraticFactor_iff (f : MonicQuintic) :
    f.hasBoundedQuadraticFactor = true ↔
      ∃ b ∈ symmetricInterval (2 * f.rootBound),
        ∃ c ∈ symmetricInterval (f.rootBound ^ 2), quadraticRemainderZero f b c := by
  simp [hasBoundedQuadraticFactor]

theorem hasBoundedProperFactor_iff (f : MonicQuintic) :
    f.hasBoundedProperFactor = true ↔
      (∃ c ∈ symmetricInterval f.rootBound, linearRemainderZero f c) ∨
      (∃ b ∈ symmetricInterval (2 * f.rootBound),
        ∃ c ∈ symmetricInterval (f.rootBound ^ 2), quadraticRemainderZero f b c) := by
  rw [hasBoundedProperFactor, Bool.or_eq_true, hasBoundedLinearFactor_iff,
    hasBoundedQuadraticFactor_iff]

/-- The linear integer remainder test is exactly divisibility by the candidate
linear factor. -/
theorem linearRemainderZero_iff_dvd (f : MonicQuintic) (c : ℤ) :
    linearRemainderZero f c ↔ linearFactor c ∣ f.polynomial := by
  rw [show linearFactor c = X - Polynomial.C (-c) by simp [linearFactor], dvd_iff_isRoot]
  simp [IsRoot, linearRemainderZero]

theorem linearRemainderZero_dvd (f : MonicQuintic) (c : ℤ)
    (h : linearRemainderZero f c) : linearFactor c ∣ f.polynomial :=
  (f.linearRemainderZero_iff_dvd c).mp h

theorem linearFactor_mem_symmetricInterval_of_dvd (f : MonicQuintic) (c : ℤ)
    (hdvd : linearFactor c ∣ f.polynomial) : c ∈ symmetricInterval f.rootBound := by
  have hrootZ : f.polynomial.IsRoot (-c) := by
    simpa [linearRemainderZero, IsRoot] using
      (f.linearRemainderZero_iff_dvd c).mpr hdvd
  have hrootC : f.complexPolynomial.IsRoot ((Int.castRingHom ℂ) (-c)) := by
    simpa [complexPolynomial] using hrootZ.map (f := Int.castRingHom ℂ)
  have hnorm := f.complexRoot_nnnorm_lt_rootBound hrootC
  have hnatAbs_lt : c.natAbs < f.rootBound := by
    have : (c.natAbs : NNReal) < (f.rootBound : NNReal) := by
      simpa [Complex.nnnorm_intCast, ← NNReal.natCast_natAbs] using hnorm
    exact_mod_cast this
  rw [mem_symmetricInterval]
  have hnatAbs : (c.natAbs : ℤ) ≤ (f.rootBound : ℤ) := by
    exact_mod_cast hnatAbs_lt.le
  rw [Int.natCast_natAbs] at hnatAbs
  constructor <;> omega

/-- The quadratic integer remainder test is exactly divisibility by the
candidate monic quadratic. -/
theorem quadraticRemainderZero_iff_dvd (f : MonicQuintic) (b c : ℤ) :
    f.quadraticRemainderZero b c ↔ quadraticFactor b c ∣ f.polynomial := by
  rw [← modByMonic_eq_zero_iff_dvd (quadraticFactor_monic b c)]
  have hdeg : degree (f.quadraticRemainder b c) < degree (quadraticFactor b c) := by
    have hfactor : degree (quadraticFactor b c) = 2 := by
      simp only [quadraticFactor]
      compute_degree!
    rw [hfactor]
    simp only [quadraticRemainder]
    compute_degree!
  rw [quadratic_division_identity, add_modByMonic,
    self_mul_modByMonic (quadraticFactor_monic b c), zero_add,
    (modByMonic_eq_self_iff (quadraticFactor_monic b c)).mpr hdeg,
    quadraticRemainder_eq_zero_iff]

theorem quadraticRemainderZero_dvd (f : MonicQuintic) (b c : ℤ)
    (h : quadraticRemainderZero f b c) : quadraticFactor b c ∣ f.polynomial :=
  (f.quadraticRemainderZero_iff_dvd b c).mp h

theorem quadraticFactor_mem_symmetricInterval_of_dvd (f : MonicQuintic) (b c : ℤ)
    (hdvd : quadraticFactor b c ∣ f.polynomial) :
    b ∈ symmetricInterval (2 * f.rootBound) ∧
      c ∈ symmetricInterval (f.rootBound ^ 2) := by
  let qZ : ℤ[X] := quadraticFactor b c
  let qC : ℂ[X] := qZ.map (Int.castRingHom ℂ)
  have hqZmonic : qZ.Monic := quadraticFactor_monic b c
  have hqCmonic : qC.Monic := hqZmonic.map _
  have hqZdeg : qZ.natDegree = 2 := by
    simp only [qZ, quadraticFactor]
    compute_degree!
  have hqCdeg : qC.natDegree = 2 := by
    simpa [qC] using (hqZmonic.natDegree_map (Int.castRingHom ℂ)).trans hqZdeg
  have hsplit : qC.Splits := IsAlgClosed.splits qC
  have hcard : qC.roots.card = 2 := by
    rw [← hsplit.natDegree_eq_card_roots, hqCdeg]
  obtain ⟨z, w, hroots⟩ := Multiset.card_eq_two.mp hcard
  have hdvdC : qC ∣ f.complexPolynomial := by
    simpa [qC, qZ, complexPolynomial] using Polynomial.map_dvd (Int.castRingHom ℂ) hdvd
  have hzq : qC.IsRoot z := by
    rw [← mem_roots hqCmonic.ne_zero]
    simp [hroots]
  have hwq : qC.IsRoot w := by
    rw [← mem_roots hqCmonic.ne_zero]
    simp [hroots]
  have hz := f.complexRoot_nnnorm_lt_rootBound (hzq.dvd hdvdC)
  have hw := f.complexRoot_nnnorm_lt_rootBound (hwq.dvd hdvdC)
  have hnextZ : qZ.nextCoeff = b := by
    rw [nextCoeff_of_natDegree_pos (hqZdeg ▸ by norm_num), hqZdeg]
    simp only [qZ, quadraticFactor, coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
    norm_num
  have hnext : qC.nextCoeff = (b : ℂ) := by
    calc
      qC.nextCoeff = (Int.castRingHom ℂ) qZ.nextCoeff := by
        change (qZ.map (Int.castRingHom ℂ)).nextCoeff = (Int.castRingHom ℂ) qZ.nextCoeff
        exact nextCoeff_map Int.cast_injective qZ
      _ = (b : ℂ) := by rw [hnextZ]; rfl
  have hcoeffZeroZ : qZ.coeff 0 = c := by
    simp only [qZ, quadraticFactor, coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
    norm_num
  have hbEq : (b : ℂ) = -(z + w) := by
    calc
      (b : ℂ) = qC.nextCoeff := hnext.symm
      _ = -qC.roots.sum := hsplit.nextCoeff_eq_neg_sum_roots_of_monic hqCmonic
      _ = -(z + w) := by simp [hroots]
  have hcEq : (c : ℂ) = z * w := by
    calc
      (c : ℂ) = qC.coeff 0 := by simp [qC, hcoeffZeroZ]
      _ = (-1) ^ qC.natDegree * qC.roots.prod :=
        hsplit.coeff_zero_eq_prod_roots_of_monic hqCmonic
      _ = z * w := by simp [hqCdeg, hroots]
  have hbNorm : ‖(b : ℂ)‖₊ < (2 * f.rootBound : ℕ) := by
    calc
      ‖(b : ℂ)‖₊ = ‖z + w‖₊ := by rw [hbEq, nnnorm_neg]
      _ ≤ ‖z‖₊ + ‖w‖₊ := nnnorm_add_le _ _
      _ < (f.rootBound : NNReal) + f.rootBound := add_lt_add hz hw
      _ = (2 * f.rootBound : ℕ) := by norm_num; ring
  have hcNorm : ‖(c : ℂ)‖₊ < (f.rootBound ^ 2 : ℕ) := by
    calc
      ‖(c : ℂ)‖₊ = ‖z‖₊ * ‖w‖₊ := by rw [hcEq, nnnorm_mul]
      _ < (f.rootBound : NNReal) * f.rootBound := by gcongr
      _ = (f.rootBound ^ 2 : ℕ) := by norm_num; ring
  have hbNat : b.natAbs ≤ 2 * f.rootBound := by
    have : (b.natAbs : NNReal) < (2 * f.rootBound : ℕ) := by
      simpa [Complex.nnnorm_intCast, ← NNReal.natCast_natAbs] using hbNorm
    exact (by exact_mod_cast this.le)
  have hcNat : c.natAbs ≤ f.rootBound ^ 2 := by
    have : (c.natAbs : NNReal) < (f.rootBound ^ 2 : ℕ) := by
      simpa [Complex.nnnorm_intCast, ← NNReal.natCast_natAbs] using hcNorm
    exact (by exact_mod_cast this.le)
  constructor
  · rw [mem_symmetricInterval]
    have hbZ : (b.natAbs : ℤ) ≤ (2 * f.rootBound : ℕ) := by exact_mod_cast hbNat
    rw [Int.natCast_natAbs] at hbZ
    constructor <;> omega
  · rw [mem_symmetricInterval]
    have hcZ : (c.natAbs : ℤ) ≤ (f.rootBound ^ 2 : ℕ) := by exact_mod_cast hcNat
    rw [Int.natCast_natAbs] at hcZ
    constructor <;> omega

theorem monic_natDegree_two_eq_quadraticFactor (q : ℤ[X]) (hq : q.Monic)
    (hdeg : q.natDegree = 2) : q = quadraticFactor (q.coeff 1) (q.coeff 0) := by
  have hlead : q.coeff 2 = 1 := by
    rw [← hdeg]
    exact hq.coeff_natDegree
  calc
    q = ∑ i ∈ Finset.range (q.natDegree + 1), Polynomial.C (q.coeff i) * X ^ i :=
      q.as_sum_range_C_mul_X_pow
    _ = quadraticFactor (q.coeff 1) (q.coeff 0) := by
      simp only [hdeg, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one,
        mul_one, zero_add, hlead, map_one, quadraticFactor]
      ring

theorem not_irreducible_iff_exists_small_monic_factor (f : MonicQuintic) :
    ¬Irreducible f.polynomial ↔
      ∃ q : ℤ[X], q.Monic ∧ (q.natDegree = 1 ∨ q.natDegree = 2) ∧ q ∣ f.polynomial := by
  have hp1 : f.polynomial ≠ 1 := by
    intro hp1
    have hdeg := congrArg Polynomial.natDegree hp1
    simp at hdeg
  constructor
  · intro hirr
    rw [f.polynomial_monic.irreducible_iff_lt_natDegree_lt hp1] at hirr
    push Not at hirr
    obtain ⟨q, hq, hdeg, hdvd⟩ := hirr
    refine ⟨q, hq, ?_, hdvd⟩
    simp only [polynomial_natDegree, Nat.reduceDiv, Finset.mem_Ioc] at hdeg
    omega
  · rintro ⟨q, hq, hdeg, hdvd⟩ hirr
    have hcriterion :=
      (f.polynomial_monic.irreducible_iff_lt_natDegree_lt hp1).mp hirr q hq
    apply hcriterion
    · simp only [polynomial_natDegree, Nat.reduceDiv, Finset.mem_Ioc]
      omega
    · exact hdvd

/-- Divisibility formulation of the bounded linear search. -/
theorem hasBoundedLinearFactor_iff_dvd (f : MonicQuintic) :
    f.hasBoundedLinearFactor = true ↔
      ∃ c ∈ symmetricInterval f.rootBound, linearFactor c ∣ f.polynomial := by
  rw [hasBoundedLinearFactor_iff]
  simp only [linearRemainderZero_iff_dvd]

/-- Divisibility formulation of the bounded quadratic search. -/
theorem hasBoundedQuadraticFactor_iff_dvd (f : MonicQuintic) :
    f.hasBoundedQuadraticFactor = true ↔
      ∃ b ∈ symmetricInterval (2 * f.rootBound),
        ∃ c ∈ symmetricInterval (f.rootBound ^ 2), quadraticFactor b c ∣ f.polynomial := by
  rw [hasBoundedQuadraticFactor_iff]
  simp only [quadraticRemainderZero_iff_dvd]

/-- The combined Boolean detects exactly the displayed bounded linear or
quadratic divisors. -/
theorem hasBoundedProperFactor_iff_dvd (f : MonicQuintic) :
    f.hasBoundedProperFactor = true ↔
      (∃ c ∈ symmetricInterval f.rootBound, linearFactor c ∣ f.polynomial) ∨
      (∃ b ∈ symmetricInterval (2 * f.rootBound),
        ∃ c ∈ symmetricInterval (f.rootBound ^ 2), quadraticFactor b c ∣ f.polynomial) := by
  rw [hasBoundedProperFactor, Bool.or_eq_true, hasBoundedLinearFactor_iff_dvd,
    hasBoundedQuadraticFactor_iff_dvd]

/-- For monic quintics over `ℤ`, the executable bounded search is complete:
it succeeds exactly when the polynomial is reducible. -/
theorem hasBoundedProperFactor_iff_not_irreducible (f : MonicQuintic) :
    f.hasBoundedProperFactor = true ↔ ¬Irreducible f.polynomial := by
  rw [hasBoundedProperFactor_iff_dvd, not_irreducible_iff_exists_small_monic_factor]
  constructor
  · rintro (⟨c, -, hdvd⟩ | ⟨b, -, c, -, hdvd⟩)
    · refine ⟨linearFactor c, linearFactor_monic c, Or.inl ?_, hdvd⟩
      simp only [linearFactor]
      compute_degree!
    · refine ⟨quadraticFactor b c, quadraticFactor_monic b c, Or.inr ?_, hdvd⟩
      simp only [quadraticFactor]
      compute_degree!
  · rintro ⟨q, hq, hdeg | hdeg, hdvd⟩
    · have hqeq : q = linearFactor (q.coeff 0) := by
        simpa [linearFactor] using hq.eq_X_add_C hdeg
      rw [hqeq] at hdvd
      exact Or.inl ⟨q.coeff 0, f.linearFactor_mem_symmetricInterval_of_dvd _ hdvd, hdvd⟩
    · have hqeq := monic_natDegree_two_eq_quadraticFactor q hq hdeg
      rw [hqeq] at hdvd
      have hbounds :=
        f.quadraticFactor_mem_symmetricInterval_of_dvd (q.coeff 1) (q.coeff 0) hdvd
      exact Or.inr ⟨q.coeff 1, hbounds.1, q.coeff 0, hbounds.2, hdvd⟩

/-- By Gauss's lemma, the same Boolean also detects reducibility after mapping
the monic integer quintic to `ℚ[X]`. -/
theorem hasBoundedProperFactor_iff_not_irreducible_map_rat (f : MonicQuintic) :
    f.hasBoundedProperFactor = true ↔
      ¬Irreducible (f.polynomial.map (algebraMap ℤ ℚ)) := by
  rw [f.hasBoundedProperFactor_iff_not_irreducible,
    f.polynomial_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)]

end MonicQuintic

/-! ## Depressing the monic quintic -/

/-- Coefficients of `Z⁵ + pZ³ + qZ² + rZ + s`. -/
structure DepressedQuintic where
  p : ℚ
  q : ℚ
  r : ℚ
  s : ℚ
  deriving DecidableEq, Repr

namespace DepressedQuintic

def eval (f : DepressedQuintic) (z : ℚ) : ℚ :=
  z ^ 5 + f.p * z ^ 3 + f.q * z ^ 2 + f.r * z + f.s

end DepressedQuintic

/-- Translate `Y = Z - B/5` and compute the four remaining coefficients. -/
def depress (f : MonicQuintic) : DepressedQuintic where
  p := f.C - 2 * f.B ^ 2 / 5
  q := f.D - 3 * f.B * f.C / 5 + 4 * f.B ^ 3 / 25
  r := f.E - 2 * f.B * f.D / 5 + 3 * f.B ^ 2 * f.C / 25 - 3 * f.B ^ 4 / 125
  s := f.H - f.B * f.E / 5 + f.B ^ 2 * f.D / 25 - f.B ^ 3 * f.C / 125 +
    4 * f.B ^ 5 / 3125

/-- Exact algebraic correctness of the depressing translation. -/
theorem depress_eval (f : MonicQuintic) (z : ℚ) :
    f.evalRat (z - f.B / 5) = (depress f).eval z := by
  simp [MonicQuintic.evalRat, depress, DepressedQuintic.eval]
  ring

/-! ## Generic bounded rational-root search for the sextic resolvent -/

/-- Seven integer coefficients `A₀, ..., A₆`, in ascending degree order.  The
type does not itself enforce the genuine-sextic condition `A₆ ≠ 0`. -/
abbrev IntegerSextic := Fin 7 → ℤ

namespace IntegerSextic

/-- The polynomial `A₆X⁶ + ⋯ + A₀` represented by the coefficient tuple. -/
noncomputable def polynomial (A : IntegerSextic) : ℤ[X] :=
  Polynomial.C (A 6) * X ^ 6 + Polynomial.C (A 5) * X ^ 5 +
    Polynomial.C (A 4) * X ^ 4 + Polynomial.C (A 3) * X ^ 3 +
    Polynomial.C (A 2) * X ^ 2 + Polynomial.C (A 1) * X + Polynomial.C (A 0)

/-- Evaluation of the represented polynomial in `ℚ`. -/
def evalRat (A : IntegerSextic) (x : ℚ) : ℚ :=
  ∑ i : Fin 7, A i * x ^ (i : ℕ)

@[simp] theorem polynomial_aeval (A : IntegerSextic) (x : ℚ) :
    aeval x A.polynomial = A.evalRat x := by
  simp [polynomial, evalRat, Fin.sum_univ_succ]
  ring

/-- A nonzero final coefficient makes the represented polynomial genuinely
degree six. -/
theorem polynomial_natDegree_eq_six (A : IntegerSextic) (hA : A 6 ≠ 0) :
    A.polynomial.natDegree = 6 := by
  apply Nat.le_antisymm
  · simp only [polynomial]
    compute_degree
  · apply le_natDegree_of_ne_zero
    simp only [polynomial, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    norm_num
    exact hA

@[simp] theorem polynomial_coeff_zero (A : IntegerSextic) :
    A.polynomial.coeff 0 = A 0 := by
  simp [polynomial]

theorem polynomial_leadingCoeff (A : IntegerSextic) (hA : A 6 ≠ 0) :
    A.polynomial.leadingCoeff = A 6 := by
  rw [leadingCoeff, A.polynomial_natDegree_eq_six hA]
  simp only [polynomial, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num

/-- The homogenized value `Σ Aᵢ uⁱ v⁶⁻ⁱ`.  For `v ≠ 0`, its vanishing is
equivalent to the associated sextic vanishing at `u/v`. -/
def homogeneousEval (A : IntegerSextic) (u v : ℤ) : ℤ :=
  ∑ i : Fin 7, A i * u ^ (i : ℕ) * v ^ (6 - (i : ℕ))

/-- Homogenization really is denominator clearing: at `v ≠ 0`, its rational
value is `v⁶` times evaluation at `u / v`. -/
theorem homogeneousEval_cast_eq (A : IntegerSextic) (u v : ℤ) (hv : v ≠ 0) :
    (A.homogeneousEval u v : ℚ) =
      (v : ℚ) ^ 6 * A.evalRat ((u : ℚ) / (v : ℚ)) := by
  simp [homogeneousEval, evalRat, Fin.sum_univ_succ]
  field_simp

/-- Numerators allowed by the rational-root theorem. -/
def numeratorCandidates (A : IntegerSextic) : Finset ℤ :=
  symmetricInterval (A 0).natAbs

/-- Positive denominator candidates supplied by the rational-root bound when
`A₆ ≠ 0`.  This set is empty when `A₆ = 0`. -/
def denominatorCandidates (A : IntegerSextic) : Finset ℤ :=
  Int.instLocallyFiniteOrder.finsetIcc 1 ((A 6).natAbs : ℤ)

@[simp] theorem mem_numeratorCandidates {A : IntegerSextic} {u : ℤ} :
    u ∈ A.numeratorCandidates ↔
      -((A 0).natAbs : ℤ) ≤ u ∧ u ≤ ((A 0).natAbs : ℤ) := by
  simp [numeratorCandidates]

@[simp] theorem mem_denominatorCandidates {A : IntegerSextic} {v : ℤ} :
    v ∈ A.denominatorCandidates ↔
      1 ≤ v ∧ v ≤ ((A 6).natAbs : ℤ) := by
  exact Int.instLocallyFiniteOrder.finset_mem_Icc _ _ _

/-- The bounded rational-root search.  A zero constant term immediately
records the rational root zero.  Otherwise all numerator/denominator pairs in
the displayed rectangle are tested by integer arithmetic.  Completeness as a
rational-root test requires the genuine-sextic condition `A₆ ≠ 0`. -/
def rationalRootSearch (A : IntegerSextic) : Bool :=
  if A 0 = 0 then true
  else
    decide (∃ u ∈ A.numeratorCandidates,
      ∃ v ∈ A.denominatorCandidates, A.homogeneousEval u v = 0)

/-- The exact finite proposition tested by `rationalRootSearch`. -/
def HasBoundedRationalRoot (A : IntegerSextic) : Prop :=
  A 0 = 0 ∨
    ∃ u ∈ A.numeratorCandidates,
      ∃ v ∈ A.denominatorCandidates, A.homogeneousEval u v = 0

/-- The represented integer polynomial has a root in `ℚ`.  The use of
`aeval` makes the coefficient embedding `ℤ → ℚ` explicit. -/
def HasRationalRoot (A : IntegerSextic) : Prop :=
  ∃ x : ℚ, aeval x A.polynomial = 0

/-- Every bounded integer witness gives a genuine rational root. -/
theorem hasRationalRoot_of_hasBoundedRationalRoot (A : IntegerSextic)
    (h : A.HasBoundedRationalRoot) : A.HasRationalRoot := by
  rcases h with hzero | ⟨u, hu, v, hv, heval⟩
  · refine ⟨0, ?_⟩
    rw [A.polynomial_aeval]
    simp [evalRat, Fin.sum_univ_succ, hzero]
  · have hvpos : 1 ≤ v := (mem_denominatorCandidates.mp hv).1
    have hvzero : v ≠ 0 := by omega
    refine ⟨(u : ℚ) / (v : ℚ), ?_⟩
    rw [A.polynomial_aeval]
    have hprod :
        (v : ℚ) ^ 6 * A.evalRat ((u : ℚ) / (v : ℚ)) = 0 := by
      rw [← A.homogeneousEval_cast_eq u v hvzero, heval]
      norm_num
    exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 6 (by exact_mod_cast hvzero))

/-- The rational-root theorem puts every rational root of a genuine sextic
inside the finite numerator/denominator rectangle. -/
theorem hasBoundedRationalRoot_of_hasRationalRoot (A : IntegerSextic)
    (hA : A 6 ≠ 0) (h : A.HasRationalRoot) : A.HasBoundedRationalRoot := by
  rcases h with ⟨x, hx⟩
  by_cases hzero : A 0 = 0
  · exact Or.inl hzero
  · right
    have hnumGeneric : IsFractionRing.num ℤ x ∣ A 0 := by
      simpa using num_dvd_of_is_root hx
    have hnum : x.num ∣ A 0 :=
      (x.isFractionRingNum.dvd_iff_dvd_left).mp hnumGeneric
    have hnumAbs : x.num.natAbs ≤ (A 0).natAbs :=
      Int.natAbs_le_of_dvd_ne_zero hnum hzero
    have hdenGeneric : (IsFractionRing.den ℤ x : ℤ) ∣ A 6 := by
      simpa [A.polynomial_leadingCoeff hA] using den_dvd_of_is_root hx
    have hdenAbsGeneric :
        (IsFractionRing.den ℤ x : ℤ).natAbs ≤ (A 6).natAbs :=
      Int.natAbs_le_of_dvd_ne_zero hdenGeneric hA
    have hdenAbs : x.den ≤ (A 6).natAbs := by
      rw [x.isFractionRingDen] at hdenAbsGeneric
      exact hdenAbsGeneric
    have hnumMem : x.num ∈ A.numeratorCandidates := by
      rw [mem_numeratorCandidates]
      have hnumZ : (x.num.natAbs : ℤ) ≤ ((A 0).natAbs : ℤ) := by
        exact_mod_cast hnumAbs
      rw [Int.natCast_natAbs] at hnumZ
      constructor <;> omega
    have hdenMem : (x.den : ℤ) ∈ A.denominatorCandidates := by
      rw [mem_denominatorCandidates]
      constructor
      · exact_mod_cast x.den_pos
      · exact_mod_cast hdenAbs
    refine ⟨x.num, hnumMem, (x.den : ℤ), hdenMem, ?_⟩
    have hdenZero : (x.den : ℤ) ≠ 0 := by exact_mod_cast x.den_ne_zero
    have hratio : (x.num : ℚ) / ((x.den : ℤ) : ℚ) = x := by
      simpa using x.num_div_den
    have hcast : (A.homogeneousEval x.num (x.den : ℤ) : ℚ) = 0 := by
      rw [A.homogeneousEval_cast_eq x.num (x.den : ℤ) hdenZero, hratio,
        ← A.polynomial_aeval, hx, mul_zero]
    exact_mod_cast hcast

theorem hasBoundedRationalRoot_iff_hasRationalRoot (A : IntegerSextic)
    (hA : A 6 ≠ 0) : A.HasBoundedRationalRoot ↔ A.HasRationalRoot :=
  ⟨A.hasRationalRoot_of_hasBoundedRationalRoot,
    A.hasBoundedRationalRoot_of_hasRationalRoot hA⟩

theorem rationalRootSearch_iff (A : IntegerSextic) :
    A.rationalRootSearch = true ↔ A.HasBoundedRationalRoot := by
  by_cases h : A 0 = 0
  · simp [rationalRootSearch, HasBoundedRationalRoot, h]
  · simp [rationalRootSearch, HasBoundedRationalRoot, h]

/-- For a genuine degree-six input, the executable bounded search succeeds
exactly when the represented polynomial has a rational root. -/
theorem rationalRootSearch_iff_hasRationalRoot (A : IntegerSextic)
    (hA : A 6 ≠ 0) : A.rationalRootSearch = true ↔ A.HasRationalRoot := by
  rw [A.rationalRootSearch_iff, A.hasBoundedRationalRoot_iff_hasRationalRoot hA]

end IntegerSextic

end LeanProofs.PolynomialFormulas.QuinticRadicalDecidability
