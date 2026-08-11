import PolynomialFormulas.LazardQuinticFourier

/-!
# Vieta completeness certificates for five displayed roots

This file isolates the formula-independent algebraic endgame needed for a
complete quintic solution.  Five scaled elementary-symmetric identities imply
the exact factorization of a general quintic into the five displayed linear
factors.  Consequently, when the leading coefficient is nonzero, every root
of the polynomial occurs in the displayed vector, including multiplicities.

The generic identities are packaged as a compact coefficient certificate,
not a stored factorization or a pointwise root assertion.  For Lazard's
concrete inverse-Fourier outputs, this file goes further: it derives all five
identities from the four `FourierRelations`, then transports them through the
Tschirnhaus translation.  Thus no independent Vieta certificate is required
by the solver.
-/

namespace LeanProofs.PolynomialFormulas.LazardQuintic

set_option autoImplicit false
set_option maxRecDepth 10000

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- First elementary symmetric expression in five indexed values. -/
def fiveESymm1 (r : Fin 5 → K) : K :=
  r 0 + r 1 + r 2 + r 3 + r 4

/-- Second elementary symmetric expression in five indexed values. -/
def fiveESymm2 (r : Fin 5 → K) : K :=
  r 0 * r 1 + r 0 * r 2 + r 0 * r 3 + r 0 * r 4 +
    r 1 * r 2 + r 1 * r 3 + r 1 * r 4 +
    r 2 * r 3 + r 2 * r 4 + r 3 * r 4

/-- Third elementary symmetric expression in five indexed values. -/
def fiveESymm3 (r : Fin 5 → K) : K :=
  r 0 * r 1 * r 2 + r 0 * r 1 * r 3 + r 0 * r 1 * r 4 +
    r 0 * r 2 * r 3 + r 0 * r 2 * r 4 + r 0 * r 3 * r 4 +
    r 1 * r 2 * r 3 + r 1 * r 2 * r 4 + r 1 * r 3 * r 4 +
    r 2 * r 3 * r 4

/-- Fourth elementary symmetric expression in five indexed values. -/
def fiveESymm4 (r : Fin 5 → K) : K :=
  r 0 * r 1 * r 2 * r 3 + r 0 * r 1 * r 2 * r 4 +
    r 0 * r 1 * r 3 * r 4 + r 0 * r 2 * r 3 * r 4 +
    r 1 * r 2 * r 3 * r 4

/-- Fifth elementary symmetric expression in five indexed values. -/
def fiveESymm5 (r : Fin 5 → K) : K :=
  r 0 * r 1 * r 2 * r 3 * r 4

/-- Vieta's five coefficient identities for a vector of candidate roots.

The identities are scaled by the leading coefficient, so the factorization
theorem does not divide by it. -/
structure FiveRootRelations (c : GeneralQuintic K) (r : Fin 5 → K) : Prop where
  coeff4 : c.b = -c.a * fiveESymm1 r
  coeff3 : c.c = c.a * fiveESymm2 r
  coeff2 : c.d = -c.a * fiveESymm3 r
  coeff1 : c.e = c.a * fiveESymm4 r
  coeff0 : c.f = -c.a * fiveESymm5 r

omit [CharZero K] in
/-- The five Vieta identities imply the exact factorization of the represented
quintic into the five displayed linear factors. -/
theorem FiveRootRelations.factorization {c : GeneralQuintic K}
    {r : Fin 5 → K} (h : FiveRootRelations c r) :
    c.polynomial = Polynomial.C c.a *
      ∏ k : Fin 5, (Polynomial.X - Polynomial.C (r k)) := by
  rw [Fin.prod_univ_five]
  unfold GeneralQuintic.polynomial
  rw [h.coeff4, h.coeff3, h.coeff2, h.coeff1, h.coeff0]
  simp only [map_neg, map_mul]
  simp only [fiveESymm1, fiveESymm2, fiveESymm3, fiveESymm4, fiveESymm5]
  simp only [map_add, map_mul]
  ring

omit [CharZero K] in
/-- Vieta relations are preserved by a field homomorphism. -/
theorem FiveRootRelations.map {L : Type*} [Field L]
    {c : GeneralQuintic K} {r : Fin 5 → K}
    (h : FiveRootRelations c r) (phi : K →+* L) :
    FiveRootRelations (c.map phi) (fun k => phi (r k)) := by
  constructor
  · simpa [GeneralQuintic.map, fiveESymm1] using congrArg phi h.coeff4
  · simpa [GeneralQuintic.map, fiveESymm2] using congrArg phi h.coeff3
  · simpa [GeneralQuintic.map, fiveESymm3] using congrArg phi h.coeff2
  · simpa [GeneralQuintic.map, fiveESymm4] using congrArg phi h.coeff1
  · simpa [GeneralQuintic.map, fiveESymm5] using congrArg phi h.coeff0

omit [CharZero K] in
/-- Pointwise form of the exact Vieta factorization. -/
theorem FiveRootRelations.eval_factorization {c : GeneralQuintic K}
    {r : Fin 5 → K} (h : FiveRootRelations c r) (x : K) :
    c.eval x = c.a * ∏ k : Fin 5, (x - r k) := by
  have heval := congrArg (fun p : Polynomial K => p.eval x) h.factorization
  simpa only [GeneralQuintic.polynomial_eval, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X] using heval

omit [CharZero K] in
/-- For a nondegenerate quintic, exact Vieta factorization proves that the
five displayed values exhaust all roots. -/
theorem FiveRootRelations.exists_eq_of_eval_eq_zero
    {c : GeneralQuintic K} {r : Fin 5 → K}
    (h : FiveRootRelations c r) (ha : c.a ≠ 0) {x : K}
    (hx : c.eval x = 0) : ∃ k : Fin 5, x = r k := by
  have heval := h.eval_factorization x
  rw [hx] at heval
  have hprod : ∏ k : Fin 5, (x - r k) = 0 :=
    (mul_eq_zero.mp heval.symm).resolve_left ha
  rw [Fin.prod_univ_five] at hprod
  rcases mul_eq_zero.mp hprod with h0123 | h4
  · rcases mul_eq_zero.mp h0123 with h012 | h3
    · rcases mul_eq_zero.mp h012 with h01 | h2
      · rcases mul_eq_zero.mp h01 with h0 | h1
        · exact ⟨0, sub_eq_zero.mp h0⟩
        · exact ⟨1, sub_eq_zero.mp h1⟩
      · exact ⟨2, sub_eq_zero.mp h2⟩
    · exact ⟨3, sub_eq_zero.mp h3⟩
  · exact ⟨4, sub_eq_zero.mp h4⟩

/-- Depressed-quintic Vieta identities, with the missing quartic coefficient
made explicit as a zero sum. -/
structure DepressedFiveRootRelations (c : DepressedQuintic K)
    (r : Fin 5 → K) : Prop where
  sum : fiveESymm1 r = 0
  pairs : fiveESymm2 r = c.p
  triples : fiveESymm3 r = -c.q
  quadruples : fiveESymm4 r = c.r
  product : fiveESymm5 r = -c.s

omit [CharZero K] in
/-- The depressed identities induce the general scaled Vieta certificate. -/
theorem DepressedFiveRootRelations.toFiveRootRelations
    {c : DepressedQuintic K} {r : Fin 5 → K}
    (h : DepressedFiveRootRelations c r) :
    FiveRootRelations
      { a := 1, b := 0, c := c.p, d := c.q, e := c.r, f := c.s } r := by
  constructor
  · rw [h.sum]
    ring
  · rw [h.pairs]
    ring
  · rw [h.triples]
    ring
  · rw [h.quadruples]
    ring
  · rw [h.product]
    ring

omit [CharZero K] in
/-- Pointwise form of the depressed factorization. -/
theorem DepressedFiveRootRelations.eval_factorization
    {c : DepressedQuintic K} {r : Fin 5 → K}
    (h : DepressedFiveRootRelations c r) (x : K) :
    c.eval x = ∏ k : Fin 5, (x - r k) := by
  rw [Fin.prod_univ_five]
  unfold DepressedQuintic.eval
  have hq : c.q = -fiveESymm3 r := by
    linear_combination h.triples
  have hs : c.s = -fiveESymm5 r := by
    linear_combination h.product
  rw [← h.pairs, hq, ← h.quadruples, hs]
  have hsum := h.sum
  simp only [fiveESymm1, fiveESymm2, fiveESymm3, fiveESymm4,
    fiveESymm5] at hsum ⊢
  linear_combination (x ^ 4) * hsum

omit [CharZero K] in
/-- Every entry of an exact depressed Vieta tuple is a root. -/
theorem DepressedFiveRootRelations.eval_root
    {c : DepressedQuintic K} {r : Fin 5 → K}
    (h : DepressedFiveRootRelations c r) (k : Fin 5) :
    c.eval (r k) = 0 := by
  rw [h.eval_factorization]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)

omit [CharZero K] in
/-- Exact depressed Vieta data exhausts the root set.  This is the reusable
set-level consequence of the stronger multiplicity-sensitive
factorization theorem. -/
theorem DepressedFiveRootRelations.exists_eq_of_eval_eq_zero
    {c : DepressedQuintic K} {r : Fin 5 → K}
    (h : DepressedFiveRootRelations c r) {x : K}
    (hx : c.eval x = 0) : ∃ k : Fin 5, x = r k := by
  let general : GeneralQuintic K :=
    { a := 1, b := 0, c := c.p, d := c.q, e := c.r, f := c.s }
  have hx' : general.eval x = 0 := by
    simpa [general, GeneralQuintic.eval, DepressedQuintic.eval] using hx
  exact h.toFiveRootRelations.exists_eq_of_eval_eq_zero one_ne_zero hx'

omit [CharZero K] in
/-- Root-set form of an exact depressed Vieta certificate. -/
theorem DepressedFiveRootRelations.eval_eq_zero_iff
    {c : DepressedQuintic K} {r : Fin 5 → K}
    (h : DepressedFiveRootRelations c r) (x : K) :
    c.eval x = 0 ↔ ∃ k : Fin 5, x = r k := by
  constructor
  · exact h.exists_eq_of_eval_eq_zero
  · rintro ⟨k, rfl⟩
    exact h.eval_root k

/-! ## Vieta identities for inverse Fourier reconstruction -/

omit [CharZero K] in
/-- Powers of a primitive fifth root may be reduced modulo five. -/
theorem FifthRootOfUnity.pow_eq_pow_mod_five
    (omega : FifthRootOfUnity K) (n : ℕ) :
    omega.value ^ n = omega.value ^ (n % 5) := by
  simpa [← omega.primitive.eq_orderOf] using
    (pow_mod_orderOf omega.value n).symm

omit [CharZero K] in
/-- The fourth power of a primitive fifth root, solved from its geometric
sum.  This is the final reduction used by the symbolic Vieta calculations. -/
theorem FifthRootOfUnity.pow_four_eq_neg
    (omega : FifthRootOfUnity K) :
    omega.value ^ 4 =
      -(1 + omega.value + omega.value ^ 2 + omega.value ^ 3) := by
  have h := omega.primitive.geom_sum_eq_zero (by norm_num : 1 < 5)
  norm_num [Finset.sum_range_succ] at h
  linear_combination h

/-- The five inverse Fourier outputs have zero sum. -/
theorem inverseFourier_esymm1
    (omega : FifthRootOfUnity K) (a b c d : K) :
    fiveESymm1 (fun k => inverseFourier omega.value a b c d k) = 0 := by
  have h1 := (omega.primitive.pow_of_coprime 1 (by decide)).geom_sum_eq_zero
    (by norm_num : 1 < 5)
  have h2 := (omega.primitive.pow_of_coprime 2 (by decide)).geom_sum_eq_zero
    (by norm_num : 1 < 5)
  have h3 := (omega.primitive.pow_of_coprime 3 (by decide)).geom_sum_eq_zero
    (by norm_num : 1 < 5)
  have h4 := (omega.primitive.pow_of_coprime 4 (by decide)).geom_sum_eq_zero
    (by norm_num : 1 < 5)
  norm_num [Finset.sum_range_succ, pow_mul] at h1 h2 h3 h4
  norm_num [fiveESymm1, inverseFourier]
  field_simp
  linear_combination a * h1 + b * h2 + c * h3 + d * h4

set_option linter.unusedSimpArgs false in
/-- The second elementary symmetric expression of the inverse Fourier
outputs is Lazard's cyclic quadratic expression. -/
theorem inverseFourier_esymm2
    (omega : FifthRootOfUnity K) (a b c d : K) :
    fiveESymm2 (fun k => inverseFourier omega.value a b c d k) =
      -fourierCyclic2 a b c d / 5 := by
  have hw4 := omega.pow_four_eq_neg
  norm_num [fiveESymm2, inverseFourier, fourierCyclic2]
  field_simp
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 32,
    omega.pow_eq_pow_mod_five 31, omega.pow_eq_pow_mod_five 30,
    omega.pow_eq_pow_mod_five 29, omega.pow_eq_pow_mod_five 28,
    omega.pow_eq_pow_mod_five 27, omega.pow_eq_pow_mod_five 26,
    omega.pow_eq_pow_mod_five 25, omega.pow_eq_pow_mod_five 24,
    omega.pow_eq_pow_mod_five 23, omega.pow_eq_pow_mod_five 22,
    omega.pow_eq_pow_mod_five 21, omega.pow_eq_pow_mod_five 20,
    omega.pow_eq_pow_mod_five 19, omega.pow_eq_pow_mod_five 18,
    omega.pow_eq_pow_mod_five 17, omega.pow_eq_pow_mod_five 16,
    omega.pow_eq_pow_mod_five 15, omega.pow_eq_pow_mod_five 14,
    omega.pow_eq_pow_mod_five 13, omega.pow_eq_pow_mod_five 12,
    omega.pow_eq_pow_mod_five 11, omega.pow_eq_pow_mod_five 10,
    omega.pow_eq_pow_mod_five 9, omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 7, omega.pow_eq_pow_mod_five 6,
    omega.pow_eq_pow_mod_five 5]
  norm_num
  rw [hw4]
  ring

set_option linter.unusedSimpArgs false in
/-- The third elementary symmetric expression of the inverse Fourier
outputs is Lazard's cyclic cubic expression. -/
theorem inverseFourier_esymm3
    (omega : FifthRootOfUnity K) (a b c d : K) :
    fiveESymm3 (fun k => inverseFourier omega.value a b c d k) =
      fourierCyclic3 a b c d / 25 := by
  have hw4 := omega.pow_four_eq_neg
  norm_num [fiveESymm3, inverseFourier, fourierCyclic3]
  field_simp
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 48,
    omega.pow_eq_pow_mod_five 47, omega.pow_eq_pow_mod_five 46,
    omega.pow_eq_pow_mod_five 45, omega.pow_eq_pow_mod_five 44,
    omega.pow_eq_pow_mod_five 43, omega.pow_eq_pow_mod_five 42,
    omega.pow_eq_pow_mod_five 41, omega.pow_eq_pow_mod_five 40,
    omega.pow_eq_pow_mod_five 39, omega.pow_eq_pow_mod_five 38,
    omega.pow_eq_pow_mod_five 37, omega.pow_eq_pow_mod_five 36,
    omega.pow_eq_pow_mod_five 35, omega.pow_eq_pow_mod_five 34,
    omega.pow_eq_pow_mod_five 33, omega.pow_eq_pow_mod_five 32,
    omega.pow_eq_pow_mod_five 31, omega.pow_eq_pow_mod_five 30,
    omega.pow_eq_pow_mod_five 29, omega.pow_eq_pow_mod_five 28,
    omega.pow_eq_pow_mod_five 27, omega.pow_eq_pow_mod_five 26,
    omega.pow_eq_pow_mod_five 25, omega.pow_eq_pow_mod_five 24,
    omega.pow_eq_pow_mod_five 23, omega.pow_eq_pow_mod_five 22,
    omega.pow_eq_pow_mod_five 21, omega.pow_eq_pow_mod_five 20,
    omega.pow_eq_pow_mod_five 19, omega.pow_eq_pow_mod_five 18,
    omega.pow_eq_pow_mod_five 17, omega.pow_eq_pow_mod_five 16,
    omega.pow_eq_pow_mod_five 15, omega.pow_eq_pow_mod_five 14,
    omega.pow_eq_pow_mod_five 13, omega.pow_eq_pow_mod_five 12,
    omega.pow_eq_pow_mod_five 11, omega.pow_eq_pow_mod_five 10,
    omega.pow_eq_pow_mod_five 9, omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 7, omega.pow_eq_pow_mod_five 6,
    omega.pow_eq_pow_mod_five 5]
  norm_num
  rw [hw4]
  ring

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- The fourth elementary symmetric expression of the inverse Fourier
outputs is Lazard's cyclic quartic expression. -/
theorem inverseFourier_esymm4
    (omega : FifthRootOfUnity K) (a b c d : K) :
    fiveESymm4 (fun k => inverseFourier omega.value a b c d k) =
      fourierCyclic4 a b c d / 125 := by
  have hw4 := omega.pow_four_eq_neg
  norm_num [fiveESymm4, inverseFourier, fourierCyclic4]
  field_simp
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 64,
    omega.pow_eq_pow_mod_five 63, omega.pow_eq_pow_mod_five 62,
    omega.pow_eq_pow_mod_five 61, omega.pow_eq_pow_mod_five 60,
    omega.pow_eq_pow_mod_five 59, omega.pow_eq_pow_mod_five 58,
    omega.pow_eq_pow_mod_five 57, omega.pow_eq_pow_mod_five 56,
    omega.pow_eq_pow_mod_five 55, omega.pow_eq_pow_mod_five 54,
    omega.pow_eq_pow_mod_five 53, omega.pow_eq_pow_mod_five 52,
    omega.pow_eq_pow_mod_five 51, omega.pow_eq_pow_mod_five 50,
    omega.pow_eq_pow_mod_five 49, omega.pow_eq_pow_mod_five 48,
    omega.pow_eq_pow_mod_five 47, omega.pow_eq_pow_mod_five 46,
    omega.pow_eq_pow_mod_five 45, omega.pow_eq_pow_mod_five 44,
    omega.pow_eq_pow_mod_five 43, omega.pow_eq_pow_mod_five 42,
    omega.pow_eq_pow_mod_five 41, omega.pow_eq_pow_mod_five 40,
    omega.pow_eq_pow_mod_five 39, omega.pow_eq_pow_mod_five 38,
    omega.pow_eq_pow_mod_five 37, omega.pow_eq_pow_mod_five 36,
    omega.pow_eq_pow_mod_five 35, omega.pow_eq_pow_mod_five 34,
    omega.pow_eq_pow_mod_five 33, omega.pow_eq_pow_mod_five 32,
    omega.pow_eq_pow_mod_five 31, omega.pow_eq_pow_mod_five 30,
    omega.pow_eq_pow_mod_five 29, omega.pow_eq_pow_mod_five 28,
    omega.pow_eq_pow_mod_five 27, omega.pow_eq_pow_mod_five 26,
    omega.pow_eq_pow_mod_five 25, omega.pow_eq_pow_mod_five 24,
    omega.pow_eq_pow_mod_five 23, omega.pow_eq_pow_mod_five 22,
    omega.pow_eq_pow_mod_five 21, omega.pow_eq_pow_mod_five 20,
    omega.pow_eq_pow_mod_five 19, omega.pow_eq_pow_mod_five 18,
    omega.pow_eq_pow_mod_five 17, omega.pow_eq_pow_mod_five 16,
    omega.pow_eq_pow_mod_five 15, omega.pow_eq_pow_mod_five 14,
    omega.pow_eq_pow_mod_five 13, omega.pow_eq_pow_mod_five 12,
    omega.pow_eq_pow_mod_five 11, omega.pow_eq_pow_mod_five 10,
    omega.pow_eq_pow_mod_five 9, omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 7, omega.pow_eq_pow_mod_five 6,
    omega.pow_eq_pow_mod_five 5]
  norm_num
  rw [hw4]
  ring

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
/-- The fifth elementary symmetric expression of the inverse Fourier
outputs is Lazard's cyclic quintic expression. -/
theorem inverseFourier_esymm5
    (omega : FifthRootOfUnity K) (a b c d : K) :
    fiveESymm5 (fun k => inverseFourier omega.value a b c d k) =
      fourierCyclic5 a b c d / 3125 := by
  have hw4 := omega.pow_four_eq_neg
  norm_num [fiveESymm5, inverseFourier, fourierCyclic5]
  field_simp
  ring_nf
  simp only [omega.pow_eq_pow_mod_five 80,
    omega.pow_eq_pow_mod_five 79, omega.pow_eq_pow_mod_five 78,
    omega.pow_eq_pow_mod_five 77, omega.pow_eq_pow_mod_five 76,
    omega.pow_eq_pow_mod_five 75, omega.pow_eq_pow_mod_five 74,
    omega.pow_eq_pow_mod_five 73, omega.pow_eq_pow_mod_five 72,
    omega.pow_eq_pow_mod_five 71, omega.pow_eq_pow_mod_five 70,
    omega.pow_eq_pow_mod_five 69, omega.pow_eq_pow_mod_five 68,
    omega.pow_eq_pow_mod_five 67, omega.pow_eq_pow_mod_five 66,
    omega.pow_eq_pow_mod_five 65, omega.pow_eq_pow_mod_five 64,
    omega.pow_eq_pow_mod_five 63, omega.pow_eq_pow_mod_five 62,
    omega.pow_eq_pow_mod_five 61, omega.pow_eq_pow_mod_five 60,
    omega.pow_eq_pow_mod_five 59, omega.pow_eq_pow_mod_five 58,
    omega.pow_eq_pow_mod_five 57, omega.pow_eq_pow_mod_five 56,
    omega.pow_eq_pow_mod_five 55, omega.pow_eq_pow_mod_five 54,
    omega.pow_eq_pow_mod_five 53, omega.pow_eq_pow_mod_five 52,
    omega.pow_eq_pow_mod_five 51, omega.pow_eq_pow_mod_five 50,
    omega.pow_eq_pow_mod_five 49, omega.pow_eq_pow_mod_five 48,
    omega.pow_eq_pow_mod_five 47, omega.pow_eq_pow_mod_five 46,
    omega.pow_eq_pow_mod_five 45, omega.pow_eq_pow_mod_five 44,
    omega.pow_eq_pow_mod_five 43, omega.pow_eq_pow_mod_five 42,
    omega.pow_eq_pow_mod_five 41, omega.pow_eq_pow_mod_five 40,
    omega.pow_eq_pow_mod_five 39, omega.pow_eq_pow_mod_five 38,
    omega.pow_eq_pow_mod_five 37, omega.pow_eq_pow_mod_five 36,
    omega.pow_eq_pow_mod_five 35, omega.pow_eq_pow_mod_five 34,
    omega.pow_eq_pow_mod_five 33, omega.pow_eq_pow_mod_five 32,
    omega.pow_eq_pow_mod_five 31, omega.pow_eq_pow_mod_five 30,
    omega.pow_eq_pow_mod_five 29, omega.pow_eq_pow_mod_five 28,
    omega.pow_eq_pow_mod_five 27, omega.pow_eq_pow_mod_five 26,
    omega.pow_eq_pow_mod_five 25, omega.pow_eq_pow_mod_five 24,
    omega.pow_eq_pow_mod_five 23, omega.pow_eq_pow_mod_five 22,
    omega.pow_eq_pow_mod_five 21, omega.pow_eq_pow_mod_five 20,
    omega.pow_eq_pow_mod_five 19, omega.pow_eq_pow_mod_five 18,
    omega.pow_eq_pow_mod_five 17, omega.pow_eq_pow_mod_five 16,
    omega.pow_eq_pow_mod_five 15, omega.pow_eq_pow_mod_five 14,
    omega.pow_eq_pow_mod_five 13, omega.pow_eq_pow_mod_five 12,
    omega.pow_eq_pow_mod_five 11, omega.pow_eq_pow_mod_five 10,
    omega.pow_eq_pow_mod_five 9, omega.pow_eq_pow_mod_five 8,
    omega.pow_eq_pow_mod_five 7, omega.pow_eq_pow_mod_five 6,
    omega.pow_eq_pow_mod_five 5]
  norm_num
  rw [hw4]
  ring

/-- The four Fourier relations already imply all five depressed Vieta
relations.  In particular, a separate Vieta certificate is unnecessary. -/
theorem FourierRelations.depressedFiveRootRelations
    {c : DepressedQuintic K} {a b c' d : K}
    (h : FourierRelations c a b c' d)
    (omega : FifthRootOfUnity K) :
    DepressedFiveRootRelations c
      (fun k => inverseFourier omega.value a b c' d k) := by
  constructor
  · exact inverseFourier_esymm1 omega a b c' d
  · rw [inverseFourier_esymm2, h.cyclic2]
    ring
  · rw [inverseFourier_esymm3, h.cyclic3]
    ring
  · rw [inverseFourier_esymm4, h.cyclic4]
    ring
  · rw [inverseFourier_esymm5, h.cyclic5]
    ring

/-! ## Tschirnhaus translation of the Vieta identities -/

omit [CharZero K] in
theorem fiveESymm1_sub_const (r : Fin 5 → K) (t : K) :
    fiveESymm1 (fun k => r k - t) = fiveESymm1 r - 5 * t := by
  simp only [fiveESymm1]
  ring

omit [CharZero K] in
theorem fiveESymm2_sub_const (r : Fin 5 → K) (t : K) :
    fiveESymm2 (fun k => r k - t) =
      fiveESymm2 r - 4 * t * fiveESymm1 r + 10 * t ^ 2 := by
  simp only [fiveESymm1, fiveESymm2]
  ring

omit [CharZero K] in
theorem fiveESymm3_sub_const (r : Fin 5 → K) (t : K) :
    fiveESymm3 (fun k => r k - t) =
      fiveESymm3 r - 3 * t * fiveESymm2 r +
        6 * t ^ 2 * fiveESymm1 r - 10 * t ^ 3 := by
  simp only [fiveESymm1, fiveESymm2, fiveESymm3]
  ring

omit [CharZero K] in
theorem fiveESymm4_sub_const (r : Fin 5 → K) (t : K) :
    fiveESymm4 (fun k => r k - t) =
      fiveESymm4 r - 2 * t * fiveESymm3 r +
        3 * t ^ 2 * fiveESymm2 r - 4 * t ^ 3 * fiveESymm1 r +
          5 * t ^ 4 := by
  simp only [fiveESymm1, fiveESymm2, fiveESymm3, fiveESymm4]
  ring

omit [CharZero K] in
theorem fiveESymm5_sub_const (r : Fin 5 → K) (t : K) :
    fiveESymm5 (fun k => r k - t) =
      fiveESymm5 r - t * fiveESymm4 r + t ^ 2 * fiveESymm3 r -
        t ^ 3 * fiveESymm2 r + t ^ 4 * fiveESymm1 r - t ^ 5 := by
  simp only [fiveESymm1, fiveESymm2, fiveESymm3, fiveESymm4, fiveESymm5]
  ring

/-- Translating depressed roots by `b/(5a)` yields the Vieta relations for
the original general quintic. -/
theorem DepressedFiveRootRelations.translate
    (c : GeneralQuintic K) (ha : c.a ≠ 0) {r : Fin 5 → K}
    (h : DepressedFiveRootRelations (depress c) r) :
    FiveRootRelations c (fun k => r k - c.b / (5 * c.a)) := by
  constructor
  · rw [fiveESymm1_sub_const, h.sum]
    field_simp [ha]
    ring
  · rw [fiveESymm2_sub_const, h.sum, h.pairs]
    simp only [depress]
    field_simp [ha]
    ring
  · rw [fiveESymm3_sub_const, h.sum, h.pairs, h.triples]
    simp only [depress]
    field_simp [ha]
    ring
  · rw [fiveESymm4_sub_const, h.sum, h.pairs, h.triples, h.quadruples]
    simp only [depress]
    field_simp [ha]
    ring
  · rw [fiveESymm5_sub_const, h.sum, h.pairs, h.triples,
      h.quadruples, h.product]
    simp only [depress]
    field_simp [ha]
    ring

/-- The four Fourier identities imply all five Vieta identities for the
concrete outputs of `solveGeneral`. -/
theorem solveGeneral_fiveRootRelations [DecidableEq K]
    (c : GeneralQuintic K) (ha : c.a ≠ 0) (i : Invariants K)
    (d : RadicalCertificate (depress c) i) (omega : FifthRootOfUnity K)
    (h : FourierRelations (depress c) d.p1
      (fourierP2 (depress c) i d.chosen d.p1)
      (fourierP3 (depress c) i d.chosen d.p1)
      (fourierP4 (depress c) i d.chosen d.p1)) :
    FiveRootRelations c (solveGeneral c i d omega) := by
  have hdep := h.depressedFiveRootRelations omega
  have htranslated := hdep.translate c ha
  change FiveRootRelations c (fun k =>
    solveDepressed (depress c) i d omega k - c.b / (5 * c.a))
  simpa only [solveDepressed_eq_inverseFourier] using htranslated

/-- Consequently, the four Fourier identities imply the exact factorization
of the original quintic by all five `solveGeneral` outputs, including repeated
roots with multiplicity. -/
theorem solveGeneral_factorization_of_fourierRelations [DecidableEq K]
    (c : GeneralQuintic K) (ha : c.a ≠ 0) (i : Invariants K)
    (d : RadicalCertificate (depress c) i) (omega : FifthRootOfUnity K)
    (h : FourierRelations (depress c) d.p1
      (fourierP2 (depress c) i d.chosen d.p1)
      (fourierP3 (depress c) i d.chosen d.p1)
      (fourierP4 (depress c) i d.chosen d.p1)) :
    c.polynomial = Polynomial.C c.a *
      ∏ k : Fin 5, (Polynomial.X - Polynomial.C (solveGeneral c i d omega k)) :=
  (solveGeneral_fiveRootRelations c ha i d omega h).factorization

end Field

end LeanProofs.PolynomialFormulas.LazardQuintic
