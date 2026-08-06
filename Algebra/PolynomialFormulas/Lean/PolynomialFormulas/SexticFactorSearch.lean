import PolynomialFormulas.SexticComputedResolventDecision

/-!
# Recursive bounded factor search for monic sextics

A reducible monic sextic has a monic factor of degree at most three.  This
file gives explicit synthetic-division tests for degrees one, two, and three,
and finite Cauchy/Vieta bounds for every coefficient searched.
-/

open scoped BigOperators Polynomial
open Polynomial
open Denumerable Encodable Function

namespace LeanProofs.PolynomialFormulas

open QuinticRadicalDecidability
open SexticRadicalDecidability
open SexticRadicalDecidability.MonicSextic

namespace SexticRadicalDecidability.MonicSextic

def height (f : MonicSextic) : ℕ :=
  max (f 5).natAbs <| max (f 4).natAbs <| max (f 3).natAbs <|
    max (f 2).natAbs <| max (f 1).natAbs (f 0).natAbs

def rootBound (f : MonicSextic) : ℕ := f.height + 1

noncomputable def complexPolynomial (f : MonicSextic) : ℂ[X] :=
  f.polynomial.map (Int.castRingHom ℂ)

theorem polynomial_coeff_natAbs_le_height (f : MonicSextic)
    (i : ℕ) (hi : i < 6) :
    (f.polynomial.coeff i).natAbs ≤ f.height := by
  interval_cases i <;>
    simp only [polynomial, coeff_add, coeff_X_pow,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] <;>
    norm_num <;> simp [height]

theorem complexPolynomial_monic (f : MonicSextic) :
    f.complexPolynomial.Monic := f.polynomial_monic.map _

@[simp] theorem complexPolynomial_natDegree (f : MonicSextic) :
    f.complexPolynomial.natDegree = 6 := by
  rw [complexPolynomial, f.polynomial_monic.natDegree_map,
    polynomial_natDegree]

theorem complexPolynomial_cauchyBound_le (f : MonicSextic) :
    f.complexPolynomial.cauchyBound ≤ f.rootBound := by
  rw [Polynomial.cauchyBound, complexPolynomial_natDegree,
    f.complexPolynomial_monic.leadingCoeff]
  simp only [nnnorm_one, div_one, rootBound, Nat.cast_add, Nat.cast_one,
    add_le_add_iff_right]
  apply Finset.sup_le
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [complexPolynomial, coeff_map]
  change ‖((f.polynomial.coeff i : ℤ) : ℂ)‖₊ ≤ (f.height : NNReal)
  rw [Complex.nnnorm_intCast, ← NNReal.natCast_natAbs]
  exact_mod_cast f.polynomial_coeff_natAbs_le_height i hi

theorem complexRoot_nnnorm_lt_rootBound (f : MonicSextic) {z : ℂ}
    (hz : f.complexPolynomial.IsRoot z) : ‖z‖₊ < f.rootBound :=
  (hz.norm_lt_cauchyBound f.complexPolynomial_monic.ne_zero).trans_le
    f.complexPolynomial_cauchyBound_le

/-! ## Synthetic division -/

def linearQ4 (f : MonicSextic) (c : ℤ) : ℤ := f 5 - c
def linearQ3 (f : MonicSextic) (c : ℤ) : ℤ := f 4 - c * f.linearQ4 c
def linearQ2 (f : MonicSextic) (c : ℤ) : ℤ := f 3 - c * f.linearQ3 c
def linearQ1 (f : MonicSextic) (c : ℤ) : ℤ := f 2 - c * f.linearQ2 c
def linearQ0 (f : MonicSextic) (c : ℤ) : ℤ := f 1 - c * f.linearQ1 c

def linearRemainderZero (f : MonicSextic) (c : ℤ) : Prop :=
  f 0 = c * f.linearQ0 c

instance (f : MonicSextic) (c : ℤ) : Decidable (linearRemainderZero f c) :=
  inferInstanceAs (Decidable (f 0 = c * f.linearQ0 c))

noncomputable def linearQuotient (f : MonicSextic) (c : ℤ) : ℤ[X] :=
  X ^ 5 + C (f.linearQ4 c) * X ^ 4 + C (f.linearQ3 c) * X ^ 3 +
    C (f.linearQ2 c) * X ^ 2 + C (f.linearQ1 c) * X + C (f.linearQ0 c)

theorem linear_division_identity (f : MonicSextic) (c : ℤ) :
    f.polynomial = linearFactor c * f.linearQuotient c +
      C (f 0 - c * f.linearQ0 c) := by
  simp [polynomial, linearFactor, linearQuotient, linearQ4, linearQ3,
    linearQ2, linearQ1, linearQ0]
  ring

theorem linearRemainderZero_iff_dvd (f : MonicSextic) (c : ℤ) :
    f.linearRemainderZero c ↔ linearFactor c ∣ f.polynomial := by
  rw [show linearFactor c = X - C (-c) by simp [linearFactor],
    dvd_iff_isRoot]
  simp [IsRoot, linearRemainderZero, polynomial, linearQ0, linearQ1,
    linearQ2, linearQ3, linearQ4]
  ring_nf
  constructor <;> intro h <;> linarith

def quadraticQ3 (f : MonicSextic) (b : ℤ) : ℤ := f 5 - b
def quadraticQ2 (f : MonicSextic) (b c : ℤ) : ℤ :=
  f 4 - c - b * f.quadraticQ3 b
def quadraticQ1 (f : MonicSextic) (b c : ℤ) : ℤ :=
  f 3 - b * f.quadraticQ2 b c - c * f.quadraticQ3 b
def quadraticQ0 (f : MonicSextic) (b c : ℤ) : ℤ :=
  f 2 - b * f.quadraticQ1 b c - c * f.quadraticQ2 b c

def quadraticRemainderZero (f : MonicSextic) (b c : ℤ) : Prop :=
  f 1 = b * f.quadraticQ0 b c + c * f.quadraticQ1 b c ∧
    f 0 = c * f.quadraticQ0 b c

instance (f : MonicSextic) (b c : ℤ) :
    Decidable (quadraticRemainderZero f b c) :=
  inferInstanceAs (Decidable
    (f 1 = b * f.quadraticQ0 b c + c * f.quadraticQ1 b c ∧
      f 0 = c * f.quadraticQ0 b c))

noncomputable def quadraticQuotient
    (f : MonicSextic) (b c : ℤ) : ℤ[X] :=
  X ^ 4 + C (f.quadraticQ3 b) * X ^ 3 +
    C (f.quadraticQ2 b c) * X ^ 2 + C (f.quadraticQ1 b c) * X +
    C (f.quadraticQ0 b c)

noncomputable def quadraticRemainder
    (f : MonicSextic) (b c : ℤ) : ℤ[X] :=
  C (f 1 - b * f.quadraticQ0 b c - c * f.quadraticQ1 b c) * X +
    C (f 0 - c * f.quadraticQ0 b c)

theorem quadratic_division_identity (f : MonicSextic) (b c : ℤ) :
    f.polynomial = quadraticFactor b c * f.quadraticQuotient b c +
      f.quadraticRemainder b c := by
  simp [polynomial, quadraticFactor, quadraticQuotient, quadraticRemainder,
    quadraticQ3, quadraticQ2, quadraticQ1, quadraticQ0]
  ring

theorem quadraticRemainder_eq_zero_iff (f : MonicSextic) (b c : ℤ) :
    f.quadraticRemainder b c = 0 ↔ f.quadraticRemainderZero b c := by
  constructor
  · intro h
    have h0 := congrArg (fun p : ℤ[X] ↦ p.eval 0) h
    have h1 := congrArg (fun p : ℤ[X] ↦ p.eval 1) h
    simp [quadraticRemainder] at h0 h1
    constructor <;> linarith
  · rintro ⟨h1, h0⟩
    simp [quadraticRemainder, h1, h0]

theorem quadraticRemainderZero_iff_dvd (f : MonicSextic) (b c : ℤ) :
    f.quadraticRemainderZero b c ↔ quadraticFactor b c ∣ f.polynomial := by
  rw [← modByMonic_eq_zero_iff_dvd (quadraticFactor_monic b c)]
  have hdeg : degree (f.quadraticRemainder b c) <
      degree (quadraticFactor b c) := by
    have hf : degree (quadraticFactor b c) = 2 := by
      simp only [quadraticFactor]
      compute_degree!
    rw [hf]
    simp only [quadraticRemainder]
    compute_degree!
  rw [quadratic_division_identity, add_modByMonic,
    self_mul_modByMonic (quadraticFactor_monic b c), zero_add,
    (modByMonic_eq_self_iff (quadraticFactor_monic b c)).mpr hdeg,
    quadraticRemainder_eq_zero_iff]

noncomputable def cubicFactor (b c d : ℤ) : ℤ[X] :=
  X ^ 3 + (C b * X ^ 2 + C c * X + C d)

theorem cubicFactor_monic (b c d : ℤ) : (cubicFactor b c d).Monic := by
  rw [cubicFactor]
  apply monic_X_pow_add
  calc
    degree (C b * X ^ 2 + C c * X + C d : ℤ[X]) ≤
        max (max (degree (C b * X ^ 2 : ℤ[X]))
          (degree (C c * X : ℤ[X]))) (degree (C d : ℤ[X])) :=
      (degree_add_le _ _).trans (max_le_max_right _ (degree_add_le _ _))
    _ ≤ 2 := max_le
      (max_le (degree_C_mul_X_pow_le 2 b)
        ((degree_C_mul_X_le c).trans (by norm_num)))
      (degree_C_le.trans (by norm_num))
    _ < 3 := by norm_num

def cubicQ2 (f : MonicSextic) (b : ℤ) : ℤ := f 5 - b
def cubicQ1 (f : MonicSextic) (b c : ℤ) : ℤ :=
  f 4 - c - b * f.cubicQ2 b
def cubicQ0 (f : MonicSextic) (b c d : ℤ) : ℤ :=
  f 3 - d - b * f.cubicQ1 b c - c * f.cubicQ2 b

def cubicRemainderZero (f : MonicSextic) (b c d : ℤ) : Prop :=
  f 2 = b * f.cubicQ0 b c d + c * f.cubicQ1 b c + d * f.cubicQ2 b ∧
    f 1 = c * f.cubicQ0 b c d + d * f.cubicQ1 b c ∧
    f 0 = d * f.cubicQ0 b c d

instance (f : MonicSextic) (b c d : ℤ) :
    Decidable (cubicRemainderZero f b c d) :=
  inferInstanceAs (Decidable
    (f 2 = b * f.cubicQ0 b c d + c * f.cubicQ1 b c + d * f.cubicQ2 b ∧
      f 1 = c * f.cubicQ0 b c d + d * f.cubicQ1 b c ∧
      f 0 = d * f.cubicQ0 b c d))

noncomputable def cubicQuotient
    (f : MonicSextic) (b c d : ℤ) : ℤ[X] :=
  X ^ 3 + C (f.cubicQ2 b) * X ^ 2 + C (f.cubicQ1 b c) * X +
    C (f.cubicQ0 b c d)

noncomputable def cubicRemainder
    (f : MonicSextic) (b c d : ℤ) : ℤ[X] :=
  C (f 2 - b * f.cubicQ0 b c d - c * f.cubicQ1 b c -
      d * f.cubicQ2 b) * X ^ 2 +
    C (f 1 - c * f.cubicQ0 b c d - d * f.cubicQ1 b c) * X +
    C (f 0 - d * f.cubicQ0 b c d)

theorem cubic_division_identity (f : MonicSextic) (b c d : ℤ) :
    f.polynomial = cubicFactor b c d * f.cubicQuotient b c d +
      f.cubicRemainder b c d := by
  simp [polynomial, cubicFactor, cubicQuotient, cubicRemainder,
    cubicQ2, cubicQ1, cubicQ0]
  ring

theorem cubicRemainder_eq_zero_iff (f : MonicSextic) (b c d : ℤ) :
    f.cubicRemainder b c d = 0 ↔ f.cubicRemainderZero b c d := by
  constructor
  · intro h
    have h0 := congrArg (fun p : ℤ[X] ↦ p.coeff 0) h
    have h1 := congrArg (fun p : ℤ[X] ↦ p.coeff 1) h
    have h2 := congrArg (fun p : ℤ[X] ↦ p.coeff 2) h
    simp only [cubicRemainder, coeff_add, coeff_C_mul_X_pow,
      coeff_C_mul_X, coeff_C] at h0 h1 h2
    norm_num at h0 h1 h2
    exact ⟨by linarith, by constructor <;> linarith⟩
  · rintro ⟨h2, h1, h0⟩
    simp [cubicRemainder, h2, h1, h0]
    ring

theorem cubicRemainderZero_iff_dvd (f : MonicSextic) (b c d : ℤ) :
    f.cubicRemainderZero b c d ↔ cubicFactor b c d ∣ f.polynomial := by
  rw [← modByMonic_eq_zero_iff_dvd (cubicFactor_monic b c d)]
  have hdeg : degree (f.cubicRemainder b c d) <
      degree (cubicFactor b c d) := by
    have hf : degree (cubicFactor b c d) = 3 := by
      simp only [cubicFactor]
      compute_degree!
    rw [hf]
    simp only [cubicRemainder]
    compute_degree!
  rw [cubic_division_identity, add_modByMonic,
    self_mul_modByMonic (cubicFactor_monic b c d), zero_add,
    (modByMonic_eq_self_iff (cubicFactor_monic b c d)).mpr hdeg,
    cubicRemainder_eq_zero_iff]

/-! ## Finite searches and coefficient bounds -/

def hasBoundedLinearFactor (f : MonicSextic) : Bool :=
  decide (∃ c ∈ symmetricInterval f.rootBound, f.linearRemainderZero c)

def hasBoundedQuadraticFactor (f : MonicSextic) : Bool :=
  decide (∃ b ∈ symmetricInterval (2 * f.rootBound),
    ∃ c ∈ symmetricInterval (f.rootBound ^ 2),
      f.quadraticRemainderZero b c)

def hasBoundedCubicFactor (f : MonicSextic) : Bool :=
  decide (∃ b ∈ symmetricInterval (3 * f.rootBound),
    ∃ c ∈ symmetricInterval (3 * f.rootBound ^ 2),
      ∃ d ∈ symmetricInterval (f.rootBound ^ 3),
        f.cubicRemainderZero b c d)

def hasBoundedNonlinearFactor (f : MonicSextic) : Bool :=
  f.hasBoundedQuadraticFactor || f.hasBoundedCubicFactor

def hasBoundedProperFactor (f : MonicSextic) : Bool :=
  f.hasBoundedLinearFactor || f.hasBoundedNonlinearFactor

theorem hasBoundedLinearFactor_iff_dvd (f : MonicSextic) :
    f.hasBoundedLinearFactor = true ↔
      ∃ c ∈ symmetricInterval f.rootBound, linearFactor c ∣ f.polynomial := by
  simp [hasBoundedLinearFactor, linearRemainderZero_iff_dvd]

theorem hasBoundedQuadraticFactor_iff_dvd (f : MonicSextic) :
    f.hasBoundedQuadraticFactor = true ↔
      ∃ b ∈ symmetricInterval (2 * f.rootBound),
        ∃ c ∈ symmetricInterval (f.rootBound ^ 2),
          quadraticFactor b c ∣ f.polynomial := by
  simp [hasBoundedQuadraticFactor, quadraticRemainderZero_iff_dvd]

theorem hasBoundedCubicFactor_iff_dvd (f : MonicSextic) :
    f.hasBoundedCubicFactor = true ↔
      ∃ b ∈ symmetricInterval (3 * f.rootBound),
        ∃ c ∈ symmetricInterval (3 * f.rootBound ^ 2),
          ∃ d ∈ symmetricInterval (f.rootBound ^ 3),
            cubicFactor b c d ∣ f.polynomial := by
  simp [hasBoundedCubicFactor, cubicRemainderZero_iff_dvd]

theorem linearFactor_mem_symmetricInterval_of_dvd (f : MonicSextic) (c : ℤ)
    (hdvd : linearFactor c ∣ f.polynomial) :
    c ∈ symmetricInterval f.rootBound := by
  have hrootZ : f.polynomial.IsRoot (-c) := by
    rw [show linearFactor c = X - C (-c) by simp [linearFactor],
      dvd_iff_isRoot] at hdvd
    exact hdvd
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

theorem quadraticFactor_mem_symmetricInterval_of_dvd
    (f : MonicSextic) (b c : ℤ)
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
    simpa [qC, qZ, complexPolynomial] using
      Polynomial.map_dvd (Int.castRingHom ℂ) hdvd
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
    simp only [qZ, quadraticFactor, coeff_add, coeff_X_pow,
      coeff_C_mul_X, coeff_C]
    norm_num
  have hnext : qC.nextCoeff = (b : ℂ) := by
    calc
      qC.nextCoeff = (Int.castRingHom ℂ) qZ.nextCoeff := by
        exact nextCoeff_map Int.cast_injective qZ
      _ = (b : ℂ) := by rw [hnextZ]; rfl
  have hcoeffZeroZ : qZ.coeff 0 = c := by
    simp only [qZ, quadraticFactor, coeff_add, coeff_X_pow,
      coeff_C_mul_X, coeff_C]
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
    exact_mod_cast this.le
  have hcNat : c.natAbs ≤ f.rootBound ^ 2 := by
    have : (c.natAbs : NNReal) < (f.rootBound ^ 2 : ℕ) := by
      simpa [Complex.nnnorm_intCast, ← NNReal.natCast_natAbs] using hcNorm
    exact_mod_cast this.le
  constructor
  · rw [mem_symmetricInterval]
    have hbZ : (b.natAbs : ℤ) ≤ (2 * f.rootBound : ℕ) := by
      exact_mod_cast hbNat
    rw [Int.natCast_natAbs] at hbZ
    constructor <;> omega
  · rw [mem_symmetricInterval]
    have hcZ : (c.natAbs : ℤ) ≤ (f.rootBound ^ 2 : ℕ) := by
      exact_mod_cast hcNat
    rw [Int.natCast_natAbs] at hcZ
    constructor <;> omega

theorem cubicFactor_mem_symmetricInterval_of_dvd
    (f : MonicSextic) (b c d : ℤ)
    (hdvd : cubicFactor b c d ∣ f.polynomial) :
    b ∈ symmetricInterval (3 * f.rootBound) ∧
      c ∈ symmetricInterval (3 * f.rootBound ^ 2) ∧
      d ∈ symmetricInterval (f.rootBound ^ 3) := by
  let qZ : ℤ[X] := cubicFactor b c d
  let qC : ℂ[X] := qZ.map (Int.castRingHom ℂ)
  have hqZmonic : qZ.Monic := cubicFactor_monic b c d
  have hqCmonic : qC.Monic := hqZmonic.map _
  have hqZdeg : qZ.natDegree = 3 := by
    simp only [qZ, cubicFactor]
    compute_degree!
  have hqCdeg : qC.natDegree = 3 := by
    simpa [qC] using (hqZmonic.natDegree_map (Int.castRingHom ℂ)).trans hqZdeg
  have hsplit : qC.Splits := IsAlgClosed.splits qC
  have hcard : qC.roots.card = 3 := by
    rw [← hsplit.natDegree_eq_card_roots, hqCdeg]
  obtain ⟨z, w, u, hroots⟩ := Multiset.card_eq_three.mp hcard
  have hdvdC : qC ∣ f.complexPolynomial := by
    simpa [qC, qZ, complexPolynomial] using
      Polynomial.map_dvd (Int.castRingHom ℂ) hdvd
  have hzq : qC.IsRoot z := by
    rw [← mem_roots hqCmonic.ne_zero]
    simp [hroots]
  have hwq : qC.IsRoot w := by
    rw [← mem_roots hqCmonic.ne_zero]
    simp [hroots]
  have huq : qC.IsRoot u := by
    rw [← mem_roots hqCmonic.ne_zero]
    simp [hroots]
  have hz := f.complexRoot_nnnorm_lt_rootBound (hzq.dvd hdvdC)
  have hw := f.complexRoot_nnnorm_lt_rootBound (hwq.dvd hdvdC)
  have hu := f.complexRoot_nnnorm_lt_rootBound (huq.dvd hdvdC)
  have hcoeff2 : qC.coeff 2 = (b : ℂ) := by
    simp only [qC, coeff_map]
    simp only [qZ, cubicFactor, coeff_add, coeff_X_pow,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    norm_num
  have hcoeff1 : qC.coeff 1 = (c : ℂ) := by
    simp only [qC, coeff_map]
    simp only [qZ, cubicFactor, coeff_add, coeff_X_pow,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    norm_num
  have hcoeff0 : qC.coeff 0 = (d : ℂ) := by
    simp only [qC, coeff_map]
    simp only [qZ, cubicFactor, coeff_add, coeff_X_pow,
      coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
    norm_num
  have hbRaw := Polynomial.coeff_eq_esymm_roots_of_splits
    (p := qC) hsplit (k := 2) (by omega)
  have hcRaw := Polynomial.coeff_eq_esymm_roots_of_splits
    (p := qC) hsplit (k := 1) (by omega)
  have hdRaw := Polynomial.coeff_eq_esymm_roots_of_splits
    (p := qC) hsplit (k := 0) (by omega)
  have hpowersetSingleton :
      Multiset.powersetCard 1 ({u} : Multiset ℂ) =
        ({{u}} : Multiset (Multiset ℂ)) := by
    change Multiset.powersetCard (0 + 1) (u ::ₘ 0) = _
    rw [Multiset.powersetCard_cons]
    simp [Multiset.powersetCard_zero_left,
      Multiset.powersetCard_zero_right]
  have hbEq : (b : ℂ) = -(z + w + u) := by
    rw [hcoeff2, hqCdeg, hqCmonic.leadingCoeff, hroots] at hbRaw
    simp [Multiset.esymm, Multiset.powersetCard_cons,
      Multiset.powersetCard_zero_left, Multiset.powersetCard_zero_right,
      hpowersetSingleton] at hbRaw
    ring_nf at hbRaw ⊢
    exact hbRaw
  have hcEq : (c : ℂ) = z * w + z * u + w * u := by
    rw [hcoeff1, hqCdeg, hqCmonic.leadingCoeff, hroots] at hcRaw
    simp [Multiset.esymm, Multiset.powersetCard_cons,
      Multiset.powersetCard_zero_left, Multiset.powersetCard_zero_right,
      hpowersetSingleton] at hcRaw
    ring_nf at hcRaw ⊢
    exact hcRaw
  have hdEq : (d : ℂ) = -(z * w * u) := by
    rw [hcoeff0, hqCdeg, hqCmonic.leadingCoeff, hroots] at hdRaw
    simp [Multiset.esymm, Multiset.powersetCard_cons,
      Multiset.powersetCard_zero_left, Multiset.powersetCard_zero_right,
      hpowersetSingleton] at hdRaw
    ring_nf at hdRaw ⊢
    exact hdRaw
  have hbNorm : ‖(b : ℂ)‖₊ < (3 * f.rootBound : ℕ) := by
    calc
      ‖(b : ℂ)‖₊ = ‖z + w + u‖₊ := by rw [hbEq, nnnorm_neg]
      _ ≤ ‖z‖₊ + ‖w‖₊ + ‖u‖₊ := by
        calc
          ‖z + w + u‖₊ ≤ ‖z + w‖₊ + ‖u‖₊ := nnnorm_add_le _ _
          _ ≤ ‖z‖₊ + ‖w‖₊ + ‖u‖₊ :=
            add_le_add (nnnorm_add_le z w) (le_refl _)
      _ < (f.rootBound : NNReal) + f.rootBound + f.rootBound :=
        add_lt_add (add_lt_add hz hw) hu
      _ = (3 * f.rootBound : ℕ) := by norm_num; ring
  have hcNorm : ‖(c : ℂ)‖₊ < (3 * f.rootBound ^ 2 : ℕ) := by
    calc
      ‖(c : ℂ)‖₊ ≤ ‖z * w‖₊ + ‖z * u‖₊ + ‖w * u‖₊ := by
        rw [hcEq]
        calc
          ‖z * w + z * u + w * u‖₊ ≤
              ‖z * w + z * u‖₊ + ‖w * u‖₊ := nnnorm_add_le _ _
          _ ≤ ‖z * w‖₊ + ‖z * u‖₊ + ‖w * u‖₊ :=
            add_le_add (nnnorm_add_le (z * w) (z * u)) (le_refl _)
      _ < (f.rootBound : NNReal) * f.rootBound +
          f.rootBound * f.rootBound + f.rootBound * f.rootBound := by
        simp only [nnnorm_mul]
        gcongr
      _ = (3 * f.rootBound ^ 2 : ℕ) := by norm_num; ring
  have hdNorm : ‖(d : ℂ)‖₊ < (f.rootBound ^ 3 : ℕ) := by
    calc
      ‖(d : ℂ)‖₊ = ‖z‖₊ * ‖w‖₊ * ‖u‖₊ := by
        rw [hdEq, nnnorm_neg, nnnorm_mul, nnnorm_mul]
      _ < (f.rootBound : NNReal) * f.rootBound * f.rootBound := by
        gcongr
      _ = (f.rootBound ^ 3 : ℕ) := by norm_num; ring
  have hbNat : b.natAbs ≤ 3 * f.rootBound := by
    have : (b.natAbs : NNReal) < (3 * f.rootBound : ℕ) := by
      simpa [Complex.nnnorm_intCast, ← NNReal.natCast_natAbs] using hbNorm
    exact_mod_cast this.le
  have hcNat : c.natAbs ≤ 3 * f.rootBound ^ 2 := by
    have : (c.natAbs : NNReal) < (3 * f.rootBound ^ 2 : ℕ) := by
      simpa [Complex.nnnorm_intCast, ← NNReal.natCast_natAbs] using hcNorm
    exact_mod_cast this.le
  have hdNat : d.natAbs ≤ f.rootBound ^ 3 := by
    have : (d.natAbs : NNReal) < (f.rootBound ^ 3 : ℕ) := by
      simpa [Complex.nnnorm_intCast, ← NNReal.natCast_natAbs] using hdNorm
    exact_mod_cast this.le
  have mem_of_natAbs_le (x : ℤ) (r : ℕ) (h : x.natAbs ≤ r) :
      x ∈ symmetricInterval r := by
    rw [mem_symmetricInterval]
    have hx : (x.natAbs : ℤ) ≤ (r : ℤ) := by exact_mod_cast h
    rw [Int.natCast_natAbs] at hx
    constructor <;> omega
  exact ⟨mem_of_natAbs_le b _ hbNat, mem_of_natAbs_le c _ hcNat,
    mem_of_natAbs_le d _ hdNat⟩

theorem monic_natDegree_three_eq_cubicFactor (q : ℤ[X]) (hq : q.Monic)
    (hdeg : q.natDegree = 3) :
    q = cubicFactor (q.coeff 2) (q.coeff 1) (q.coeff 0) := by
  have hlead : q.coeff 3 = 1 := by
    rw [← hdeg]
    exact hq.coeff_natDegree
  calc
    q = ∑ i ∈ Finset.range (q.natDegree + 1),
        C (q.coeff i) * X ^ i := q.as_sum_range_C_mul_X_pow
    _ = cubicFactor (q.coeff 2) (q.coeff 1) (q.coeff 0) := by
      simp only [hdeg, Finset.sum_range_succ, Finset.sum_range_zero,
        pow_zero, pow_one, mul_one, zero_add, hlead, map_one, cubicFactor]
      ring

theorem not_irreducible_iff_exists_small_monic_factor (f : MonicSextic) :
    ¬Irreducible f.polynomial ↔
      ∃ q : ℤ[X], q.Monic ∧
        (q.natDegree = 1 ∨ q.natDegree = 2 ∨ q.natDegree = 3) ∧
        q ∣ f.polynomial := by
  have hp1 : f.polynomial ≠ 1 := by
    intro hp1
    have hdeg := congrArg Polynomial.natDegree hp1
    simp [polynomial_natDegree] at hdeg
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
      rcases hdeg with hdeg | hdeg | hdeg <;> omega
    · exact hdvd

theorem hasBoundedNonlinearFactor_iff_dvd (f : MonicSextic) :
    f.hasBoundedNonlinearFactor = true ↔
      (∃ b ∈ symmetricInterval (2 * f.rootBound),
        ∃ c ∈ symmetricInterval (f.rootBound ^ 2),
          quadraticFactor b c ∣ f.polynomial) ∨
      (∃ b ∈ symmetricInterval (3 * f.rootBound),
        ∃ c ∈ symmetricInterval (3 * f.rootBound ^ 2),
          ∃ d ∈ symmetricInterval (f.rootBound ^ 3),
            cubicFactor b c d ∣ f.polynomial) := by
  rw [hasBoundedNonlinearFactor, Bool.or_eq_true,
    hasBoundedQuadraticFactor_iff_dvd, hasBoundedCubicFactor_iff_dvd]

theorem hasBoundedProperFactor_iff_not_irreducible (f : MonicSextic) :
    f.hasBoundedProperFactor = true ↔ ¬Irreducible f.polynomial := by
  rw [hasBoundedProperFactor, Bool.or_eq_true,
    hasBoundedLinearFactor_iff_dvd, hasBoundedNonlinearFactor_iff_dvd,
    not_irreducible_iff_exists_small_monic_factor]
  constructor
  · rintro (⟨a, -, ha⟩ | ⟨b, -, c, -, hbc⟩ | ⟨b, -, c, -, d, -, hbcd⟩)
    · refine ⟨linearFactor a, linearFactor_monic a, Or.inl ?_, ha⟩
      simp only [linearFactor]
      compute_degree!
    · refine ⟨quadraticFactor b c, quadraticFactor_monic b c,
        Or.inr (Or.inl ?_), hbc⟩
      simp only [quadraticFactor]
      compute_degree!
    · refine ⟨cubicFactor b c d, cubicFactor_monic b c d,
        Or.inr (Or.inr ?_), hbcd⟩
      simp only [cubicFactor]
      compute_degree!
  · rintro ⟨q, hq, hdeg, hdvd⟩
    rcases hdeg with hdeg | hdeg | hdeg
    · have hqeq : q = linearFactor (q.coeff 0) := by
        simpa [linearFactor] using hq.eq_X_add_C hdeg
      rw [hqeq] at hdvd
      exact Or.inl ⟨q.coeff 0,
        f.linearFactor_mem_symmetricInterval_of_dvd _ hdvd, hdvd⟩
    · have hqeq :=
        QuinticRadicalDecidability.MonicQuintic.monic_natDegree_two_eq_quadraticFactor
          q hq hdeg
      rw [hqeq] at hdvd
      have hb := f.quadraticFactor_mem_symmetricInterval_of_dvd
        (q.coeff 1) (q.coeff 0) hdvd
      exact Or.inr <| Or.inl ⟨q.coeff 1, hb.1, q.coeff 0, hb.2, hdvd⟩
    · have hqeq := monic_natDegree_three_eq_cubicFactor q hq hdeg
      rw [hqeq] at hdvd
      have hb := f.cubicFactor_mem_symmetricInterval_of_dvd
        (q.coeff 2) (q.coeff 1) (q.coeff 0) hdvd
      exact Or.inr <| Or.inr ⟨q.coeff 2, hb.1, q.coeff 1, hb.2.1,
        q.coeff 0, hb.2.2, hdvd⟩

theorem hasBoundedProperFactor_iff_not_irreducible_map_rat
    (f : MonicSextic) :
    f.hasBoundedProperFactor = true ↔ ¬Irreducible f.ratPolynomial := by
  rw [f.hasBoundedProperFactor_iff_not_irreducible]
  simpa only [ratPolynomial, algebraMap_int_eq] using
    not_congr
      (f.polynomial_monic.irreducible_iff_irreducible_map_fraction_map (K := ℚ))

/-! ## Primitive-recursive certification -/

theorem coeff_primrec (i : Fin 6) :
    Primrec fun f : MonicSextic ↦ f i :=
  Primrec.fin_app.comp Primrec.id (Primrec.const i)

theorem height_primrec : Primrec height := by
  exact (Primrec.nat_max.comp
    (QuinticRadicalPrimrec.int_natAbs_primrec.comp (coeff_primrec 5)) <|
    Primrec.nat_max.comp
      (QuinticRadicalPrimrec.int_natAbs_primrec.comp (coeff_primrec 4)) <|
    Primrec.nat_max.comp
      (QuinticRadicalPrimrec.int_natAbs_primrec.comp (coeff_primrec 3)) <|
    Primrec.nat_max.comp
      (QuinticRadicalPrimrec.int_natAbs_primrec.comp (coeff_primrec 2)) <|
    Primrec.nat_max.comp
      (QuinticRadicalPrimrec.int_natAbs_primrec.comp (coeff_primrec 1))
      (QuinticRadicalPrimrec.int_natAbs_primrec.comp (coeff_primrec 0))).of_eq
        fun _ ↦ rfl

theorem rootBound_primrec : Primrec rootBound :=
  (Primrec.succ.comp height_primrec).of_eq fun _ ↦ rfl

theorem linearQ4_primrec :
    Primrec fun p : MonicSextic × ℤ ↦ p.1.linearQ4 p.2 :=
  (QuinticRadicalPrimrec.int_sub_primrec.comp
    ((coeff_primrec 5).comp Primrec.fst) Primrec.snd).of_eq fun _ ↦ rfl

theorem linearQ3_primrec :
    Primrec fun p : MonicSextic × ℤ ↦ p.1.linearQ3 p.2 :=
  (QuinticRadicalPrimrec.int_sub_primrec.comp
    ((coeff_primrec 4).comp Primrec.fst)
    (QuinticRadicalPrimrec.int_mul_primrec.comp Primrec.snd
      linearQ4_primrec)).of_eq fun _ ↦ rfl

theorem linearQ2_primrec :
    Primrec fun p : MonicSextic × ℤ ↦ p.1.linearQ2 p.2 :=
  (QuinticRadicalPrimrec.int_sub_primrec.comp
    ((coeff_primrec 3).comp Primrec.fst)
    (QuinticRadicalPrimrec.int_mul_primrec.comp Primrec.snd
      linearQ3_primrec)).of_eq fun _ ↦ rfl

theorem linearQ1_primrec :
    Primrec fun p : MonicSextic × ℤ ↦ p.1.linearQ1 p.2 :=
  (QuinticRadicalPrimrec.int_sub_primrec.comp
    ((coeff_primrec 2).comp Primrec.fst)
    (QuinticRadicalPrimrec.int_mul_primrec.comp Primrec.snd
      linearQ2_primrec)).of_eq fun _ ↦ rfl

theorem linearQ0_primrec :
    Primrec fun p : MonicSextic × ℤ ↦ p.1.linearQ0 p.2 :=
  (QuinticRadicalPrimrec.int_sub_primrec.comp
    ((coeff_primrec 1).comp Primrec.fst)
    (QuinticRadicalPrimrec.int_mul_primrec.comp Primrec.snd
      linearQ1_primrec)).of_eq fun _ ↦ rfl

theorem linearRemainderZero_primrec : PrimrecRel linearRemainderZero := by
  exact (Primrec.eq.comp ((coeff_primrec 0).comp Primrec.fst)
    (QuinticRadicalPrimrec.int_mul_primrec.comp Primrec.snd
      linearQ0_primrec)).of_eq fun _ ↦ by
        simp only [linearRemainderZero]

theorem quadraticQ3_primrec :
    Primrec fun p : MonicSextic × (ℤ × ℤ) ↦ p.1.quadraticQ3 p.2.1 :=
  (QuinticRadicalPrimrec.int_sub_primrec.comp
    ((coeff_primrec 5).comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd)).of_eq fun _ ↦ rfl

theorem quadraticQ2_primrec :
    Primrec fun p : MonicSextic × (ℤ × ℤ) ↦
      p.1.quadraticQ2 p.2.1 p.2.2 := by
  exact (QuinticRadicalPrimrec.int_sub_primrec.comp
    (QuinticRadicalPrimrec.int_sub_primrec.comp
      ((coeff_primrec 4).comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd))
    (QuinticRadicalPrimrec.int_mul_primrec.comp
      (Primrec.fst.comp Primrec.snd) quadraticQ3_primrec)).of_eq fun _ ↦ rfl

theorem quadraticQ1_primrec :
    Primrec fun p : MonicSextic × (ℤ × ℤ) ↦
      p.1.quadraticQ1 p.2.1 p.2.2 := by
  have hq3 := quadraticQ3_primrec
  have hq2 := quadraticQ2_primrec
  exact (QuinticRadicalPrimrec.int_sub_primrec.comp
    (QuinticRadicalPrimrec.int_sub_primrec.comp
      ((coeff_primrec 3).comp Primrec.fst)
      (QuinticRadicalPrimrec.int_mul_primrec.comp
        (Primrec.fst.comp Primrec.snd) hq2))
    (QuinticRadicalPrimrec.int_mul_primrec.comp
      (Primrec.snd.comp Primrec.snd) hq3)).of_eq fun _ ↦ rfl

theorem quadraticQ0_primrec :
    Primrec fun p : MonicSextic × (ℤ × ℤ) ↦
      p.1.quadraticQ0 p.2.1 p.2.2 := by
  have hq2 := quadraticQ2_primrec
  have hq1 := quadraticQ1_primrec
  exact (QuinticRadicalPrimrec.int_sub_primrec.comp
    (QuinticRadicalPrimrec.int_sub_primrec.comp
      ((coeff_primrec 2).comp Primrec.fst)
      (QuinticRadicalPrimrec.int_mul_primrec.comp
        (Primrec.fst.comp Primrec.snd) hq1))
    (QuinticRadicalPrimrec.int_mul_primrec.comp
      (Primrec.snd.comp Primrec.snd) hq2)).of_eq fun _ ↦ rfl

theorem quadraticRemainderZero_primrec :
    PrimrecPred fun p : MonicSextic × (ℤ × ℤ) ↦
      p.1.quadraticRemainderZero p.2.1 p.2.2 := by
  have hq0 := quadraticQ0_primrec
  have hq1 := quadraticQ1_primrec
  have hleft : PrimrecPred fun p : MonicSextic × (ℤ × ℤ) ↦
      p.1 1 = p.2.1 * p.1.quadraticQ0 p.2.1 p.2.2 +
        p.2.2 * p.1.quadraticQ1 p.2.1 p.2.2 :=
    Primrec.eq.comp ((coeff_primrec 1).comp Primrec.fst)
      (QuinticRadicalPrimrec.int_add_primrec.comp
        (QuinticRadicalPrimrec.int_mul_primrec.comp
          (Primrec.fst.comp Primrec.snd) hq0)
        (QuinticRadicalPrimrec.int_mul_primrec.comp
          (Primrec.snd.comp Primrec.snd) hq1))
  have hright : PrimrecPred fun p : MonicSextic × (ℤ × ℤ) ↦
      p.1 0 = p.2.2 * p.1.quadraticQ0 p.2.1 p.2.2 :=
    Primrec.eq.comp ((coeff_primrec 0).comp Primrec.fst)
      (QuinticRadicalPrimrec.int_mul_primrec.comp
        (Primrec.snd.comp Primrec.snd) hq0)
  exact (hleft.and hright).of_eq fun _ ↦ by
    simp only [quadraticRemainderZero]

theorem cubicQ2_primrec :
    Primrec fun p : MonicSextic × (ℤ × (ℤ × ℤ)) ↦
      p.1.cubicQ2 p.2.1 :=
  (QuinticRadicalPrimrec.int_sub_primrec.comp
    ((coeff_primrec 5).comp Primrec.fst)
    (Primrec.fst.comp Primrec.snd)).of_eq fun _ ↦ rfl

theorem cubicQ1_primrec :
    Primrec fun p : MonicSextic × (ℤ × (ℤ × ℤ)) ↦
      p.1.cubicQ1 p.2.1 p.2.2.1 := by
  exact (QuinticRadicalPrimrec.int_sub_primrec.comp
    (QuinticRadicalPrimrec.int_sub_primrec.comp
      ((coeff_primrec 4).comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    (QuinticRadicalPrimrec.int_mul_primrec.comp
      (Primrec.fst.comp Primrec.snd) cubicQ2_primrec)).of_eq fun _ ↦ rfl

theorem cubicQ0_primrec :
    Primrec fun p : MonicSextic × (ℤ × (ℤ × ℤ)) ↦
      p.1.cubicQ0 p.2.1 p.2.2.1 p.2.2.2 := by
  have hq2 := cubicQ2_primrec
  have hq1 := cubicQ1_primrec
  exact (QuinticRadicalPrimrec.int_sub_primrec.comp
    (QuinticRadicalPrimrec.int_sub_primrec.comp
      (QuinticRadicalPrimrec.int_sub_primrec.comp
        ((coeff_primrec 3).comp Primrec.fst)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (QuinticRadicalPrimrec.int_mul_primrec.comp
        (Primrec.fst.comp Primrec.snd) hq1))
    (QuinticRadicalPrimrec.int_mul_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hq2)).of_eq fun _ ↦ rfl

theorem cubicRemainderZero_primrec :
    PrimrecPred fun p : MonicSextic × (ℤ × (ℤ × ℤ)) ↦
      p.1.cubicRemainderZero p.2.1 p.2.2.1 p.2.2.2 := by
  have hq2 := cubicQ2_primrec
  have hq1 := cubicQ1_primrec
  have hq0 := cubicQ0_primrec
  have h2 : PrimrecPred fun p : MonicSextic × (ℤ × (ℤ × ℤ)) ↦
      p.1 2 = p.2.1 * p.1.cubicQ0 p.2.1 p.2.2.1 p.2.2.2 +
        p.2.2.1 * p.1.cubicQ1 p.2.1 p.2.2.1 +
        p.2.2.2 * p.1.cubicQ2 p.2.1 :=
    Primrec.eq.comp ((coeff_primrec 2).comp Primrec.fst)
      (QuinticRadicalPrimrec.int_add_primrec.comp
        (QuinticRadicalPrimrec.int_add_primrec.comp
          (QuinticRadicalPrimrec.int_mul_primrec.comp
            (Primrec.fst.comp Primrec.snd) hq0)
          (QuinticRadicalPrimrec.int_mul_primrec.comp
            (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hq1))
        (QuinticRadicalPrimrec.int_mul_primrec.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hq2))
  have h1 : PrimrecPred fun p : MonicSextic × (ℤ × (ℤ × ℤ)) ↦
      p.1 1 = p.2.2.1 * p.1.cubicQ0 p.2.1 p.2.2.1 p.2.2.2 +
        p.2.2.2 * p.1.cubicQ1 p.2.1 p.2.2.1 :=
    Primrec.eq.comp ((coeff_primrec 1).comp Primrec.fst)
      (QuinticRadicalPrimrec.int_add_primrec.comp
        (QuinticRadicalPrimrec.int_mul_primrec.comp
          (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) hq0)
        (QuinticRadicalPrimrec.int_mul_primrec.comp
          (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hq1))
  have h0 : PrimrecPred fun p : MonicSextic × (ℤ × (ℤ × ℤ)) ↦
      p.1 0 = p.2.2.2 * p.1.cubicQ0 p.2.1 p.2.2.1 p.2.2.2 :=
    Primrec.eq.comp ((coeff_primrec 0).comp Primrec.fst)
      (QuinticRadicalPrimrec.int_mul_primrec.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) hq0)
  exact (h2.and (h1.and h0)).of_eq fun _ ↦ by
    simp only [cubicRemainderZero]

theorem exists_code_linear_iff (f : MonicSextic) :
    (∃ n < QuinticRadicalPrimrec.symmetricCodeBound f.rootBound,
      f.linearRemainderZero (ofNat ℤ n)) ↔
      ∃ c ∈ symmetricInterval f.rootBound, f.linearRemainderZero c := by
  constructor
  · rintro ⟨n, hn, hz⟩
    exact ⟨ofNat ℤ n,
      (QuinticRadicalPrimrec.ofNat_int_mem_symmetricInterval_iff
        n f.rootBound).mpr hn, hz⟩
  · rintro ⟨c, hc, hz⟩
    refine ⟨Equiv.intEquivNat c, ?_, ?_⟩
    · exact (QuinticRadicalPrimrec.intEquivNat_lt_iff_mem_symmetricInterval
        c f.rootBound).mpr hc
    · change f.linearRemainderZero
        (Equiv.intEquivNat.symm (Equiv.intEquivNat c))
      simpa using hz

theorem exists_code_quadratic_iff (f : MonicSextic) :
    (∃ nb < QuinticRadicalPrimrec.symmetricCodeBound (2 * f.rootBound),
      ∃ nc < QuinticRadicalPrimrec.symmetricCodeBound (f.rootBound ^ 2),
        f.quadraticRemainderZero (ofNat ℤ nb) (ofNat ℤ nc)) ↔
      ∃ b ∈ symmetricInterval (2 * f.rootBound),
        ∃ c ∈ symmetricInterval (f.rootBound ^ 2),
          f.quadraticRemainderZero b c := by
  constructor
  · rintro ⟨nb, hnb, nc, hnc, hz⟩
    exact ⟨ofNat ℤ nb,
      (QuinticRadicalPrimrec.ofNat_int_mem_symmetricInterval_iff
        nb (2 * f.rootBound)).mpr hnb,
      ofNat ℤ nc,
      (QuinticRadicalPrimrec.ofNat_int_mem_symmetricInterval_iff
        nc (f.rootBound ^ 2)).mpr hnc, hz⟩
  · rintro ⟨b, hb, c, hc, hz⟩
    refine ⟨Equiv.intEquivNat b, ?_, Equiv.intEquivNat c, ?_, ?_⟩
    · exact (QuinticRadicalPrimrec.intEquivNat_lt_iff_mem_symmetricInterval
        b (2 * f.rootBound)).mpr hb
    · exact (QuinticRadicalPrimrec.intEquivNat_lt_iff_mem_symmetricInterval
        c (f.rootBound ^ 2)).mpr hc
    · change f.quadraticRemainderZero
        (Equiv.intEquivNat.symm (Equiv.intEquivNat b))
        (Equiv.intEquivNat.symm (Equiv.intEquivNat c))
      simpa using hz

theorem exists_code_cubic_iff (f : MonicSextic) :
    (∃ nb < QuinticRadicalPrimrec.symmetricCodeBound (3 * f.rootBound),
      ∃ nc < QuinticRadicalPrimrec.symmetricCodeBound (3 * f.rootBound ^ 2),
        ∃ nd < QuinticRadicalPrimrec.symmetricCodeBound (f.rootBound ^ 3),
          f.cubicRemainderZero (ofNat ℤ nb) (ofNat ℤ nc) (ofNat ℤ nd)) ↔
      ∃ b ∈ symmetricInterval (3 * f.rootBound),
        ∃ c ∈ symmetricInterval (3 * f.rootBound ^ 2),
          ∃ d ∈ symmetricInterval (f.rootBound ^ 3),
            f.cubicRemainderZero b c d := by
  constructor
  · rintro ⟨nb, hnb, nc, hnc, nd, hnd, hz⟩
    exact ⟨ofNat ℤ nb,
      (QuinticRadicalPrimrec.ofNat_int_mem_symmetricInterval_iff
        nb (3 * f.rootBound)).mpr hnb,
      ofNat ℤ nc,
      (QuinticRadicalPrimrec.ofNat_int_mem_symmetricInterval_iff
        nc (3 * f.rootBound ^ 2)).mpr hnc,
      ofNat ℤ nd,
      (QuinticRadicalPrimrec.ofNat_int_mem_symmetricInterval_iff
        nd (f.rootBound ^ 3)).mpr hnd, hz⟩
  · rintro ⟨b, hb, c, hc, d, hd, hz⟩
    refine ⟨Equiv.intEquivNat b, ?_, Equiv.intEquivNat c, ?_,
      Equiv.intEquivNat d, ?_, ?_⟩
    · exact (QuinticRadicalPrimrec.intEquivNat_lt_iff_mem_symmetricInterval
        b (3 * f.rootBound)).mpr hb
    · exact (QuinticRadicalPrimrec.intEquivNat_lt_iff_mem_symmetricInterval
        c (3 * f.rootBound ^ 2)).mpr hc
    · exact (QuinticRadicalPrimrec.intEquivNat_lt_iff_mem_symmetricInterval
        d (f.rootBound ^ 3)).mpr hd
    · change f.cubicRemainderZero
        (Equiv.intEquivNat.symm (Equiv.intEquivNat b))
        (Equiv.intEquivNat.symm (Equiv.intEquivNat c))
        (Equiv.intEquivNat.symm (Equiv.intEquivNat d))
      simpa using hz

theorem hasBoundedLinearFactor_primrec : Primrec hasBoundedLinearFactor := by
  have hdecode : Primrec fun n : ℕ ↦ ofNat ℤ n := Primrec.ofNat ℤ
  have hrel : PrimrecRel fun n : ℕ ↦ fun f : MonicSextic ↦
      f.linearRemainderZero (ofNat ℤ n) :=
    linearRemainderZero_primrec.comp Primrec.snd (hdecode.comp Primrec.fst)
  have hbound : Primrec fun f : MonicSextic ↦
      QuinticRadicalPrimrec.symmetricCodeBound f.rootBound :=
    QuinticRadicalPrimrec.symmetricCodeBound_primrec.comp rootBound_primrec
  have hp : PrimrecPred fun f : MonicSextic ↦
      ∃ n < QuinticRadicalPrimrec.symmetricCodeBound f.rootBound,
        f.linearRemainderZero (ofNat ℤ n) :=
    QuinticRadicalPrimrec.primrecPred_exists_lt hrel hbound
  exact hp.decide.of_eq fun f ↦ by
    rw [show f.hasBoundedLinearFactor = decide
      (∃ c ∈ symmetricInterval f.rootBound,
        f.linearRemainderZero c) by rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact exists_code_linear_iff f

theorem hasBoundedQuadraticFactor_primrec :
    Primrec hasBoundedQuadraticFactor := by
  have hdecode : Primrec fun n : ℕ ↦ ofNat ℤ n := Primrec.ofNat ℤ
  have hmap : Primrec fun q : ℕ × (ℕ × MonicSextic) ↦
      (q.2.2, (ofNat ℤ q.2.1, ofNat ℤ q.1)) :=
    Primrec.pair (Primrec.snd.comp Primrec.snd) <| Primrec.pair
      (hdecode.comp (Primrec.fst.comp Primrec.snd))
      (hdecode.comp Primrec.fst)
  have htest : PrimrecPred fun q : ℕ × (ℕ × MonicSextic) ↦
      q.2.2.quadraticRemainderZero (ofNat ℤ q.2.1) (ofNat ℤ q.1) :=
    quadraticRemainderZero_primrec.comp hmap
  have hr2 : Primrec fun f : MonicSextic ↦ f.rootBound ^ 2 :=
    (Primrec.nat_mul.comp rootBound_primrec rootBound_primrec).of_eq
      fun f ↦ by simp [pow_two]
  have hbRadius : Primrec fun f : MonicSextic ↦ 2 * f.rootBound :=
    Primrec.nat_mul.comp (Primrec.const 2) rootBound_primrec
  have hb : Primrec fun f : MonicSextic ↦
      QuinticRadicalPrimrec.symmetricCodeBound (2 * f.rootBound) :=
    QuinticRadicalPrimrec.symmetricCodeBound_primrec.comp hbRadius
  have hc : Primrec₂ fun _ : ℕ ↦ fun f : MonicSextic ↦
      QuinticRadicalPrimrec.symmetricCodeBound (f.rootBound ^ 2) :=
    (QuinticRadicalPrimrec.symmetricCodeBound_primrec.comp hr2).comp₂
      Primrec₂.right
  have hp : PrimrecPred fun f : MonicSextic ↦
      ∃ nb < QuinticRadicalPrimrec.symmetricCodeBound (2 * f.rootBound),
        ∃ nc < QuinticRadicalPrimrec.symmetricCodeBound (f.rootBound ^ 2),
          f.quadraticRemainderZero (ofNat ℤ nb) (ofNat ℤ nc) :=
    QuinticRadicalPrimrec.primrecPred_exists₂_lt htest hb hc
  exact hp.decide.of_eq fun f ↦ by
    rw [show f.hasBoundedQuadraticFactor = decide
      (∃ b ∈ symmetricInterval (2 * f.rootBound),
        ∃ c ∈ symmetricInterval (f.rootBound ^ 2),
          f.quadraticRemainderZero b c) by rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact exists_code_quadratic_iff f

theorem hasBoundedCubicFactor_primrec : Primrec hasBoundedCubicFactor := by
  have hdecode : Primrec fun n : ℕ ↦ ofNat ℤ n := Primrec.ofNat ℤ
  have hmap : Primrec fun q : ℕ × (ℕ × (ℕ × MonicSextic)) ↦
      (q.2.2.2,
        (ofNat ℤ q.2.2.1, (ofNat ℤ q.2.1, ofNat ℤ q.1))) :=
    Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) <|
      Primrec.pair
        (hdecode.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))) <|
      Primrec.pair
        (hdecode.comp (Primrec.fst.comp Primrec.snd))
        (hdecode.comp Primrec.fst)
  have htest : PrimrecPred fun q : ℕ × (ℕ × (ℕ × MonicSextic)) ↦
      q.2.2.2.cubicRemainderZero (ofNat ℤ q.2.2.1)
        (ofNat ℤ q.2.1) (ofNat ℤ q.1) :=
    cubicRemainderZero_primrec.comp hmap
  have hr2 : Primrec fun f : MonicSextic ↦ f.rootBound ^ 2 :=
    (Primrec.nat_mul.comp rootBound_primrec rootBound_primrec).of_eq
      fun f ↦ by simp [pow_two]
  have hr3 : Primrec fun f : MonicSextic ↦ f.rootBound ^ 3 :=
    (Primrec.nat_mul.comp
      (Primrec.nat_mul.comp rootBound_primrec rootBound_primrec)
      rootBound_primrec).of_eq fun f ↦ by ring
  have hbRadius : Primrec fun f : MonicSextic ↦ 3 * f.rootBound :=
    Primrec.nat_mul.comp (Primrec.const 3) rootBound_primrec
  have hcRadius : Primrec fun f : MonicSextic ↦ 3 * f.rootBound ^ 2 :=
    Primrec.nat_mul.comp (Primrec.const 3) hr2
  have hb : Primrec fun f : MonicSextic ↦
      QuinticRadicalPrimrec.symmetricCodeBound (3 * f.rootBound) :=
    QuinticRadicalPrimrec.symmetricCodeBound_primrec.comp hbRadius
  have hc : Primrec fun p : ℕ × MonicSextic ↦
      QuinticRadicalPrimrec.symmetricCodeBound (3 * p.2.rootBound ^ 2) :=
    (QuinticRadicalPrimrec.symmetricCodeBound_primrec.comp hcRadius).comp
      Primrec.snd
  have hd : Primrec fun p : ℕ × (ℕ × MonicSextic) ↦
      QuinticRadicalPrimrec.symmetricCodeBound (p.2.2.rootBound ^ 3) :=
    (QuinticRadicalPrimrec.symmetricCodeBound_primrec.comp hr3).comp
      (Primrec.snd.comp Primrec.snd)
  have hExistsD : PrimrecPred fun p : ℕ × (ℕ × MonicSextic) ↦
      ∃ nd < QuinticRadicalPrimrec.symmetricCodeBound (p.2.2.rootBound ^ 3),
        p.2.2.cubicRemainderZero (ofNat ℤ p.2.1)
          (ofNat ℤ p.1) (ofNat ℤ nd) :=
    QuinticRadicalPrimrec.primrecPred_exists_lt
      (α := ℕ × (ℕ × MonicSextic))
      (R := fun nd p ↦ p.2.2.cubicRemainderZero
        (ofNat ℤ p.2.1) (ofNat ℤ p.1) (ofNat ℤ nd)) htest hd
  have hExistsC : PrimrecPred fun p : ℕ × MonicSextic ↦
      ∃ nc < QuinticRadicalPrimrec.symmetricCodeBound (3 * p.2.rootBound ^ 2),
        ∃ nd < QuinticRadicalPrimrec.symmetricCodeBound (p.2.rootBound ^ 3),
          p.2.cubicRemainderZero (ofNat ℤ p.1)
            (ofNat ℤ nc) (ofNat ℤ nd) :=
    QuinticRadicalPrimrec.primrecPred_exists_lt
      (α := ℕ × MonicSextic)
      (R := fun nc p ↦
        ∃ nd < QuinticRadicalPrimrec.symmetricCodeBound (p.2.rootBound ^ 3),
          p.2.cubicRemainderZero (ofNat ℤ p.1)
            (ofNat ℤ nc) (ofNat ℤ nd)) hExistsD hc
  have hp : PrimrecPred fun f : MonicSextic ↦
      ∃ nb < QuinticRadicalPrimrec.symmetricCodeBound (3 * f.rootBound),
        ∃ nc < QuinticRadicalPrimrec.symmetricCodeBound (3 * f.rootBound ^ 2),
          ∃ nd < QuinticRadicalPrimrec.symmetricCodeBound (f.rootBound ^ 3),
            f.cubicRemainderZero (ofNat ℤ nb) (ofNat ℤ nc) (ofNat ℤ nd) :=
    QuinticRadicalPrimrec.primrecPred_exists_lt
      (α := MonicSextic)
      (R := fun nb f ↦
        ∃ nc < QuinticRadicalPrimrec.symmetricCodeBound (3 * f.rootBound ^ 2),
          ∃ nd < QuinticRadicalPrimrec.symmetricCodeBound (f.rootBound ^ 3),
            f.cubicRemainderZero (ofNat ℤ nb) (ofNat ℤ nc) (ofNat ℤ nd))
      hExistsC hb
  exact hp.decide.of_eq fun f ↦ by
    rw [show f.hasBoundedCubicFactor = decide
      (∃ b ∈ symmetricInterval (3 * f.rootBound),
        ∃ c ∈ symmetricInterval (3 * f.rootBound ^ 2),
          ∃ d ∈ symmetricInterval (f.rootBound ^ 3),
            f.cubicRemainderZero b c d) by rfl]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact exists_code_cubic_iff f

theorem hasBoundedNonlinearFactor_primrec :
    Primrec hasBoundedNonlinearFactor :=
  (Primrec.or.comp hasBoundedQuadraticFactor_primrec
    hasBoundedCubicFactor_primrec).of_eq fun _ ↦ rfl

theorem hasBoundedProperFactor_primrec : Primrec hasBoundedProperFactor :=
  (Primrec.or.comp hasBoundedLinearFactor_primrec
    hasBoundedNonlinearFactor_primrec).of_eq fun _ ↦ rfl

end SexticRadicalDecidability.MonicSextic

end LeanProofs.PolynomialFormulas
