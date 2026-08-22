import ExponentialIdentities.TwoBaseIntegerExponent.RestrictedMatrixCoefficient
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# The formal prime-symbol determinant

For a positive natural number `n`, `primeFactorLinearForm n` is the formal logarithm

`sum_p v_p(n) X_p`.

The determinant

`X_2 * primeFactorLinearForm B - X_3 * primeFactorLinearForm A`

is the sparse quadratic obtained by replacing every prime logarithm in the restricted
logarithm matrix by an independent variable.  This file proves two facts from the formal
prime-symbol reduction:

* specializing `X_p` to `log p` recovers the restricted numerical determinant; and
* for positive `A` and `B`, the formal determinant is zero exactly when
  `A = 2 ^ m` and `B = 3 ^ m` for a common natural exponent `m`.

The coefficient extraction proof evaluates the polynomial at finitely supported Kronecker
assignments.  Thus it reasons about the actual `MvPolynomial`, without requiring a separate
normal form for unordered quadratic monomials.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open MvPolynomial

noncomputable section

/-- The formal prime-factorization logarithm `sum_p v_p(n) X_p`. -/
def primeFactorLinearForm (n : ℕ) : MvPolynomial ℕ ℤ :=
  n.factorization.sum fun p e ↦ C (e : ℤ) * X p

/-- The formal determinant `X_2 L_B - X_3 L_A`. -/
def formalPrimeDeterminant (A B : ℕ) : MvPolynomial ℕ ℤ :=
  X 2 * primeFactorLinearForm B - X 3 * primeFactorLinearForm A

/-- Evaluation of the formal factorization linear form is the corresponding finite dot
product with the valuation vector. -/
theorem primeFactorLinearForm_eval₂ {R : Type*} [CommRing R]
    (f : ℤ →+* R) (x : ℕ → R) (n : ℕ) :
    eval₂ f x (primeFactorLinearForm n) =
      n.factorization.sum fun p e ↦ f (e : ℤ) * x p := by
  classical
  simp [primeFactorLinearForm, Finsupp.sum]

/-- Substitution `X_p = log p` turns the formal factorization linear form into `log n`. -/
theorem primeFactorLinearForm_eval₂_log (n : ℕ) :
    eval₂ (Int.castRingHom ℝ) (fun p : ℕ ↦ Real.log p) (primeFactorLinearForm n) =
      Real.log n := by
  rw [primeFactorLinearForm_eval₂]
  simpa using (Real.log_nat_eq_sum_factorization n).symm

/-- Prime-log specialization of the formal polynomial is exactly the determinant of the
restricted logarithm matrix. -/
theorem formalPrimeDeterminant_eval₂_log (A B : ℕ) :
    eval₂ (Int.castRingHom ℝ) (fun p : ℕ ↦ Real.log p) (formalPrimeDeterminant A B) =
      restrictedLogDet A B := by
  simp [formalPrimeDeterminant, primeFactorLinearForm_eval₂_log, restrictedLogDet]
  ring

private def primeKronecker (q p : ℕ) : ℤ :=
  if p = q then 1 else 0

private theorem factorization_sum_primeKronecker (n q : ℕ) :
    n.factorization.sum (fun p e ↦ (e : ℤ) * primeKronecker q p) =
      (n.factorization q : ℤ) := by
  classical
  by_cases hq : q ∈ n.factorization.support
  · rw [Finsupp.sum, Finset.sum_eq_single q]
    · simp [primeKronecker]
    · intro p hp hpq
      simp [primeKronecker, hpq]
    · exact fun h ↦ (h hq).elim
  · have hz : n.factorization q = 0 := Finsupp.notMem_support_iff.mp hq
    rw [hz, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro p hp
    have hpq : p ≠ q := fun hpq ↦ hq (hpq ▸ hp)
    simp [primeKronecker, hpq]

private theorem primeFactorLinearForm_eval_primeKronecker (n q : ℕ) :
    eval (primeKronecker q) (primeFactorLinearForm n) =
      (n.factorization q : ℤ) := by
  change eval₂ (RingHom.id ℤ) (primeKronecker q) (primeFactorLinearForm n) = _
  rw [primeFactorLinearForm_eval₂]
  exact factorization_sum_primeKronecker n q

private theorem primeFactorLinearForm_eval_add_primeKronecker (n q r : ℕ) :
    eval (primeKronecker q + primeKronecker r) (primeFactorLinearForm n) =
      (n.factorization q : ℤ) + (n.factorization r : ℤ) := by
  change eval₂ (RingHom.id ℤ) (primeKronecker q + primeKronecker r)
    (primeFactorLinearForm n) = _
  rw [primeFactorLinearForm_eval₂]
  calc
    n.factorization.sum
          (fun p e ↦ (e : ℤ) * (primeKronecker q + primeKronecker r) p) =
        n.factorization.sum (fun p e ↦ (e : ℤ) * primeKronecker q p) +
          n.factorization.sum (fun p e ↦ (e : ℤ) * primeKronecker r p) := by
            simp [Finsupp.sum, mul_add, Finset.sum_add_distrib]
    _ = (n.factorization q : ℤ) + (n.factorization r : ℤ) := by
      rw [factorization_sum_primeKronecker, factorization_sum_primeKronecker]

private theorem factorization_eq_single_of_eq_zero_off
    {n p m : ℕ} (hm : n.factorization p = m)
    (hoff : ∀ q : ℕ, q ≠ p → n.factorization q = 0) :
    n.factorization = Finsupp.single p m := by
  ext q
  by_cases hq : q = p
  · subst q
    simp [hm]
  · rw [hoff q hq, Finsupp.single_apply, if_neg (Ne.symm hq)]

/-- **Formal vanishing classification.**  For positive integral outputs, the formal
prime-symbol determinant vanishes exactly for the trivial common-power pairs. -/
theorem formalPrimeDeterminant_eq_zero_iff
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) :
    formalPrimeDeterminant A B = 0 ↔
      ∃ m : ℕ, A = 2 ^ m ∧ B = 3 ^ m := by
  constructor
  · intro hzero
    have hBtwoInt : (B.factorization 2 : ℤ) = 0 := by
      have h := congrArg (eval (primeKronecker 2)) hzero
      simpa [formalPrimeDeterminant, primeFactorLinearForm_eval_primeKronecker,
        primeKronecker] using h
    have hAthreeInt : (A.factorization 3 : ℤ) = 0 := by
      have h := congrArg (eval (primeKronecker 3)) hzero
      simpa [formalPrimeDeterminant, primeFactorLinearForm_eval_primeKronecker,
        primeKronecker] using h
    have hBtwo : B.factorization 2 = 0 := by exact_mod_cast hBtwoInt
    have hAthree : A.factorization 3 = 0 := by exact_mod_cast hAthreeInt
    have hBother : ∀ p : ℕ, p ≠ 2 → p ≠ 3 → B.factorization p = 0 := by
      intro p hp2 hp3
      have h := congrArg (eval (primeKronecker 2 + primeKronecker p)) hzero
      have hInt : (B.factorization 2 : ℤ) + (B.factorization p : ℤ) = 0 := by
        simpa [formalPrimeDeterminant, primeFactorLinearForm_eval_add_primeKronecker,
          primeKronecker, hp2, hp3, Ne.symm hp2, Ne.symm hp3] using h
      rw [hBtwoInt, zero_add] at hInt
      exact_mod_cast hInt
    have hAother : ∀ p : ℕ, p ≠ 2 → p ≠ 3 → A.factorization p = 0 := by
      intro p hp2 hp3
      have h := congrArg (eval (primeKronecker 3 + primeKronecker p)) hzero
      have hInt : -((A.factorization 3 : ℤ) + (A.factorization p : ℤ)) = 0 := by
        simpa [formalPrimeDeterminant, primeFactorLinearForm_eval_add_primeKronecker,
          primeKronecker, hp2, hp3, Ne.symm hp2, Ne.symm hp3] using h
      rw [hAthreeInt, zero_add, neg_eq_zero] at hInt
      exact_mod_cast hInt
    have hcrossInt :
        (B.factorization 2 : ℤ) + (B.factorization 3 : ℤ) -
            ((A.factorization 2 : ℤ) + (A.factorization 3 : ℤ)) = 0 := by
      have h := congrArg (eval (primeKronecker 2 + primeKronecker 3)) hzero
      simpa [formalPrimeDeterminant, primeFactorLinearForm_eval_add_primeKronecker,
        primeKronecker] using h
    have hcrossInt' : (B.factorization 3 : ℤ) = (A.factorization 2 : ℤ) := by
      rw [hBtwoInt, zero_add, hAthreeInt, add_zero, sub_eq_zero] at hcrossInt
      exact hcrossInt
    have hcross : B.factorization 3 = A.factorization 2 := by
      exact_mod_cast hcrossInt'
    let m := A.factorization 2
    have hAoff : ∀ p : ℕ, p ≠ 2 → A.factorization p = 0 := by
      intro p hp2
      by_cases hp3 : p = 3
      · subst p
        exact hAthree
      · exact hAother p hp2 hp3
    have hBoff : ∀ p : ℕ, p ≠ 3 → B.factorization p = 0 := by
      intro p hp3
      by_cases hp2 : p = 2
      · subst p
        exact hBtwo
      · exact hBother p hp2 hp3
    have hAfactorization : A.factorization = Finsupp.single 2 m :=
      factorization_eq_single_of_eq_zero_off rfl hAoff
    have hBfactorization : B.factorization = Finsupp.single 3 m :=
      factorization_eq_single_of_eq_zero_off hcross hBoff
    refine ⟨m, Nat.eq_pow_of_factorization_eq_single hA.ne' hAfactorization,
      Nat.eq_pow_of_factorization_eq_single hB.ne' hBfactorization⟩
  · rintro ⟨m, rfl, rfl⟩
    simp only [formalPrimeDeterminant, primeFactorLinearForm]
    rw [(by norm_num : Nat.Prime 2).factorization_pow,
      (by norm_num : Nat.Prime 3).factorization_pow]
    simp [Finsupp.sum_single_index]
    ring

/-- The sparse Structural Rank statement needed here: whenever prime-log specialization makes
one of the signed valuation determinants vanish, the formal polynomial was already zero. -/
def SparsePrimeLogStructuralRankPrinciple : Prop :=
  ∀ A B : ℕ, 0 < A → 0 < B →
    eval₂ (Int.castRingHom ℝ) (fun p : ℕ ↦ Real.log p) (formalPrimeDeterminant A B) = 0 →
      formalPrimeDeterminant A B = 0

/-- **Sparse Structural Rank formulation of Alaoglu--Erdos.**  The two-base conjecture is
equivalent to the assertion that prime-log specialization cannot annihilate a nonzero formal
determinant of the signed valuation form `X_2 L_B - X_3 L_A`. -/
theorem alaogluErdosConjecture_iff_sparsePrimeLogStructuralRankPrinciple :
    AlaogluErdosConjecture ↔ SparsePrimeLogStructuralRankPrinciple := by
  constructor
  · intro hAE A B hA hB hspecial
    have hdet : restrictedLogDet A B = 0 := by
      rw [← formalPrimeDeterminant_eval₂_log]
      exact hspecial
    obtain ⟨β, hAβ, hBβ⟩ :=
      (restrictedLogDet_eq_zero_iff_exists_commonExponent hA hB).mp hdet
    have htwo : (2 : ℝ) ^ β ∈ Set.range ((↑) : ℤ → ℝ) := by
      refine ⟨(A : ℤ), ?_⟩
      exact_mod_cast hAβ
    have hthree : (3 : ℝ) ^ β ∈ Set.range ((↑) : ℤ → ℝ) := by
      refine ⟨(B : ℤ), ?_⟩
      exact_mod_cast hBβ
    obtain ⟨z, hz⟩ := hAE htwo hthree
    have hβnonneg : 0 ≤ β := IntegerExponent.nonneg_of_two_rpow_integer htwo
    have hznonneg : 0 ≤ z := by
      rw [← hz] at hβnonneg
      exact_mod_cast hβnonneg
    let m : ℕ := z.toNat
    have hmInt : (m : ℤ) = z := Int.toNat_of_nonneg hznonneg
    have hmReal : (m : ℝ) = β := by
      calc
        (m : ℝ) = (z : ℝ) := by exact_mod_cast hmInt
        _ = β := hz
    have hAeq : A = 2 ^ m := by
      apply Nat.cast_injective (R := ℝ)
      rw [Nat.cast_pow]
      calc
        (A : ℝ) = (2 : ℝ) ^ β := hAβ
        _ = (2 : ℝ) ^ (m : ℝ) := by rw [hmReal]
        _ = (2 : ℝ) ^ m := Real.rpow_natCast 2 m
    have hBeq : B = 3 ^ m := by
      apply Nat.cast_injective (R := ℝ)
      rw [Nat.cast_pow]
      calc
        (B : ℝ) = (3 : ℝ) ^ β := hBβ
        _ = (3 : ℝ) ^ (m : ℝ) := by rw [hmReal]
        _ = (3 : ℝ) ^ m := Real.rpow_natCast 3 m
    exact (formalPrimeDeterminant_eq_zero_iff hA hB).mpr ⟨m, hAeq, hBeq⟩
  · intro hSR x htwo hthree
    obtain ⟨zA, hzA⟩ := htwo
    obtain ⟨zB, hzB⟩ := hthree
    have hzApos : 0 < zA := by
      exact_mod_cast (hzA.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) x)
    have hzBpos : 0 < zB := by
      exact_mod_cast (hzB.symm ▸ Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) x)
    lift zA to ℕ using hzApos.le with A hAcast
    lift zB to ℕ using hzBpos.le with B hBcast
    have hApos : 0 < A := by exact_mod_cast hzApos
    have hBpos : 0 < B := by exact_mod_cast hzBpos
    have hAx : (A : ℝ) = (2 : ℝ) ^ x := by exact_mod_cast hzA
    have hBx : (B : ℝ) = (3 : ℝ) ^ x := by exact_mod_cast hzB
    have hdet : restrictedLogDet A B = 0 :=
      (restrictedLogDet_eq_zero_iff_exists_commonExponent hApos hBpos).mpr
        ⟨x, hAx, hBx⟩
    have hspecial :
        eval₂ (Int.castRingHom ℝ) (fun p : ℕ ↦ Real.log p)
            (formalPrimeDeterminant A B) = 0 := by
      rw [formalPrimeDeterminant_eval₂_log]
      exact hdet
    have hformal := hSR A B hApos hBpos hspecial
    obtain ⟨m, hAeq, _hBeq⟩ :=
      (formalPrimeDeterminant_eq_zero_iff hApos hBpos).mp hformal
    have hxm : x = (m : ℝ) := by
      apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
      change (2 : ℝ) ^ x = (2 : ℝ) ^ (m : ℝ)
      rw [← hAx, hAeq, Real.rpow_natCast]
      push_cast
      rfl
    refine ⟨(m : ℤ), ?_⟩
    exact_mod_cast hxm.symm

end

end LeanProofs.TwoBaseIntegerExponent
