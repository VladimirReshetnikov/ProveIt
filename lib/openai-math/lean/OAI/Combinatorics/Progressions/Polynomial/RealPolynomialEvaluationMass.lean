/- Modified for ProveIt: import Lean 4.32 compatibility declarations and
simplify polynomial coefficient addition explicitly. Statements unchanged. -/
import OAI.Compat.BigOperators
import OAI.Compat.MvPolynomial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def realPolynomialMass {I : Type*} (p : MvPolynomial I ℝ) : ℝ :=
  ∑ m ∈ p.support, |p.coeff m|

theorem realPolynomialMass_nonneg {I : Type*} (p : MvPolynomial I ℝ) : 0 ≤ realPolynomialMass p :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem realPolynomialMass_zero {I : Type*} : realPolynomialMass (0 : MvPolynomial I ℝ) = 0 := by
  simp [realPolynomialMass]

theorem realPolynomialMass_monomial {I : Type*} (m : I →₀ ℕ) (c : ℝ) :
    realPolynomialMass (MvPolynomial.monomial m c) = |c| := by
  classical
  by_cases hc : c = 0 <;> simp [realPolynomialMass, MvPolynomial.support_monomial, hc]

theorem realPolynomialMass_C {I : Type*} (c : ℝ) :
    realPolynomialMass (MvPolynomial.C c : MvPolynomial I ℝ) = |c| :=
  realPolynomialMass_monomial 0 c

theorem realPolynomialMass_X {I : Type*} (i : I) :
    realPolynomialMass (MvPolynomial.X i : MvPolynomial I ℝ) = 1 := by
  simpa only [MvPolynomial.X, abs_one] using realPolynomialMass_monomial (Finsupp.single i 1) 1

theorem realPolynomialMass_one {I : Type*} : realPolynomialMass (1 : MvPolynomial I ℝ) = 1 := by
  simpa only [map_one, abs_one] using (realPolynomialMass_C (I := I) 1)

theorem realPolynomialMass_eq_sum_of_support_subset {I : Type*}
    (p : MvPolynomial I ℝ) (s : Finset (I →₀ ℕ)) (hs : p.support ⊆ s) :
    realPolynomialMass p = ∑ m ∈ s, |p.coeff m| := by
  classical
  apply Finset.sum_subset hs
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.mp hm, abs_zero]

theorem realPolynomialMass_coeff_le {I : Type*} (p : MvPolynomial I ℝ) (m : I →₀ ℕ) :
    |p.coeff m| ≤ realPolynomialMass p := by
  classical
  by_cases hm : m ∈ p.support
  · exact Finset.single_le_sum (fun n _ => abs_nonneg (p.coeff n)) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm, abs_zero]
    exact realPolynomialMass_nonneg p

theorem realPolynomialMass_add_le {I : Type*} (p q : MvPolynomial I ℝ) :
    realPolynomialMass (p + q) ≤ realPolynomialMass p + realPolynomialMass q := by
  classical
  rw [realPolynomialMass_eq_sum_of_support_subset (p + q) (p.support ∪ q.support)
    (MvPolynomial.support_add),
    realPolynomialMass_eq_sum_of_support_subset p (p.support ∪ q.support) Finset.subset_union_left,
    realPolynomialMass_eq_sum_of_support_subset q (p.support ∪ q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun monomial _ => by
    simpa only [MvPolynomial.coeff_add] using
      abs_add_le (p.coeff monomial) (q.coeff monomial))

theorem realPolynomialMass_sum_le {I J : Type*} (s : Finset J) (p : J → MvPolynomial I ℝ) :
    realPolynomialMass (∑ j ∈ s, p j) ≤ ∑ j ∈ s, realPolynomialMass (p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, realPolynomialMass_zero, le_refl]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact (realPolynomialMass_add_le _ _).trans (add_le_add le_rfl ih)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realPolynomialMass_mul_le {I : Type*} (p q : MvPolynomial I ℝ) :
    realPolynomialMass (p * q) ≤ realPolynomialMass p * realPolynomialMass q := by
  classical
  have he : p * q = ∑ m ∈ p.support, ∑ n ∈ q.support,
      MvPolynomial.monomial (m + n) (p.coeff m * q.coeff n) := by
    conv_lhs => rw [p.as_sum, q.as_sum]
    simp only [Finset.sum_mul, Finset.mul_sum, MvPolynomial.monomial_mul_monomial]
    exact Finset.sum_comm
  rw [he]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ m ∈ p.support, ∑ n ∈ q.support,
        realPolynomialMass (MvPolynomial.monomial (m + n) (p.coeff m * q.coeff n)) :=
      Finset.sum_le_sum (fun _ _ => realPolynomialMass_sum_le _ _)
    _ = realPolynomialMass p * realPolynomialMass q := by
      simp_rw [realPolynomialMass_monomial]
      simp only [abs_mul, realPolynomialMass,
        Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

theorem realPolynomialMass_prod_le {I J : Type*} (s : Finset J) (p : J → MvPolynomial I ℝ) :
    realPolynomialMass (∏ j ∈ s, p j) ≤ ∏ j ∈ s, realPolynomialMass (p j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, realPolynomialMass_one, le_refl]
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact (realPolynomialMass_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (realPolynomialMass_nonneg _))

theorem realPolynomialMass_pow_le {I : Type*} (p : MvPolynomial I ℝ) (n : ℕ) :
    realPolynomialMass (p ^ n) ≤ realPolynomialMass p ^ n := by
  induction n with
  | zero => simp only [pow_zero, realPolynomialMass_one, le_refl]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (realPolynomialMass_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (realPolynomialMass_nonneg _))

theorem realPolynomialMass_C_mul_le {I : Type*} (c : ℝ) (p : MvPolynomial I ℝ) :
    realPolynomialMass (MvPolynomial.C c * p) ≤ |c| * realPolynomialMass p := by
  simpa only [realPolynomialMass_C] using realPolynomialMass_mul_le (MvPolynomial.C c) p

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

theorem polynomialFunctional_expansion {σ R : Type*} [CommRing R]
    (L : MvPolynomial σ R →ₗ[R] R) (P : MvPolynomial σ R) :
    L P = ∑ d ∈ P.support, P.coeff d * L (monomial d 1) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  have he : monomial d (P.coeff d) = P.coeff d • monomial d (1 : R) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul, smul_eq_mul]

theorem polynomialFunctional_map_expansion {σ R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (L : MvPolynomial σ S →ₗ[S] S) (P : MvPolynomial σ R) :
    L (map ρ P) = ∑ d ∈ P.support, ρ (P.coeff d) * L (monomial d 1) := by
  conv_lhs => rw [P.as_sum]
  simp only [map_sum, map_monomial]
  apply Finset.sum_congr rfl
  intro d _
  have he : monomial d (ρ (P.coeff d)) = ρ (P.coeff d) • monomial d (1 : S) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [he, map_smul, smul_eq_mul]

theorem polynomialFunctional_le_mass {σ : Type*}
    (L : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) (P : MvPolynomial σ ℝ) {C : ℝ}
    (hL : ∀ d ∈ P.support, |L (monomial d 1)| ≤ C) :
    |L P| ≤ C * realPolynomialMass P := by
  rw [polynomialFunctional_expansion]
  calc
    _ ≤ ∑ d ∈ P.support, |P.coeff d * L (monomial d 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ P.support, C * |P.coeff d| := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul, mul_comm C]
      exact mul_le_mul_of_nonneg_left (hL d hd) (abs_nonneg _)
    _ = C * realPolynomialMass P := by rw [realPolynomialMass, Finset.mul_sum]

theorem polynomialFunctional_homogeneous_le_mass {σ : Type*}
    (L : MvPolynomial σ ℝ →ₗ[ℝ] ℝ) {P : MvPolynomial σ ℝ} {h : ℕ}
    (hP : P.IsHomogeneous h) {C : ℝ}
    (hL : ∀ d : σ →₀ ℕ, d.degree = h → |L (monomial d 1)| ≤ C) :
    |L P| ≤ C * realPolynomialMass P :=
  polynomialFunctional_le_mass L P (fun d hd => hL d
    (by simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hP (mem_support_iff.mp hd)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem realPolynomialMass_substitution_le {I J : Type*}
    (p : MvPolynomial I ℝ) (f : I → MvPolynomial J ℝ) {M : ℝ} (hM : 1 ≤ M)
    (hf : ∀ i, realPolynomialMass (f i) ≤ M) {d : ℕ} (hd : p.totalDegree ≤ d) :
    realPolynomialMass (MvPolynomial.eval₂Hom MvPolynomial.C f p) ≤
      realPolynomialMass p * M ^ d := by
  classical
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  calc
    _ ≤ ∑ m ∈ p.support, realPolynomialMass
        (MvPolynomial.C (p.coeff m) * ∏ i ∈ m.support, f i ^ m i) :=
      realPolynomialMass_sum_le _ _
    _ ≤ ∑ m ∈ p.support, |p.coeff m| * M ^ d := by
      apply Finset.sum_le_sum
      intro m hm
      apply (realPolynomialMass_C_mul_le _ _).trans
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ ≤ ∏ i ∈ m.support, realPolynomialMass (f i ^ m i) := realPolynomialMass_prod_le _ _
        _ ≤ ∏ i ∈ m.support, M ^ m i := by
          apply Finset.prod_le_prod₀ (fun _ _ => realPolynomialMass_nonneg _)
          intro i _
          exact (realPolynomialMass_pow_le _ _).trans
            (pow_le_pow_left₀ (realPolynomialMass_nonneg _) (hf i) _)
        _ = M ^ (m.sum fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
        _ ≤ M ^ d := pow_le_pow_right₀ hM ((MvPolynomial.le_totalDegree hm).trans hd)
    _ = realPolynomialMass p * M ^ d := by rw [← Finset.sum_mul]; rfl

theorem polynomial_substitution_totalDegree_le {I J : Type*}
    (p : MvPolynomial I ℝ) (f : I → MvPolynomial J ℝ) {e d : ℕ}
    (hf : ∀ i, (f i).totalDegree ≤ e) (hd : p.totalDegree ≤ d) :
    (MvPolynomial.eval₂Hom MvPolynomial.C f p).totalDegree ≤ d * e := by
  classical
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  apply (MvPolynomial.totalDegree_mul _ _).trans
  simp only [MvPolynomial.totalDegree_C, zero_add]
  calc
    _ ≤ ∑ i ∈ m.support, (f i ^ m i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ m.support, m i * e := Finset.sum_le_sum (fun i _ =>
      (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hf i)))
    _ = (m.sum fun _ n => n) * e := by rw [← Finset.sum_mul]; rfl
    _ ≤ d * e := Nat.mul_le_mul_right _ ((MvPolynomial.le_totalDegree hm).trans hd)

theorem realPolynomialMass_rename_le {I J : Type*} (p : MvPolynomial I ℝ) (f : I → J) :
    realPolynomialMass (MvPolynomial.rename f p) ≤ realPolynomialMass p := by
  have he : (MvPolynomial.rename f : MvPolynomial I ℝ →ₐ[ℝ] MvPolynomial J ℝ).toRingHom =
      MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X (f i)) := by ext <;> simp
  change realPolynomialMass ((MvPolynomial.rename f).toRingHom p) ≤ _
  rw [he]
  have h := realPolynomialMass_substitution_le p (fun i => MvPolynomial.X (f i))
    (M := 1) le_rfl (fun i => (realPolynomialMass_X (f i)).le) le_rfl
  simpa only [one_pow, mul_one] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def polynomialMonomial {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) : MvPolynomial I ℝ :=
  ∏ k ∈ m.support, a k ^ m k

theorem polynomialMonomial_eval {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) (x : I → ℝ) :
    MvPolynomial.eval x (polynomialMonomial a m) =
      ∏ k ∈ m.support, MvPolynomial.eval x (a k) ^ m k := by
  simp only [polynomialMonomial, map_prod, map_pow]

theorem polynomialMonomial_mass_le {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) {M : ℝ}
    (ha : ∀ k ∈ m.support, realPolynomialMass (a k) ≤ M) :
    realPolynomialMass (polynomialMonomial a m) ≤ M ^ (m.sum fun _ n => n) := by
  classical
  apply (realPolynomialMass_prod_le _ _).trans
  calc
    _ ≤ ∏ k ∈ m.support, M ^ m k := by
      apply Finset.prod_le_prod₀ (fun _ _ => realPolynomialMass_nonneg _)
      intro k hk
      exact (realPolynomialMass_pow_le _ _).trans
        (pow_le_pow_left₀ (realPolynomialMass_nonneg _) (ha k hk) _)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum]; rfl

theorem polynomialMonomial_totalDegree_le {K I : Type*}
    (a : K → MvPolynomial I ℝ) (m : K →₀ ℕ) {e : ℕ}
    (ha : ∀ k ∈ m.support, (a k).totalDegree ≤ e) :
    (polynomialMonomial a m).totalDegree ≤ (m.sum fun _ n => n) * e := by
  classical
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ k ∈ m.support, m k * e := Finset.sum_le_sum (fun k hk =>
      (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (ha k hk)))
    _ = _ := by rw [← Finset.sum_mul]; rfl

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

theorem realPolynomialMass_smul (c : ℝ) (P : MvPolynomial σ ℝ) :
    realPolynomialMass (c • P) = |c| * realPolynomialMass P := by
  classical
  by_cases hc : c = 0
  · simp [hc, realPolynomialMass_zero]
  · simp only [realPolynomialMass, support_smul_eq hc, coeff_smul,
      smul_eq_mul, abs_mul, Finset.mul_sum]

theorem realPolynomialMass_pderiv (i : σ) (P : MvPolynomial σ ℝ)
    {s : ℕ} (hP : P.totalDegree ≤ s) :
    realPolynomialMass (pderiv i P) ≤ s * realPolynomialMass P := by
  classical
  conv_lhs => rw [← P.support_sum_monomial_coeff, map_sum]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ P.support, s * |P.coeff a| := by
      apply Finset.sum_le_sum
      intro a ha
      rw [pderiv_monomial, realPolynomialMass_monomial, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (a i : ℝ) from Nat.cast_nonneg _)]
      have h : (a i : ℝ) ≤ s := by
        exact_mod_cast (monomial_le_degreeOf i ha).trans ((degreeOf_le_totalDegree P i).trans hP)
      nlinarith [abs_nonneg (P.coeff a)]
    _ = _ := by rw [realPolynomialMass, Finset.mul_sum]

theorem polynomialDerivation_eq_sum [Fintype σ]
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)) :
    D = ∑ i, D (X i) • pderiv i := by
  classical
  apply MvPolynomial.derivation_ext
  intro j
  change D (X j) = (Derivation.coeFnAddMonoidHom (∑ i, D (X i) • pderiv i)) (X j)
  rw [map_sum]
  simp [pderiv_X, smul_eq_mul, Pi.single_apply]

theorem realPolynomialMass_derivation [Fintype σ]
    (D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hD : ∀ i, realPolynomialMass (D (X i)) ≤ M)
    {P : MvPolynomial σ ℝ} {s : ℕ} (hP : P.totalDegree ≤ s) :
    realPolynomialMass (D P) ≤ (Fintype.card σ * M * s) * realPolynomialMass P := by
  classical
  have he : D P = ∑ i, D (X i) * pderiv i P := by
    conv_lhs => rw [polynomialDerivation_eq_sum D]
    change (Derivation.coeFnAddMonoidHom (∑ i, D (X i) • pderiv i)) P = _
    rw [map_sum]
    simp [smul_eq_mul]
  rw [he]
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : σ, M * (s * realPolynomialMass P) := by
      apply Finset.sum_le_sum
      intro i _
      exact (realPolynomialMass_mul_le _ _).trans
        (mul_le_mul (hD i) (realPolynomialMass_pderiv i P hP)
          (realPolynomialMass_nonneg _) hM)
    _ = _ := by simp; ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem abs_aeval_le_mass_box {σ : Type*} (P : MvPolynomial σ ℝ) (x : σ → ℝ)
    {B : ℝ} {n : ℕ} (hB : 1 ≤ B) (hx : ∀ i, |x i| ≤ B) (hP : P.totalDegree ≤ n) :
    |aeval x P| ≤ realPolynomialMass P * B ^ n := by
  classical
  change |P.eval₂ (RingHom.id ℝ) x| ≤ _
  rw [eval₂_eq]
  calc
    _ ≤ ∑ a ∈ P.support, |P.coeff a * ∏ i ∈ a.support, x i ^ a i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ P.support, |P.coeff a| * B ^ n := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        _ = ∏ i ∈ a.support, |x i| ^ a i := by simp only [abs_pow]
        _ ≤ ∏ i ∈ a.support, B ^ a i :=
          Finset.prod_le_prod₀ (fun _ _ => by positivity)
            (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hx i) _)
        _ = B ^ (a.sum fun _ m => m) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
        _ ≤ B ^ n := pow_le_pow_right₀ hB ((le_totalDegree ha).trans hP)
    _ = _ := by rw [← Finset.sum_mul]; rfl

end Erdos3

end

end OAI
