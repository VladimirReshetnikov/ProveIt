-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Derivative
import OAI.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
import OAI.Compat.MvPolynomial

namespace OAI

section

namespace Erdos3

open MvPolynomial
open scoped Pointwise

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialTranslate (h : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (fun i => X i + C (h i))

@[simp] theorem polynomialTranslate_X (h : σ → R) (i : σ) :
    polynomialTranslate h (X i) = X i + C (h i) := by simp [polynomialTranslate]

@[simp] theorem polynomialTranslate_C (h : σ → R) (r : R) :
    polynomialTranslate h (C r) = C r := by simp [polynomialTranslate]

noncomputable def weightedSupportLE (w : σ → ℕ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {α | Finsupp.weight w α ≤ d}

noncomputable def weightedSupportLT (w : σ → ℕ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {α | Finsupp.weight w α < d}

theorem weightedSupportLE_monomial (w : σ → ℕ) (α : σ →₀ ℕ) (r : R) :
    monomial α r ∈ weightedSupportLE w (Finsupp.weight w α) := by
  apply (monomial_mem_restrictSupport R).mpr
  left
  change Finsupp.weight w α ≤ Finsupp.weight w α
  exact le_rfl

theorem weightedSupportLE_mul {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (hq : q ∈ weightedSupportLE w e) :
    p * q ∈ weightedSupportLE w (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  exact (map_add (Finsupp.weight w) β γ).trans_le (Nat.add_le_add (hp hβ) (hq hγ))

theorem weightedSupportLT_mul_LE {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w d) (hq : q ∈ weightedSupportLE w e) :
    p * q ∈ weightedSupportLT w (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  exact (map_add (Finsupp.weight w) β γ).trans_lt (Nat.add_lt_add_of_lt_of_le (hp hβ) (hq hγ))

theorem weightedSupportLE_mul_LT {w : σ → ℕ} {d e : ℕ} {p q : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (hq : q ∈ weightedSupportLT w e) :
    p * q ∈ weightedSupportLT w (d + e) := by
  rw [mul_comm, Nat.add_comm]
  exact weightedSupportLT_mul_LE hq hp

private theorem translation_bounds_mul (h : σ → R) (w : σ → ℕ)
    (p q : MvPolynomial σ R) (d e : ℕ)
    (hp : p ∈ weightedSupportLE w d)
    (htp : polynomialTranslate h p ∈ weightedSupportLE w d)
    (htq : polynomialTranslate h q ∈ weightedSupportLE w e)
    (hdp : polynomialTranslate h p - p ∈ weightedSupportLT w d)
    (hdq : polynomialTranslate h q - q ∈ weightedSupportLT w e) :
    polynomialTranslate h (p * q) ∈ weightedSupportLE w (d + e) ∧
      polynomialTranslate h (p * q) - p * q ∈ weightedSupportLT w (d + e) := by
  refine ⟨by rw [map_mul]; exact weightedSupportLE_mul htp htq, ?_⟩
  rw [map_mul, show polynomialTranslate h p * polynomialTranslate h q - p * q =
    (polynomialTranslate h p - p) * polynomialTranslate h q + p * (polynomialTranslate h q - q) by ring]
  exact (weightedSupportLT w (d + e)).add_mem (weightedSupportLT_mul_LE hdp htq)
    (weightedSupportLE_mul_LT hp hdq)

theorem polynomialTranslate_monomial_bounds (h : σ → R) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) ∈ weightedSupportLE w (Finsupp.weight w α) ∧
      polynomialTranslate h (monomial α 1) - monomial α 1 ∈
        weightedSupportLT w (Finsupp.weight w α) := by
  classical
  have hX (i : σ) : polynomialTranslate h (X i) ∈ weightedSupportLE w (w i) ∧
      polynomialTranslate h (X i) - X i ∈ weightedSupportLT w (w i) := by
    have hi : (X i : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
      simpa only [X, Finsupp.weight_single, one_smul] using weightedSupportLE_monomial w (Finsupp.single i 1) (1 : R)
    have hc : (C (h i) : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
      exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simp))
    refine ⟨by rw [polynomialTranslate_X]; exact (weightedSupportLE w _).add_mem hi hc, ?_⟩
    rw [polynomialTranslate_X, add_sub_cancel_left]
    exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simpa using hw i))
  have hsingle (i : σ) (n : ℕ) :
      polynomialTranslate h (monomial (Finsupp.single i n) 1) ∈ weightedSupportLE w (n * w i) ∧
      polynomialTranslate h (monomial (Finsupp.single i n) 1) - monomial (Finsupp.single i n) 1 ∈
        weightedSupportLT w (n * w i) := by
    induction n with
    | zero =>
      rw [Finsupp.single_zero, zero_mul]
      change polynomialTranslate h 1 ∈ weightedSupportLE w 0 ∧
        polynomialTranslate h 1 - 1 ∈ weightedSupportLT w 0
      rw [map_one, sub_self]
      exact ⟨by simpa using weightedSupportLE_monomial w (0 : σ →₀ ℕ) (1 : R), Submodule.zero_mem _⟩
    | succ n ih =>
      have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
      simp only [Finsupp.weight_single, smul_eq_mul] at hp
      have hh := translation_bounds_mul h w (monomial (Finsupp.single i n) 1) (X i)
        (n * w i) (w i) hp ih.1 (hX i).1 ih.2 (hX i).2
      simpa only [X, monomial_mul_monomial, one_mul, ← Finsupp.single_add, Nat.succ_mul] using hh
  induction α using Finsupp.induction with
  | zero =>
    change polynomialTranslate h 1 ∈ weightedSupportLE w 0 ∧
      polynomialTranslate h 1 - 1 ∈ weightedSupportLT w 0
    rw [map_one, sub_self]
    exact ⟨by simpa using weightedSupportLE_monomial w (0 : σ →₀ ℕ) (1 : R), Submodule.zero_mem _⟩
  | @single_add i n α hi hn ih =>
    have hp := weightedSupportLE_monomial w (Finsupp.single i n) (1 : R)
    have hh := translation_bounds_mul h w (monomial (Finsupp.single i n) 1) (monomial α 1)
      (Finsupp.weight w (Finsupp.single i n)) (Finsupp.weight w α) hp
      (by simpa only [Finsupp.weight_single, smul_eq_mul] using (hsingle i n).1) ih.1
      (by simpa only [Finsupp.weight_single, smul_eq_mul] using (hsingle i n).2) ih.2
    simpa only [monomial_mul_monomial, one_mul, map_add] using hh

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Pointwise

variable {σ : Type*}

noncomputable def polynomialDegreeGap (k d : ℕ) : Submodule ℚ (MvPolynomial σ ℚ) :=
  MvPolynomial.restrictSupport ℚ {α | Finsupp.weight (fun _ => 1) α + k ≤ d}

theorem polynomialDegreeGap_monomial (α : σ →₀ ℕ) (c : ℚ) :
    monomial α c ∈ polynomialDegreeGap 0 (Finsupp.weight (fun _ => 1) α) :=
  (monomial_mem_restrictSupport ℚ).mpr (Or.inl (by simp))

theorem polynomialDegreeGap_mul {i j d e : ℕ} {p q : MvPolynomial σ ℚ}
    (hp : p ∈ polynomialDegreeGap i d) (hq : q ∈ polynomialDegreeGap j e) :
    p * q ∈ polynomialDegreeGap (i + j) (d + e) := by
  classical
  intro α hα
  obtain ⟨β, hβ, γ, hγ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hα)
  have hb := hp hβ
  have hc := hq hγ
  change Finsupp.weight (fun _ : σ => 1) β + i ≤ d at hb
  change Finsupp.weight (fun _ : σ => 1) γ + j ≤ e at hc
  change Finsupp.weight (fun _ : σ => 1) (β + γ) + (i + j) ≤ d + e
  rw [map_add]
  omega

theorem polynomialDegreeGap_pderiv {k d : ℕ} {p : MvPolynomial σ ℚ}
    (hp : p ∈ polynomialDegreeGap k d) (i : σ) :
    MvPolynomial.pderiv i p ∈ polynomialDegreeGap (k + 1) d := by
  classical
  intro α hα
  change α ∈ (MvPolynomial.pderiv i p).support at hα
  have hn : p.coeff (α + Finsupp.single i 1) ≠ 0 := by
    intro hz
    have hc : (MvPolynomial.pderiv i p).coeff α ≠ 0 := MvPolynomial.mem_support_iff.mp hα
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul] at hc
    exact hc rfl
  have hh := hp (MvPolynomial.mem_support_iff.mpr hn)
  change Finsupp.weight (fun _ : σ => 1) (α + Finsupp.single i 1) + k ≤ d at hh
  simp only [map_add, Finsupp.weight_single, one_smul] at hh
  change Finsupp.weight (fun _ : σ => 1) α + (k + 1) ≤ d
  omega

noncomputable def scalarDirectionalDerivative [Fintype σ] (h : σ → ℚ) :
    Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) :=
  ∑ i, h i • MvPolynomial.pderiv i

theorem scalarDirectionalDerivative_apply [Fintype σ] (h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative h p = ∑ i, h i • MvPolynomial.pderiv i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, h i • MvPolynomial.pderiv i)) p = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply]

@[simp] theorem scalarDirectionalDerivative_C [Fintype σ] (h : σ → ℚ) (c : ℚ) :
    scalarDirectionalDerivative h (C c) = 0 := MvPolynomial.derivation_C _ _

@[simp] theorem scalarDirectionalDerivative_X [Fintype σ] (h : σ → ℚ) (j : σ) :
    scalarDirectionalDerivative h (X j) = C (h j) := by
  classical
  simp [scalarDirectionalDerivative_apply, MvPolynomial.pderiv_X, Pi.single_apply, MvPolynomial.C_eq_smul_one]

theorem scalarDirectionalDerivative_mul [Fintype σ] (h : σ → ℚ) (p q : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative h (p * q) = scalarDirectionalDerivative h p * q +
      p * scalarDirectionalDerivative h q := by
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem polynomialDegreeGap_directionalDerivative [Fintype σ] (h : σ → ℚ)
    {k d : ℕ} {p : MvPolynomial σ ℚ} (hp : p ∈ polynomialDegreeGap k d) :
    scalarDirectionalDerivative h p ∈ polynomialDegreeGap (k + 1) d := by
  rw [scalarDirectionalDerivative_apply]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (polynomialDegreeGap_pderiv hp i))

theorem polynomialDegreeGap_translate_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) ∈ polynomialDegreeGap 0 (Finsupp.weight (fun _ => 1) α) := by
  intro β hβ
  simpa only [Nat.add_zero] using
    (polynomialTranslate_monomial_bounds h (fun _ => 1) (by simp) α).1 hβ

theorem polynomialDegreeGap_translate_sub_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    polynomialTranslate h (monomial α 1) - monomial α 1 ∈
      polynomialDegreeGap 1 (Finsupp.weight (fun _ => 1) α) := by
  intro β hβ
  exact Nat.succ_le_of_lt ((polynomialTranslate_monomial_bounds h (fun _ => 1) (by simp) α).2 hβ)

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem eval₂_eq_of_weightedSupport (φ : R →+* S)
    {w : σ → ℕ} {d : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLE w d) (x y : σ → S)
    (hxy : ∀ i, w i ≤ d → x i = y i) :
    eval₂ φ x P = eval₂ φ y P := by
  apply MvPolynomial.eval₂_congr φ x y
  intro i α hi hα
  exact hxy i ((Finsupp.le_weight_of_ne_zero' w
    (Finsupp.mem_support_iff.mp hi)).trans (hP (MvPolynomial.mem_support_iff.mpr hα)))

theorem aeval_eq_of_weightedSupportLE [Algebra R S]
    {w : σ → ℕ} {d : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportLE w d) (x y : σ → S)
    (hxy : ∀ i, w i ≤ d → x i = y i) : aeval x P = aeval y P :=
  eval₂_eq_of_weightedSupport (algebraMap R S) hP x y hxy

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem weightedSupportLE_mono {w : σ → ℕ} {d e : ℕ} {p : MvPolynomial σ R}
    (hde : d ≤ e) (hp : p ∈ weightedSupportLE w d) : p ∈ weightedSupportLE w e :=
  fun _ h => (hp h).trans hde

theorem weightedSupportLE_C (w : σ → ℕ) (d : ℕ) (r : R) :
    C r ∈ weightedSupportLE w d := by
  exact (monomial_mem_restrictSupport R).mpr (Or.inl (by simp))

theorem weightedSupportLE_X (w : σ → ℕ) (i : σ) :
    (X i : MvPolynomial σ R) ∈ weightedSupportLE w (w i) := by
  simpa only [X, Finsupp.weight_single, one_smul] using
    weightedSupportLE_monomial w (Finsupp.single i 1) (1 : R)

theorem weightedSupportLE_pow {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLE w d) (n : ℕ) :
    p ^ n ∈ weightedSupportLE w (n * d) := by
  induction n with
  | zero => simpa using weightedSupportLE_C w 0 (1 : R)
  | succ n ih =>
    simpa only [pow_succ, Nat.succ_mul] using weightedSupportLE_mul ih hp

theorem weightedSupportLE_prod {ι : Type*} (s : Finset ι) (w : σ → ℕ)
    (f : ι → MvPolynomial σ R) (d : ι → ℕ)
    (hf : ∀ i ∈ s, f i ∈ weightedSupportLE w (d i)) :
    (∏ i ∈ s, f i) ∈ weightedSupportLE w (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weightedSupportLE_C w 0 (1 : R)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact weightedSupportLE_mul (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem weightedSupportLE_aeval_monomial (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (α : σ →₀ ℕ) (r : R) :
    aeval (R := R) f (monomial α r) ∈ weightedSupportLE v (Finsupp.weight w α) := by
  classical
  rw [aeval_monomial]
  have hprod := weightedSupportLE_prod α.support v (fun i => f i ^ α i)
    (fun i => α i * w i) (fun i _ => weightedSupportLE_pow (hf i) (α i))
  have hweight : (∑ i ∈ α.support, α i * w i) = Finsupp.weight w α := by
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Nat.cast_id]
  rw [hweight] at hprod
  simpa only [zero_add, MvPolynomial.algebraMap_eq, Finsupp.prod] using
    weightedSupportLE_mul (weightedSupportLE_C v 0 r) hprod

theorem weightedSupportLE_aeval (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    {p : MvPolynomial σ R} {d : ℕ} (hp : p ∈ weightedSupportLE w d) :
    aeval (R := R) f p ∈ weightedSupportLE v d := by
  classical
  rw [← p.support_sum_monomial_coeff, map_sum]
  apply (weightedSupportLE v d).sum_mem
  intro α hα
  exact weightedSupportLE_mono (hp hα) (weightedSupportLE_aeval_monomial w v f hf α _)

theorem mem_weightedSupportLE_iff (w : σ → ℕ) (d : ℕ) (p : MvPolynomial σ R) :
    p ∈ weightedSupportLE w d ↔ p.weightedTotalDegree w ≤ d := by
  classical
  change (∀ α ∈ p.support, Finsupp.weight w α ≤ d) ↔ _
  simp only [weightedTotalDegree, Finset.sup_le_iff]

theorem weightedTotalDegree_aeval_le (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).weightedTotalDegree v ≤ w i)
    {p : MvPolynomial σ R} {d : ℕ} (hp : p.weightedTotalDegree w ≤ d) :
    (aeval (R := R) f p).weightedTotalDegree v ≤ d := by
  apply (mem_weightedSupportLE_iff v d _).mp
  apply weightedSupportLE_aeval w v f
  · intro i
    exact (mem_weightedSupportLE_iff v (w i) _).mpr (hf i)
  · exact (mem_weightedSupportLE_iff w d _).mpr hp

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} [Fintype σ]

noncomputable def scalarTaylorRemainder (h : σ → ℚ) :
    MvPolynomial σ ℚ →ₗ[ℚ] MvPolynomial σ ℚ :=
  (polynomialTranslate h).toLinearMap - LinearMap.id - (scalarDirectionalDerivative h).toLinearMap

theorem scalarTaylorRemainder_apply (h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    scalarTaylorRemainder h p = polynomialTranslate h p - p - scalarDirectionalDerivative h p := rfl

@[simp] theorem scalarTaylorRemainder_C (h : σ → ℚ) (c : ℚ) :
    scalarTaylorRemainder h (C c) = 0 := by
  rw [scalarTaylorRemainder_apply, polynomialTranslate_C, scalarDirectionalDerivative_C, sub_self, sub_zero]

@[simp] theorem scalarTaylorRemainder_X (h : σ → ℚ) (i : σ) :
    scalarTaylorRemainder h (X i) = 0 := by
  rw [scalarTaylorRemainder_apply, polynomialTranslate_X, scalarDirectionalDerivative_X]
  ring

theorem scalarTaylorRemainder_mul (h : σ → ℚ) (p q : MvPolynomial σ ℚ) :
    scalarTaylorRemainder h (p * q) =
      scalarTaylorRemainder h p * polynomialTranslate h q +
        scalarDirectionalDerivative h p * (polynomialTranslate h q - q) +
        p * scalarTaylorRemainder h q := by
  simp only [scalarTaylorRemainder_apply, map_mul, scalarDirectionalDerivative_mul]
  ring

private theorem remainder_monomial_add (h : σ → ℚ) (α β : σ →₀ ℕ)
    (hα : scalarTaylorRemainder h (monomial α 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) α))
    (hβ : scalarTaylorRemainder h (monomial β 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) β)) :
    scalarTaylorRemainder h (monomial (α + β) 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) (α + β)) := by
  rw [map_add]
  have he : (monomial (α + β) 1 : MvPolynomial σ ℚ) = monomial α 1 * monomial β 1 := by simp
  rw [he, scalarTaylorRemainder_mul]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact polynomialDegreeGap_mul (i := 2) (j := 0) hα (polynomialDegreeGap_translate_monomial h β)
    · exact polynomialDegreeGap_mul (i := 1) (j := 1)
        (polynomialDegreeGap_directionalDerivative h (k := 0) (polynomialDegreeGap_monomial α 1))
        (polynomialDegreeGap_translate_sub_monomial h β)
  · exact polynomialDegreeGap_mul (i := 0) (j := 2) (polynomialDegreeGap_monomial α 1) hβ

theorem scalarTaylorRemainder_monomial (h : σ → ℚ) (α : σ →₀ ℕ) :
    scalarTaylorRemainder h (monomial α 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) α) := by
  classical
  have hz : scalarTaylorRemainder h (monomial (0 : σ →₀ ℕ) 1) = 0 :=
    scalarTaylorRemainder_C h 1
  have hsingle (i : σ) (n : ℕ) : scalarTaylorRemainder h (monomial (Finsupp.single i n) 1) ∈
      polynomialDegreeGap 2 (Finsupp.weight (fun _ => 1) (Finsupp.single i n)) := by
    induction n with
    | zero => rw [Finsupp.single_zero, hz]; exact Submodule.zero_mem _
    | succ n ih =>
      rw [show Finsupp.single i (n + 1) = Finsupp.single i n + Finsupp.single i 1 from Finsupp.single_add _ _ _]
      apply remainder_monomial_add h _ _ ih
      change scalarTaylorRemainder h (X i) ∈ _
      rw [scalarTaylorRemainder_X]
      exact Submodule.zero_mem _
  induction α using Finsupp.induction with
  | zero => rw [hz]; exact Submodule.zero_mem _
  | @single_add i n α _ _ ih => exact remainder_monomial_add h _ _ (hsingle i n) ih

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

noncomputable def polynomialTranslationPath (x : σ → ℚ) :
    MvPolynomial σ ℚ →ₐ[ℚ] Polynomial (MvPolynomial σ ℚ) :=
  MvPolynomial.aeval fun i =>
    Polynomial.C (X i) - Polynomial.C (C (x i)) * Polynomial.X

@[simp] theorem polynomialTranslationPath_C (x : σ → ℚ) (c : ℚ) :
    polynomialTranslationPath x (C c) = Polynomial.C (C c) := by
  simp [polynomialTranslationPath]

@[simp] theorem polynomialTranslationPath_X (x : σ → ℚ) (i : σ) :
    polynomialTranslationPath x (X i) =
      Polynomial.C (X i) - Polynomial.C (C (x i)) * Polynomial.X := by
  simp [polynomialTranslationPath]

theorem polynomialTranslationPath_eval (x : σ → ℚ) (t : ℚ)
    (V : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x V).eval (C t) =
      polynomialTranslate (fun i => -(t * x i)) V := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, polynomialTranslationPath_X,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X, polynomialTranslate_X]
    congr 1
    simp only [map_neg, map_mul]
    ring

@[simp] theorem polynomialTranslate_zero (V : MvPolynomial σ ℚ) :
    polynomialTranslate (0 : σ → ℚ) V = V := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [hp]

@[simp] theorem polynomialTranslationPath_eval_zero (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x V).eval 0 = V := by
  have h := polynomialTranslationPath_eval x 0 V
  simp only [map_zero, zero_mul, neg_zero] at h
  exact h.trans (polynomialTranslate_zero V)

theorem polynomialTranslationPath_derivative [Fintype σ] (x : σ → ℚ)
    (V : MvPolynomial σ ℚ) :
    (polynomialTranslationPath x V).derivative =
      -polynomialTranslationPath x (scalarDirectionalDerivative x V) := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, neg_add_rev]
    abel
  | mul_X p i hp =>
    simp only [map_mul, Polynomial.derivative_mul, hp,
      polynomialTranslationPath_X, Polynomial.derivative_sub, Polynomial.derivative_C,
      Polynomial.derivative_X, zero_sub, scalarDirectionalDerivative_mul,
      scalarDirectionalDerivative_X, map_add, polynomialTranslationPath_C]
    ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

def lowestSlotWeight (h : ℕ) : σ ⊕ τ → ℕ := Sum.elim (fun _ => 1) (fun _ => h)

theorem exponent_eq_single_of_lowest_slot {h : ℕ} (hh : 0 < h)
    {α : (σ ⊕ τ) →₀ ℕ}
    (hα : Finsupp.weight (lowestSlotWeight h) α ≤ h)
    {j : τ} (hj : α (Sum.inr j) ≠ 0) : α = Finsupp.single (Sum.inr j) 1 := by
  classical
  have hw := Finsupp.weight_sub_single_add (w := lowestSlotWeight (σ := σ) (τ := τ) h) hj
  have hz : Finsupp.weight (lowestSlotWeight h) (α - Finsupp.single (Sum.inr j) 1) = 0 := by
    change _ + h = _ at hw
    omega
  have hzero : α - Finsupp.single (Sum.inr j) 1 = 0 := by
    ext v
    have hv : lowestSlotWeight (σ := σ) (τ := τ) h v ≠ 0 := by
      cases v <;> simp [lowestSlotWeight, hh.ne']
    have hle := Finsupp.le_weight (lowestSlotWeight h) hv (α - Finsupp.single (Sum.inr j) 1)
    rw [hz] at hle
    exact Nat.eq_zero_of_le_zero hle
  have heq := Finsupp.sub_add_single_one_cancel hj
  rw [hzero, zero_add] at heq
  exact heq.symm

def SlotAffine [Fintype τ] (h : ℕ) (p : MvPolynomial (σ ⊕ τ) R) : Prop :=
  ∃ (C₀ : MvPolynomial σ R) (m : τ → R),
    C₀ ∈ weightedSupportLE (fun _ : σ => 1) h ∧
    ∀ (t : σ → R) (x : τ → R),
      aeval (Sum.elim t x) p = aeval t C₀ + ∑ j, m j * x j

namespace SlotAffine

variable [Fintype τ] {h : ℕ}

theorem zero : SlotAffine (σ := σ) (τ := τ) (R := R) h 0 := by
  refine ⟨0, 0, (weightedSupportLE _ _).zero_mem, ?_⟩
  intro t x
  simp

theorem add {p q : MvPolynomial (σ ⊕ τ) R}
    (hp : SlotAffine h p) (hq : SlotAffine h q) : SlotAffine h (p + q) := by
  obtain ⟨Cp, mp, hCp, heqp⟩ := hp
  obtain ⟨Cq, mq, hCq, heqq⟩ := hq
  refine ⟨Cp + Cq, mp + mq, (weightedSupportLE _ _).add_mem hCp hCq, ?_⟩
  intro t x
  simp only [map_add, heqp, heqq, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  abel

theorem of_monomial {α : (σ ⊕ τ) →₀ ℕ} (c : R) (hh : 0 < h)
    (hα : Finsupp.weight (lowestSlotWeight h) α ≤ h) :
    SlotAffine h (monomial α c) := by
  classical
  by_cases hslots : ∀ j : τ, α (Sum.inr j) = 0
  · let C₀ : MvPolynomial σ R :=
      aeval (Sum.elim X (fun _ : τ => 0)) (monomial α c)
    have hC : C₀ ∈ weightedSupportLE (fun _ : σ => 1) h := by
      apply weightedSupportLE_aeval (lowestSlotWeight h) (fun _ : σ => 1)
      · intro v
        cases v with
        | inl a => exact weightedSupportLE_X _ a
        | inr j => exact (weightedSupportLE _ _).zero_mem
      · exact weightedSupportLE_mono hα (weightedSupportLE_monomial _ _ _)
    refine ⟨C₀, 0, hC, ?_⟩
    intro t x
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, C₀,
      MvPolynomial.comp_aeval_apply]
    simp only [aeval_monomial]
    congr 1
    apply Finset.prod_congr rfl
    intro v hv
    cases v with
    | inl a => simp
    | inr j => simp [hslots j]
  · push Not at hslots
    obtain ⟨j, hj⟩ := hslots
    rw [exponent_eq_single_of_lowest_slot hh hα hj]
    refine ⟨0, Pi.single j c, (weightedSupportLE _ _).zero_mem, ?_⟩
    intro t x
    simp [aeval_monomial, Pi.single_apply]

end SlotAffine

theorem slotAffine_of_weightedSupport [Fintype τ] {h : ℕ} (hh : 0 < h)
    {p : MvPolynomial (σ ⊕ τ) R}
    (hp : p ∈ weightedSupportLE (lowestSlotWeight h) h) : SlotAffine h p := by
  classical
  have hsum (s : Finset ((σ ⊕ τ) →₀ ℕ))
      (hs : ∀ α ∈ s, Finsupp.weight (lowestSlotWeight h) α ≤ h) :
      SlotAffine h (∑ α ∈ s, monomial α (p.coeff α)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (SlotAffine.zero (σ := σ) (τ := τ) (R := R) (h := h))
    | @insert α s hnot ih =>
      rw [Finset.sum_insert hnot]
      exact (SlotAffine.of_monomial _ hh (hs α (Finset.mem_insert_self _ _))).add
        (ih (fun β hβ => hs β (Finset.mem_insert_of_mem hβ)))
  simpa only [p.support_sum_monomial_coeff] using hsum p.support hp

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U B R : Type*} [CommRing R]

theorem weightedSupportLE_rename_inl_ring (v : U → ℕ) (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial U R} (hP : P ∈ weightedSupportLE v d) :
    rename (Sum.inl : U → U ⊕ B) P ∈ weightedSupportLE (Sum.elim v w) d := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro i
  exact weightedSupportLE_X (Sum.elim v w) (Sum.inl i)

theorem weightedSupportLE_rename_inr_ring (v : U → ℕ) (w : B → ℕ)
    {d : ℕ} {P : MvPolynomial B R} (hP : P ∈ weightedSupportLE w d) :
    rename (Sum.inr : B → U ⊕ B) P ∈ weightedSupportLE (Sum.elim v w) d := by
  rw [rename_eq_aeval]
  apply weightedSupportLE_aeval _ _ _ _ hP
  intro i
  exact weightedSupportLE_X (Sum.elim v w) (Sum.inr i)

end Erdos3

end

end OAI
