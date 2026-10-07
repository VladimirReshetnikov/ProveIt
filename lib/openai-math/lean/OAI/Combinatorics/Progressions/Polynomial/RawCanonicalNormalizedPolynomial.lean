/- Modified for ProveIt: distribute coefficients over polynomial sums
explicitly in Mathlib v4.32.0. Mathematical statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.ScaledJointFrozenSource

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def rawProductArrayPolynomial {D K : Type*} {B L : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (terms : ∀ d, Finset (L d)) (exponent : ∀ d, L d → K →₀ ℕ)
    (principal : ∀ d, B d → Fin (h d) → K)
    (a : ∀ d, B d → ℝ) (b : ∀ d, L d → ℝ) (constant : D → ℝ) (d : D) : MvPolynomial K ℝ :=
  MvPolynomial.C (constant d) +
    (∑ j, MvPolynomial.C (a d j) * ∏ v, MvPolynomial.X (principal d j v)) +
      ∑ n ∈ terms d, MvPolynomial.monomial (exponent d n) (b d n)

theorem rawProductArrayPolynomial_eval {D K : Type*} {B L : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (terms : ∀ d, Finset (L d)) (exponent : ∀ d, L d → K →₀ ℕ)
    (principal : ∀ d, B d → Fin (h d) → K)
    (a : ∀ d, B d → ℝ) (b : ∀ d, L d → ℝ) (constant : D → ℝ) (y : K → ℝ) (d : D) :
    MvPolynomial.eval y (rawProductArrayPolynomial h terms exponent principal a b constant d) =
      rawProductArrayValue h terms exponent principal a b constant y d := by
  simp only [rawProductArrayPolynomial, rawProductArrayValue, map_add, map_sum, map_mul,
    map_prod, MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.eval_monomial, Finsupp.prod]

theorem rawProductArrayJet_polynomial {D K α : Type*} [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d))
    (exponent : ∀ d, L d → K →₀ ℕ) (principal : ∀ d, B d → Fin (h d) → K)
    (a : ∀ d, B d → ℝ) (b : ∀ d, L d → ℝ) (constant Q : D → ℝ)
    (tuple : Finset α → K → ℝ) (o : Σ d, O d) :
    rawProductArrayJet h sets terms exponent principal a b constant Q tuple o =
      booleanCoefficient (fun vertex => MvPolynomial.eval (tuple vertex)
        (rawProductArrayPolynomial h terms exponent principal a b constant o.1))
        (sets o.1 o.2) / Q o.1 := by
  simp only [rawProductArrayPolynomial_eval, rawProductArrayJet]

theorem rawProductArrayPolynomial_totalDegree_le {D K : Type*}
    {B L : D → Type*} [∀ d, Fintype (B d)]
    (h : D → ℕ) (terms : ∀ d, Finset (L d)) (exponent : ∀ d, L d → K →₀ ℕ)
    (principal : ∀ d, B d → Fin (h d) → K)
    (a : ∀ d, B d → ℝ) (b : ∀ d, L d → ℝ) (constant : D → ℝ) (d : D)
    {H : ℕ} (hh : h d ≤ H) (he : ∀ n ∈ terms d, (exponent d n).sum (fun _ e => e) ≤ H) :
    (rawProductArrayPolynomial h terms exponent principal a b constant d).totalDegree ≤ H := by
  classical
  unfold rawProductArrayPolynomial
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply (MvPolynomial.totalDegree_add _ _).trans
    apply max_le
    · simp
    · apply MvPolynomial.totalDegree_finsetSum_le
      intro j _
      apply (MvPolynomial.totalDegree_mul _ _).trans
      simp only [MvPolynomial.totalDegree_C, zero_add]
      apply (MvPolynomial.totalDegree_finsetProd _ _).trans
      simpa only [MvPolynomial.totalDegree_X, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, smul_eq_mul, mul_one] using hh
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro n hn
    exact (MvPolynomial.totalDegree_monomial_le _ _).trans (he n hn)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_coefficient_split {K : Type*} [DecidableEq K] (p : MvPolynomial K ℝ)
    (selected : Finset (K →₀ ℕ)) :
    p = (∑ n ∈ selected, MvPolynomial.monomial n (p.coeff n)) +
      ∑ n ∈ p.support \ selected, MvPolynomial.monomial n (p.coeff n) := by
  classical
  ext n
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sum]
  by_cases hs : n ∈ selected
  · simp [MvPolynomial.coeff_monomial, hs]
  · by_cases hp : n ∈ p.support
    · simp [MvPolynomial.coeff_monomial, hs, hp]
    · have hc := MvPolynomial.notMem_support_iff.mp hp
      simp [MvPolynomial.coeff_monomial, hs, hp, hc]

noncomputable def nonprincipalSupport {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (principal : J → K →₀ ℕ) : Finset (K →₀ ℕ) := by
  classical
  exact p.support \ insert 0 (Finset.univ.image principal)

theorem polynomial_coefficient_split_principal {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (principal : J → K →₀ ℕ)
    (hinj : Function.Injective principal) (hzero : ∀ j, principal j ≠ 0) :
    p = MvPolynomial.C (p.coeff 0) +
      (∑ j, MvPolynomial.monomial (principal j) (p.coeff (principal j))) +
      ∑ n ∈ nonprincipalSupport p principal, MvPolynomial.monomial n (p.coeff n) := by
  classical
  have hnot : (0 : K →₀ ℕ) ∉ Finset.univ.image principal := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hzero
  have he := polynomial_coefficient_split p (insert 0 (Finset.univ.image principal))
  rw [Finset.sum_insert hnot, Finset.sum_image (fun i _ j _ hij => hinj hij)] at he
  exact he

theorem nonprincipalSupport_subset {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (principal : J → K →₀ ℕ) :
    nonprincipalSupport p principal ⊆ p.support := by
  classical
  exact Finset.sdiff_subset

theorem nonprincipalSupport_degree {K J : Type*} [Fintype J]
    (p : MvPolynomial K ℝ) (principal : J → K →₀ ℕ)
    {n : K →₀ ℕ} (hn : n ∈ nonprincipalSupport p principal) :
    n.sum (fun _ e => e) ≤ p.totalDegree :=
  MvPolynomial.le_totalDegree (nonprincipalSupport_subset p principal hn)

theorem nonprincipalSupport_card_le {K J : Type*} [Fintype K] [Fintype J]
    (p : MvPolynomial K ℝ) (principal : J → K →₀ ℕ)
    {h : ℕ} (hp : p.totalDegree ≤ h) :
    (nonprincipalSupport p principal).card ≤ (Fintype.card K + 1) ^ h :=
  (Finset.card_le_card (nonprincipalSupport_subset p principal)).trans
    (mvPolynomial_support_card_le_totalDegree p hp)

theorem nonprincipalSupport_abs_sum_le {K J : Type*} [Fintype K] [Fintype J]
    (p : MvPolynomial K ℝ) (principal : J → K →₀ ℕ)
    {h : ℕ} (hp : p.totalDegree ≤ h) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ n ∈ nonprincipalSupport p principal, |p.coeff n| ≤ M) :
    (∑ n ∈ nonprincipalSupport p principal, |p.coeff n|) ≤
      ((Fintype.card K : ℝ) + 1) ^ h * M :=
  monomialArray_abs_sum_le (nonprincipalSupport p principal) id
    (fun _ _ _ _ he => he) h (fun _ hn => (nonprincipalSupport_degree p principal hn).trans hp)
    p.coeff hM hc

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem rawCanonicalJet_normalized_polynomial {D G Z α : Type*} [Fintype α] [DecidableEq α]
    {B O L : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ) (c : ∀ d, B d → ℝ)
    (sets : ∀ d, O d → Finset α) (terms : ∀ d, Finset (L d)) (weight : ∀ d, L d → ℝ)
    (exponent : ∀ d, L d → SamplerTupleIndex G B h →₀ ℕ)
    (coefficientIndex : ∀ d, L d → Z) (extra : G → Option α → Z)
    (Q : D → ℝ) (scale : SamplerTupleIndex G B h → ℝ) (constant : D → ℝ)
    (hQ : ∀ d, Q d ≠ 0) (hscale : ∀ k, scale k ≠ 0)
    (t : ℝ) (z : Z → ℝ) (x : JointBlockParameter B h α → ℝ) :
    rawCanonicalJet h c sets terms weight exponent coefficientIndex extra Q scale constant t z
      (jointCubeScale h (fun i => scale (.inr i)) x) =
      fun o => booleanCoefficient (fun vertex =>
        MvPolynomial.eval (normalizedCubeTuple (canonicalTupleInput extra) z x vertex)
          (rawProductArrayPolynomial h terms exponent (fun d b v => .inr ⟨d, b, v⟩) c
            (fun d j => t * (weight d j * z (coefficientIndex d j))) constant o.1))
        (sets o.1 o.2) := by
  rw [rawCanonicalJet_rescale]
  funext o
  unfold canonicalScaledProductArrayJet scaledProductArrayJet rawProductArrayJet
  rw [← booleanCoefficient_div]
  congr 1
  funext vertex
  rw [rawProductArrayValue_scaled h terms weight exponent _ coefficientIndex c Q scale constant hQ hscale,
    rawProductArrayPolynomial_eval]
  simp only [rawProductArrayValue, Finset.mul_sum, mul_assoc]

end Erdos3

end

end OAI
