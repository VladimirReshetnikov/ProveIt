import Diophantine.Common.RefinedRelationCombiningPolynomial
import Mathlib.Data.Finsupp.Weight
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Degree bounds for the refined relation-combining polynomial

The coefficients are first substituted by their actual target polynomials.
For each supported outer monomial we then bound twice the total degree of
its coefficient plus the weighted degree of its formal radicals. Expansion
by two affects only radical exponents. This gives a substitution bound
after exponent halving without expanding the product over sign choices.

All degree budgets are natural numbers. The doubled grading accommodates
odd radicand degree bounds without rounding a putative square-root degree.
-/

namespace Diophantine.RefinedRelationCombiningPolynomial

open MvPolynomial
open Diophantine.RelationCombiningPolynomial (signed)

noncomputable section

variable {ι σ : Type*}

/-- A degree bound on nested polynomials, counting coefficient degrees
twice and giving each outer variable its specified radical budget. -/
def ScaledBound (w : ι → ℕ) (p : MvPolynomial ι (MvPolynomial σ ℤ)) (N : ℕ) : Prop :=
  ∀ d ∈ p.support, 2 * (p.coeff d).totalDegree + Finsupp.weight w d ≤ N

namespace ScaledBound

variable {w : ι → ℕ} {p r : MvPolynomial ι (MvPolynomial σ ℤ)} {N M : ℕ}

theorem mono (h : ScaledBound w p N) (hNM : N ≤ M) : ScaledBound w p M :=
  fun d hd => (h d hd).trans hNM

theorem zero (w : ι → ℕ) (N : ℕ) :
    ScaledBound w (0 : MvPolynomial ι (MvPolynomial σ ℤ)) N := by
  intro d hd
  simp only [support_zero, Finset.notMem_empty] at hd

theorem C (w : ι → ℕ) (p : MvPolynomial σ ℤ) :
    ScaledBound w (MvPolynomial.C p) (2 * p.totalDegree) := by
  classical
  intro d hd
  have hd0 : d = 0 := by
    by_contra h
    exact (mem_support_iff.mp hd) (coeff_C_of_ne_zero h p)
  subst d
  simp

theorem X (w : ι → ℕ) (i : ι) :
    ScaledBound w (MvPolynomial.X i : MvPolynomial ι (MvPolynomial σ ℤ)) (w i) := by
  classical
  intro d hd
  have hd1 : d = Finsupp.single i 1 := by
    simpa only [support_X, Finset.mem_singleton] using hd
  subst d
  simp [Finsupp.weight_single]

theorem neg (hp : ScaledBound w p N) : ScaledBound w (-p) N := by
  intro d hd
  have hd' : d ∈ p.support := by simpa using hd
  simpa only [coeff_neg, totalDegree_neg] using hp d hd'

theorem add (hp : ScaledBound w p N) (hr : ScaledBound w r M) :
    ScaledBound w (p + r) (max N M) := by
  classical
  intro d hd
  rw [coeff_add]
  by_cases hp0 : p.coeff d = 0
  · have hr0 : r.coeff d ≠ 0 := by
      simpa only [mem_support_iff, coeff_add, hp0, zero_add] using hd
    simpa only [hp0, zero_add] using (hr d (mem_support_iff.mpr hr0)).trans (le_max_right N M)
  · by_cases hr0 : r.coeff d = 0
    · simpa only [hr0, add_zero] using
        (hp d (mem_support_iff.mpr hp0)).trans (le_max_left N M)
    · have hp' := hp d (mem_support_iff.mpr hp0)
      have hr' := hr d (mem_support_iff.mpr hr0)
      have hdeg := totalDegree_add (p.coeff d) (r.coeff d)
      omega

theorem sub (hp : ScaledBound w p N) (hr : ScaledBound w r M) :
    ScaledBound w (p - r) (max N M) := by
  simpa only [sub_eq_add_neg] using hp.add hr.neg

/-- A finite coefficient sum preserves a common shifted, doubled bound. -/
private theorem degree_sum_le {κ : Type*} (s : Finset κ)
    (f : κ → MvPolynomial σ ℤ) (K N : ℕ) (hK : K ≤ N)
    (hf : ∀ i ∈ s, 2 * (f i).totalDegree + K ≤ N) :
    2 * (s.sum f).totalDegree + K ≤ N := by
  have hdeg : (s.sum f).totalDegree ≤ (N - K) / 2 := by
    apply totalDegree_finsetSum_le
    intro i hi
    have := hf i hi
    omega
  omega

theorem mul (hp : ScaledBound w p N) (hr : ScaledBound w r M) :
    ScaledBound w (p * r) (N + M) := by
  classical
  intro d hd
  have hcoeff : (∑ ab ∈ Finset.antidiagonal d, p.coeff ab.1 * r.coeff ab.2) ≠ 0 := by
    simpa only [← coeff_mul] using mem_support_iff.mp hd
  have hterm : ∀ ab ∈ Finset.antidiagonal d,
      p.coeff ab.1 * r.coeff ab.2 ≠ 0 →
      2 * (p.coeff ab.1 * r.coeff ab.2).totalDegree + Finsupp.weight w d ≤ N + M := by
    intro ab hab hne
    have hp' := hp ab.1 (mem_support_iff.mpr (left_ne_zero_of_mul hne))
    have hr' := hr ab.2 (mem_support_iff.mpr (right_ne_zero_of_mul hne))
    have hdeg := totalDegree_mul (p.coeff ab.1) (r.coeff ab.2)
    have hdw : Finsupp.weight w d =
        Finsupp.weight w ab.1 + Finsupp.weight w ab.2 := by
      rw [← Finset.mem_antidiagonal.mp hab, map_add]
    omega
  obtain ⟨ab, hab, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff
  have hw : Finsupp.weight w d ≤ N + M := by
    have := hterm ab hab hne
    omega
  rw [coeff_mul]
  apply degree_sum_le _ _ _ _ hw
  intro ab hab
  by_cases hzero : p.coeff ab.1 * r.coeff ab.2 = 0
  · simpa only [hzero, totalDegree_zero, mul_zero, zero_add] using hw
  · exact hterm ab hab hzero

theorem sum {κ : Type*} (s : Finset κ) (f : κ → MvPolynomial ι (MvPolynomial σ ℤ))
    (hf : ∀ i ∈ s, ScaledBound w (f i) N) : ScaledBound w (s.sum f) N := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simpa using zero w N
  | @insert i s hi ih =>
    intro hf
    rw [Finset.sum_insert hi]
    simpa only [max_self] using
      (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem prod {κ : Type*} (s : Finset κ) (f : κ → MvPolynomial ι (MvPolynomial σ ℤ))
    (b : κ → ℕ) (hf : ∀ i ∈ s, ScaledBound w (f i) (b i)) :
    ScaledBound w (s.prod f) (s.sum b) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => intro _; simpa using C w (1 : MvPolynomial σ ℤ)
  | @insert i s hi ih =>
    intro hf
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end ScaledBound

/-- Substitution into a single outer monomial, including the degree of
its polynomial coefficient. -/
theorem totalDegree_eval₂_monomial_le (w : ι → ℕ) (A : ι → MvPolynomial σ ℤ)
    (hA : ∀ i, (A i).totalDegree ≤ w i) (d : ι →₀ ℕ) (c : MvPolynomial σ ℤ) :
    (eval₂ (RingHom.id _) A (monomial d c)).totalDegree ≤
      c.totalDegree + Finsupp.weight w d := by
  classical
  rw [eval₂_monomial]
  refine (totalDegree_mul _ _).trans (Nat.add_le_add_left ?_ _)
  change (∏ i ∈ d.support, A i ^ d i).totalDegree ≤ Finsupp.weight w d
  refine (totalDegree_finsetProd _ _).trans ?_
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  apply Finset.sum_le_sum
  intro i hi
  exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hA i))

/-- Transport a bound through exponent halving and arbitrary polynomial
substitution. Only the outer exponents are doubled; coefficients retain
their full target-variable degree. -/
theorem totalDegree_eval₂_le_of_expand_bound (w : ι → ℕ)
    (p : MvPolynomial ι (MvPolynomial σ ℤ)) (A : ι → MvPolynomial σ ℤ)
    (hA : ∀ i, (A i).totalDegree ≤ w i) (N : ℕ)
    (hp : ScaledBound w (expand 2 p) N) :
    2 * (eval₂ (RingHom.id _) A p).totalDegree ≤ N := by
  classical
  have hdeg : (eval₂ (RingHom.id _) A p).totalDegree ≤ N / 2 := by
    conv_lhs => rw [p.as_sum]
    rw [eval₂_sum]
    apply totalDegree_finsetSum_le
    intro d hd
    have hcoeff : (expand 2 p).coeff (2 • d) = p.coeff d :=
      coeff_expand_smul 2 (by decide) p d
    have hex : 2 • d ∈ (expand 2 p).support := by
      rw [mem_support_iff, hcoeff]
      exact mem_support_iff.mp hd
    have hb := hp (2 • d) hex
    rw [hcoeff, map_nsmul] at hb
    simp only [smul_eq_mul] at hb
    have hm := totalDegree_eval₂_monomial_le w A hA d (p.coeff d)
    omega
  omega

/-- The degree budget for a prefix of the individual weight polynomials. -/
def prefixDegree {q : ℕ} (dV : Fin q → ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin q => i.val < m), dV i

theorem totalDegree_prefix_le {q : ℕ} (V : Fin q → MvPolynomial σ ℤ)
    (dV : Fin q → ℕ) (hV : ∀ i, (V i).totalDegree ≤ dV i) (m : ℕ) :
    (weightPrefix V m).totalDegree ≤ prefixDegree dV m := by
  unfold weightPrefix prefixDegree
  exact (totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => hV i)

/-- Doubled budget for the parenthesized expression in a signed factor. -/
def innerBudget (q : ℕ) (dA dV : Fin q → ℕ) (dC : ℕ) : ℕ :=
  max (2 * dC) (max (2 * prefixDegree dV q)
    (Finset.univ.sup fun i : Fin q => dA i + 2 * prefixDegree dV i.val))

/-- Doubled degree budget for one signed factor. -/
def factorBudget (q : ℕ) (dA dV : Fin q → ℕ) (dn dB dC dD : ℕ) : ℕ :=
  max (2 * max (dB + dn) dC)
    (2 * (dB + dD) + innerBudget q dA dV dC)

private theorem degree_add_le {p r : MvPolynomial σ ℤ} {N M : ℕ}
    (hp : p.totalDegree ≤ N) (hr : r.totalDegree ≤ M) :
    (p + r).totalDegree ≤ max N M :=
  (totalDegree_add _ _).trans (max_le_max hp hr)

private theorem degree_mul_le {p r : MvPolynomial σ ℤ} {N M : ℕ}
    (hp : p.totalDegree ≤ N) (hr : r.totalDegree ≤ M) :
    (p * r).totalDegree ≤ N + M :=
  (totalDegree_mul _ _).trans (Nat.add_le_add hp hr)

private theorem map_signed_polynomial {q : ℕ} (f : Coeff q →+* MvPolynomial σ ℤ)
    (ε : Bool) (p : RootPoly q) :
    map f (signed ε p) = signed ε (map f p) := by
  cases ε <;> simp only [signed, Bool.false_eq_true, if_false, if_true, map_neg]

/-- Keep coefficient substitution separate from the support degree proof.
In particular, the prefix products remain opaque throughout this identity. -/
private theorem map_rawFactor_substitution (q : ℕ) (V : Fin q → MvPolynomial σ ℤ)
    (n b c d : MvPolynomial σ ℤ) (ε : Fin q → Bool) :
    map (parameterSubstitution q V n b c d) (rawFactor q ε) =
      C (b * n + c) - C (b * (2 * d - 1)) *
        (C c + C (weightPrefix V q) +
          ∑ i : Fin q, signed (ε i) (X i) * C (weightPrefix V i.val)) := by
  classical
  let f := parameterSubstitution q V n b c d
  have hweight (i : Fin q) : f (X (Sum.inl i)) = V i :=
    eval₂Hom_X' C (Sum.elim V ![n, b, c, d]) (Sum.inl i)
  have hn : f (X (Sum.inr 0)) = n :=
    eval₂Hom_X' C (Sum.elim V ![n, b, c, d]) (Sum.inr 0)
  have hb : f (X (Sum.inr 1)) = b :=
    eval₂Hom_X' C (Sum.elim V ![n, b, c, d]) (Sum.inr 1)
  have hc : f (X (Sum.inr 2)) = c :=
    eval₂Hom_X' C (Sum.elim V ![n, b, c, d]) (Sum.inr 2)
  have hd : f (X (Sum.inr 3)) = d :=
    eval₂Hom_X' C (Sum.elim V ![n, b, c, d]) (Sum.inr 3)
  have hw (m : ℕ) : f (rawWeight q m) = weightPrefix V m := by
    rw [eval_rawWeight]
    simp only [hweight]
  change map f (rawFactor q ε) = _
  simp only [rawFactor, map_sub, map_mul, map_add, map_C, map_sum,
    map_signed_polynomial, map_X, map_ofNat, map_one, hw, hn, hb, hc, hd]

set_option maxHeartbeats 1000000 in
/-- Each signed factor satisfies the same bound after the coefficient
weights and arithmetic parameters are replaced by target polynomials. -/
theorem scaledBound_map_rawFactor (q : ℕ) (V : Fin q → MvPolynomial σ ℤ)
    (n b c d : MvPolynomial σ ℤ) (dA dV : Fin q → ℕ) (dn dB dC dD : ℕ)
    (hV : ∀ i, (V i).totalDegree ≤ dV i)
    (hn : n.totalDegree ≤ dn) (hb : b.totalDegree ≤ dB)
    (hc : c.totalDegree ≤ dC) (hd : d.totalDegree ≤ dD) (ε : Fin q → Bool) :
    ScaledBound dA (map (parameterSubstitution q V n b c d) (rawFactor q ε))
      (factorBudget q dA dV dn dB dC dD) := by
  classical
  rw [map_rawFactor_substitution]
  let T := innerBudget q dA dV dC
  have hC : ScaledBound dA
      (C c : MvPolynomial (Fin q) (MvPolynomial σ ℤ)) T :=
    (ScaledBound.C dA c).mono ((Nat.mul_le_mul_left 2 hc).trans (le_max_left _ _))
  have hP : ScaledBound dA
      (C (weightPrefix V q) : MvPolynomial (Fin q) (MvPolynomial σ ℤ)) T :=
    (ScaledBound.C dA _).mono
      ((Nat.mul_le_mul_left 2 (totalDegree_prefix_le V dV hV q)).trans
        ((le_max_left _ _).trans (le_max_right _ _)))
  have hsum : ScaledBound dA
      (∑ i : Fin q, signed (ε i) (X i) * C (weightPrefix V i.val)) T := by
    apply ScaledBound.sum
    intro i hi
    have hX : ScaledBound dA
        (signed (ε i) (X i) : MvPolynomial (Fin q) (MvPolynomial σ ℤ)) (dA i) := by
      cases ε i
      · exact (ScaledBound.X dA i).neg
      · exact ScaledBound.X dA i
    apply (hX.mul (ScaledBound.C dA (weightPrefix V i.val))).mono
    calc
      dA i + 2 * (weightPrefix V i.val).totalDegree ≤
          dA i + 2 * prefixDegree dV i.val :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 2 (totalDegree_prefix_le V dV hV i.val)) _
      _ ≤ T := (Finset.le_sup
        (f := fun j : Fin q => dA j + 2 * prefixDegree dV j.val) hi).trans
          ((le_max_right _ _).trans (le_max_right _ _))
  have hinner : ScaledBound dA
      (C c + C (weightPrefix V q) + ∑ i : Fin q, signed (ε i) (X i) * C (weightPrefix V i.val)) T := by
    simpa only [max_self] using (hC.add hP).add hsum
  have hfront : (b * n + c).totalDegree ≤ max (dB + dn) dC :=
    degree_add_le (degree_mul_le hb hn) hc
  have htwo : (2 * d - 1).totalDegree ≤ dD := by
    have hmul : (2 * d).totalDegree ≤ dD := by
      have hh := totalDegree_mul (2 : MvPolynomial σ ℤ) d
      have hconst : (2 : MvPolynomial σ ℤ).totalDegree = 0 := by
        change (C (2 : ℤ) : MvPolynomial σ ℤ).totalDegree = 0
        exact totalDegree_C _
      rw [hconst, zero_add] at hh
      exact hh.trans hd
    exact (totalDegree_sub _ _).trans (max_le hmul (by simp))
  have hback : (b * (2 * d - 1)).totalDegree ≤ dB + dD := degree_mul_le hb htwo
  have hres := ((ScaledBound.C dA (b * n + c)).mono
      (Nat.mul_le_mul_left 2 hfront)).sub
    (((ScaledBound.C dA (b * (2 * d - 1))).mono
      (Nat.mul_le_mul_left 2 hback)).mul hinner)
  exact hres

/-- A generic substitution degree bound for the refined construction.
The right side counts sign factors; no signed-product expansion is needed. -/
theorem twice_totalDegree_compose_le (q : ℕ)
    (A V : Fin q → MvPolynomial σ ℤ) (n b c d : MvPolynomial σ ℤ)
    (dA dV : Fin q → ℕ) (dn dB dC dD : ℕ)
    (hA : ∀ i, (A i).totalDegree ≤ dA i)
    (hV : ∀ i, (V i).totalDegree ≤ dV i)
    (hn : n.totalDegree ≤ dn) (hb : b.totalDegree ≤ dB)
    (hc : c.totalDegree ≤ dC) (hd : d.totalDegree ≤ dD) :
    2 * (compose q A V n b c d).totalDegree ≤
      2 ^ q * factorBudget q dA dV dn dB dC dD := by
  classical
  let f := parameterSubstitution q V n b c d
  have hprod : ScaledBound dA (map f (rawProduct q))
      (2 ^ q * factorBudget q dA dV dn dB dC dD) := by
    rw [rawProduct, map_prod]
    have hh := ScaledBound.prod Finset.univ
      (fun ε : Fin q → Bool => map f (rawFactor q ε))
      (fun _ => factorBudget q dA dV dn dB dC dD)
      (fun ε _ => scaledBound_map_rawFactor q V n b c d dA dV dn dB dC dD
        hV hn hb hc hd ε)
    simpa using hh
  have hex : expand 2 (map f (core q)) = map f (rawProduct q) := by
    rw [← map_expand, expand_two_core]
  have hh := totalDegree_eval₂_le_of_expand_bound dA (map f (core q)) A hA
    (2 ^ q * factorBudget q dA dV dn dB dC dD) (hex.symm ▸ hprod)
  simpa only [eval₂_map, RingHom.id_comp, compose, f] using hh

/-- A prefix plus its next weight is bounded by the full sum of weights. -/
theorem prefixDegree_add_le_sum {q : ℕ} (dV : Fin q → ℕ) (i : Fin q) :
    prefixDegree dV i.val + dV i ≤ ∑ j : Fin q, dV j := by
  classical
  have hnot : i ∉ Finset.univ.filter (fun j : Fin q => j.val < i.val) := by simp
  have hh := Finset.sum_le_sum_of_subset (f := dV)
    (Finset.subset_univ (insert i
      (Finset.univ.filter (fun j : Fin q => j.val < i.val))))
  rw [Finset.sum_insert hnot] at hh
  simpa only [prefixDegree, Nat.add_comm] using hh

/-- A practical parameter budget: if each radical's degree is at most
twice the corresponding weight degree, the whole inner expression is
bounded by the larger of the parameter degree and the sum of weights. -/
theorem factorBudget_le (q : ℕ) (dA dV : Fin q → ℕ) (dn dB dC dD : ℕ)
    (hAV : ∀ i, dA i ≤ 2 * dV i)
    (hfront : dn ≤ dD + max dC (∑ i : Fin q, dV i)) :
    factorBudget q dA dV dn dB dC dD ≤
      2 * (dB + dD + max dC (∑ i : Fin q, dV i)) := by
  classical
  let T := max dC (∑ i : Fin q, dV i)
  have hC : dC ≤ T := le_max_left _ _
  have hV : (∑ i : Fin q, dV i) ≤ T := le_max_right _ _
  have hP : prefixDegree dV q = ∑ i : Fin q, dV i := by
    simp [prefixDegree]
  have hinner : innerBudget q dA dV dC ≤ 2 * T := by
    unfold innerBudget
    apply max_le
    · omega
    · apply max_le
      · rw [hP]
        omega
      · apply Finset.sup_le
        intro i hi
        have hprefix := prefixDegree_add_le_sum dV i
        have hiA := hAV i
        omega
  unfold factorBudget
  apply max_le
  · have hn : dn ≤ dD + T := hfront
    omega
  · omega

/-- Degree bound used for the refined six-square and five-square products.
Coefficient parameters are arbitrary polynomials; all their degrees enter
the bound explicitly. -/
theorem totalDegree_compose_le (q : ℕ)
    (A V : Fin q → MvPolynomial σ ℤ) (n b c d : MvPolynomial σ ℤ)
    (dA dV : Fin q → ℕ) (dn dB dC dD : ℕ)
    (hA : ∀ i, (A i).totalDegree ≤ dA i)
    (hV : ∀ i, (V i).totalDegree ≤ dV i)
    (hn : n.totalDegree ≤ dn) (hb : b.totalDegree ≤ dB)
    (hc : c.totalDegree ≤ dC) (hd : d.totalDegree ≤ dD)
    (hAV : ∀ i, dA i ≤ 2 * dV i)
    (hfront : dn ≤ dD + max dC (∑ i : Fin q, dV i)) :
    (compose q A V n b c d).totalDegree ≤
      2 ^ q * (dB + dD + max dC (∑ i : Fin q, dV i)) := by
  have hh := twice_totalDegree_compose_le q A V n b c d dA dV dn dB dC dD
    hA hV hn hb hc hd
  have hbnd := Nat.mul_le_mul_left (2 ^ q)
    (factorBudget_le q dA dV dn dB dC dD hAV hfront)
  have hfinal := hh.trans hbnd
  nlinarith

/-- The six-square numerical budget from the refined 1976 construction. -/
theorem totalDegree_compose_six_le
    (A V : Fin 6 → MvPolynomial σ ℤ) (n b c d : MvPolynomial σ ℤ)
    (hA : ∀ i, (A i).totalDegree ≤ ![6, 6, 184, 14, 18, 22] i)
    (hV : ∀ i, (V i).totalDegree ≤ ![3, 3, 92, 7, 9, 11] i)
    (hn : n.totalDegree ≤ 1) (hb : b.totalDegree ≤ 34)
    (hc : c.totalDegree ≤ 2) (hd : d.totalDegree ≤ 50) :
    (compose 6 A V n b c d).totalDegree ≤ 13376 := by
  have hh := twice_totalDegree_compose_le 6 A V n b c d
    ![6, 6, 184, 14, 18, 22] ![3, 3, 92, 7, 9, 11] 1 34 2 50
    hA hV hn hb hc hd
  have hbudget : factorBudget 6 ![6, 6, 184, 14, 18, 22]
      ![3, 3, 92, 7, 9, 11] 1 34 2 50 = 418 := by decide
  rw [hbudget] at hh
  omega

/-- The five-square numerical budget after replacing the first two tests. -/
theorem totalDegree_compose_five_le
    (A V : Fin 5 → MvPolynomial σ ℤ) (n b c d : MvPolynomial σ ℤ)
    (hA : ∀ i, (A i).totalDegree ≤ ![22, 184, 14, 18, 22] i)
    (hV : ∀ i, (V i).totalDegree ≤ ![11, 92, 7, 9, 11] i)
    (hn : n.totalDegree ≤ 1) (hb : b.totalDegree ≤ 34)
    (hc : c.totalDegree ≤ 2) (hd : d.totalDegree ≤ 50) :
    (compose 5 A V n b c d).totalDegree ≤ 6848 := by
  have hh := twice_totalDegree_compose_le 5 A V n b c d
    ![22, 184, 14, 18, 22] ![11, 92, 7, 9, 11] 1 34 2 50
    hA hV hn hb hc hd
  have hbudget : factorBudget 5 ![22, 184, 14, 18, 22]
      ![11, 92, 7, 9, 11] 1 34 2 50 = 428 := by decide
  rw [hbudget] at hh
  omega

end

end Diophantine.RefinedRelationCombiningPolynomial
