import PolynomialFormulas.GaussianRadicals
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Polynomial.Radical

/-!
# Separable layers for Gaussian-rational quartics

A monic polynomial of degree at most four over the Gaussian rationals is a
product of four monic separable polynomials, with constant-one factors used as
padding.  This is useful when a root argument must retain multiplicities:
repeated irreducible factors can be placed in different separable layers.

The construction below uses the normalized irreducible-factor multiset.  In
particular, repetitions in that multiset remain repetitions among the layers;
they are not discarded by taking a squarefree radical.
-/

namespace LeanProofs.PolynomialFormulas

open Polynomial
open UniqueFactorizationMonoid

/-- A multiset of nonconstant monic polynomials has at least as much total
degree as it has elements. -/
private theorem card_le_sum_natDegree_of_irreducible_monic
    (s : Multiset GaussianRat[X])
    (hs : ∀ q ∈ s, Irreducible q ∧ q.Monic) :
    s.card ≤ (s.map Polynomial.natDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons q s ih =>
      have hq := hs q (by simp)
      have hs' : ∀ r ∈ s, Irreducible r ∧ r.Monic := by
        intro r hr
        exact hs r (by simp [hr])
      have hqpos : 0 < q.natDegree :=
        hq.2.natDegree_pos_of_not_isUnit hq.1.not_isUnit
      have hi := ih hs'
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
      omega

/-- The number of normalized irreducible factors of a monic Gaussian-rational
polynomial, counted with multiplicity, is bounded by its natural degree. -/
theorem normalizedFactors_card_le_natDegree (p : GaussianRat[X]) (hp : p.Monic) :
    (normalizedFactors p).card ≤ p.natDegree := by
  have hp0 := hp.ne_zero
  have hs : ∀ q ∈ normalizedFactors p, Irreducible q ∧ q.Monic := by
    intro q hq
    have h := (Polynomial.mem_normalizedFactors_iff hp0).mp hq
    exact ⟨h.1, h.2.1⟩
  have hprod : (normalizedFactors p).prod = p := by
    simpa [hp.leadingCoeff] using Polynomial.leadingCoeff_mul_prod_normalizedFactors p
  calc
    (normalizedFactors p).card
        ≤ ((normalizedFactors p).map Polynomial.natDegree).sum :=
          card_le_sum_natDegree_of_irreducible_monic _ hs
    _ = (normalizedFactors p).prod.natDegree :=
          (Polynomial.natDegree_multiset_prod_of_monic _ fun q hq => (hs q hq).2).symm
    _ = p.natDegree := by rw [hprod]

private theorem natDegree_sum_eq_of_four_monic
    {p p₀ p₁ p₂ p₃ : GaussianRat[X]}
    (h₀ : p₀.Monic) (h₁ : p₁.Monic) (h₂ : p₂.Monic) (h₃ : p₃.Monic)
    (hprod : p₀ * p₁ * p₂ * p₃ = p) :
    p₀.natDegree + p₁.natDegree + p₂.natDegree + p₃.natDegree = p.natDegree := by
  rw [← hprod, ((h₀.mul h₁).mul h₂).natDegree_mul h₃,
    (h₀.mul h₁).natDegree_mul h₂, h₀.natDegree_mul h₁]

/-- Every monic Gaussian-rational polynomial of degree at most four is a
product of four monic separable layers.  The natural degrees of the layers add
to the natural degree of the original polynomial.

Monicity already implies that `p` is nonzero.  Each nontrivial layer below is
one normalized irreducible factor of `p`; unused layers are `1`. -/
theorem exists_four_monic_separable_factors
    (p : GaussianRat[X]) (hp : p.Monic) (hdegree : p.natDegree ≤ 4) :
    ∃ p₀ p₁ p₂ p₃ : GaussianRat[X],
      p₀.Monic ∧ p₁.Monic ∧ p₂.Monic ∧ p₃.Monic ∧
      p₀.Separable ∧ p₁.Separable ∧ p₂.Separable ∧ p₃.Separable ∧
      p₀ * p₁ * p₂ * p₃ = p ∧
      p₀.natDegree + p₁.natDegree + p₂.natDegree + p₃.natDegree = p.natDegree := by
  let s := normalizedFactors p
  have hp0 := hp.ne_zero
  have hfactor : ∀ q ∈ s, q.Monic ∧ q.Separable := by
    intro q hq
    have h := (Polynomial.mem_normalizedFactors_iff hp0).mp hq
    exact ⟨h.2.1, h.1.separable⟩
  have hprod : s.prod = p := by
    dsimp [s]
    simpa [hp.leadingCoeff] using Polynomial.leadingCoeff_mul_prod_normalizedFactors p
  have hcard : s.card ≤ 4 :=
    (normalizedFactors_card_le_natDegree p hp).trans hdegree
  have hcases :
      s.card = 0 ∨ s.card = 1 ∨ s.card = 2 ∨ s.card = 3 ∨ s.card = 4 := by
    omega
  rcases hcases with hzero | hone | htwo | hthree | hfour
  · have hs : s = 0 := Multiset.card_eq_zero.mp hzero
    have hpone : (1 : GaussianRat[X]) = p := by simpa [hs] using hprod
    refine ⟨1, 1, 1, 1, monic_one, monic_one, monic_one, monic_one,
      separable_one, separable_one, separable_one, separable_one, ?_, ?_⟩
    · simpa using hpone
    · simp [← hpone]
  · obtain ⟨q, hs⟩ := Multiset.card_eq_one.mp hone
    have hq : q.Monic ∧ q.Separable := hfactor q (by simp [hs])
    have hqp : q = p := by simpa [hs] using hprod
    refine ⟨q, 1, 1, 1, hq.1, monic_one, monic_one, monic_one,
      hq.2, separable_one, separable_one, separable_one, ?_, ?_⟩
    · simpa using hqp
    · exact natDegree_sum_eq_of_four_monic hq.1 monic_one monic_one monic_one
        (by simpa using hqp)
  · obtain ⟨q, r, hs⟩ := Multiset.card_eq_two.mp htwo
    have hq : q.Monic ∧ q.Separable := hfactor q (by simp [hs])
    have hr : r.Monic ∧ r.Separable := hfactor r (by simp [hs])
    have hqrp : q * r = p := by simpa [hs] using hprod
    refine ⟨q, r, 1, 1, hq.1, hr.1, monic_one, monic_one,
      hq.2, hr.2, separable_one, separable_one, ?_, ?_⟩
    · simpa using hqrp
    · exact natDegree_sum_eq_of_four_monic hq.1 hr.1 monic_one monic_one
        (by simpa using hqrp)
  · obtain ⟨q, r, t, hs⟩ := Multiset.card_eq_three.mp hthree
    have hq : q.Monic ∧ q.Separable := hfactor q (by simp [hs])
    have hr : r.Monic ∧ r.Separable := hfactor r (by simp [hs])
    have ht : t.Monic ∧ t.Separable := hfactor t (by simp [hs])
    have hqrtp : q * r * t = p := by simpa [hs, mul_assoc] using hprod
    refine ⟨q, r, t, 1, hq.1, hr.1, ht.1, monic_one,
      hq.2, hr.2, ht.2, separable_one, ?_, ?_⟩
    · simpa using hqrtp
    · exact natDegree_sum_eq_of_four_monic hq.1 hr.1 ht.1 monic_one
        (by simpa using hqrtp)
  · obtain ⟨q, r, t, u, hs⟩ := Multiset.card_eq_four.mp hfour
    have hq : q.Monic ∧ q.Separable := hfactor q (by simp [hs])
    have hr : r.Monic ∧ r.Separable := hfactor r (by simp [hs])
    have ht : t.Monic ∧ t.Separable := hfactor t (by simp [hs])
    have hu : u.Monic ∧ u.Separable := hfactor u (by simp [hs])
    have hqrtup : q * r * t * u = p := by simpa [hs, mul_assoc] using hprod
    refine ⟨q, r, t, u, hq.1, hr.1, ht.1, hu.1,
      hq.2, hr.2, ht.2, hu.2, hqrtup, ?_⟩
    exact natDegree_sum_eq_of_four_monic hq.1 hr.1 ht.1 hu.1 hqrtup

end LeanProofs.PolynomialFormulas
