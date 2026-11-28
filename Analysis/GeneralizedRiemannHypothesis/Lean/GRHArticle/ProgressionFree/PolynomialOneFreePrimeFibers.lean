import GRHArticle.ProgressionFree.PolynomialRationalRatios
import GRHArticle.ProgressionFree.PolynomialRoughCount
import Mathlib.Combinatorics.Additive.AP.Three.Defs

/-!
# One free prime for rational-function ratios

The nonconstant-ratio convention is equivalent to nontrivial steps
between monic prime-factor multiplicities. Fixing a monic cofactor
allows an arbitrary arithmetic-progression-free set of exponents at
one designated prime without permitting steps at any other prime.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators

variable {F : Type*} [Field F]

/-- The multiplicity of the prescribed monic irreducible in a polynomial. -/
noncomputable def polynomialPrimeExponent (P f : F[X]) : ℕ :=
  (normalizedFactors f).count P

private noncomputable def oneFreePrimeCofactorFactors (P f : F[X]) : Multiset F[X] :=
  (normalizedFactors f).filter (· ≠ P)

/-- Remove the leading scalar and all powers of the prescribed monic prime. -/
noncomputable def oneFreePrimeCofactor (P f : F[X]) : F[X] :=
  (oneFreePrimeCofactorFactors P f).prod

theorem polynomial_eq_scalar_mul_oneFreePrimeCofactor_mul_pow (P f : F[X]) :
    C f.leadingCoeff * oneFreePrimeCofactor P f * P^(polynomialPrimeExponent P f) = f := by
  have hprod := Multiset.prod_filter_mul_prod_filter_not (s := normalizedFactors f) (Eq P)
  rw [← Multiset.pow_count] at hprod
  have h : P^(polynomialPrimeExponent P f) * oneFreePrimeCofactor P f =
      (normalizedFactors f).prod := by
    simpa only [polynomialPrimeExponent, oneFreePrimeCofactor, oneFreePrimeCofactorFactors,
      ne_comm] using hprod
  rw [mul_assoc, mul_comm (oneFreePrimeCofactor P f), h,
    Polynomial.leadingCoeff_mul_prod_normalizedFactors]

theorem monic_oneFreePrimeCofactor (P f : F[X]) : (oneFreePrimeCofactor P f).Monic := by
  simpa only [oneFreePrimeCofactor, Multiset.map_id] using
    Polynomial.monic_multiset_prod_of_monic (oneFreePrimeCofactorFactors P f) id (fun p hp ↦ by
      have hp' := (Multiset.mem_filter.mp hp).1
      exact (Polynomial.normalize_eq_self_iff_monic (irreducible_of_normalized_factor p hp').ne_zero).mp
        (normalize_normalized_factor p hp'))

private theorem normalizedFactors_oneFreePrimeCofactor (P f : F[X]) :
    normalizedFactors (oneFreePrimeCofactor P f) = oneFreePrimeCofactorFactors P f := by
  rw [oneFreePrimeCofactor, normalizedFactors_prod_eq (oneFreePrimeCofactorFactors P f) (fun p hp ↦
    irreducible_of_normalized_factor p (Multiset.mem_filter.mp hp).1)]
  rw [Multiset.map_congr (s := oneFreePrimeCofactorFactors P f) rfl
    (f := normalize) (g := id) (fun p hp ↦
      normalize_normalized_factor p (Multiset.mem_filter.mp hp).1), Multiset.map_id]

theorem polynomialPrimeExponent_oneFreePrimeCofactor {P p f : F[X]} :
    polynomialPrimeExponent p (oneFreePrimeCofactor P f) =
      if p = P then 0 else polynomialPrimeExponent p f := by
  simp [polynomialPrimeExponent, normalizedFactors_oneFreePrimeCofactor,
    oneFreePrimeCofactorFactors, Multiset.count_filter]

theorem not_dvd_oneFreePrimeCofactor {P : F[X]} (hm : P.Monic) (hi : Irreducible P) (f : F[X]) :
    ¬ P ∣ oneFreePrimeCofactor P f := by
  intro h
  have hp := (Polynomial.mem_normalizedFactors_iff (monic_oneFreePrimeCofactor P f).ne_zero).mpr
    ⟨hi, hm, h⟩
  rw [normalizedFactors_oneFreePrimeCofactor] at hp
  exact (Multiset.mem_filter.mp hp).2 rfl

theorem polynomialPrimeExponent_mul (P : F[X]) {f g : F[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    polynomialPrimeExponent P (f*g) = polynomialPrimeExponent P f + polynomialPrimeExponent P g := by
  simp [polynomialPrimeExponent, normalizedFactors_mul hf hg]

theorem natDegree_eq_oneFreePrimeCofactor_add_exponent
    {P f : F[X]} (hP : P.natDegree = 1) (hf : f ≠ 0) :
    f.natDegree = (oneFreePrimeCofactor P f).natDegree + polynomialPrimeExponent P f := by
  have hp : P ≠ 0 := by intro he; simp [he] at hP
  have hc := leadingCoeff_ne_zero.mpr hf
  have h := congrArg natDegree (polynomial_eq_scalar_mul_oneFreePrimeCofactor_mul_pow P f)
  rw [natDegree_mul (mul_ne_zero (C_ne_zero.mpr hc) (monic_oneFreePrimeCofactor P f).ne_zero)
    (pow_ne_zero _ hp), natDegree_C_mul hc, natDegree_pow, hP, mul_one] at h
  exact h.symm

private theorem normalizedFactors_scalar_mul_cofactor_mul_pow
    {P g : F[X]} {a : F} (hP : P.Monic) (hi : Irreducible P) (hg : g.Monic)
    (ha : a ≠ 0) (e : ℕ) :
    normalizedFactors (C a * g * P^e) =
      normalizedFactors g + Multiset.replicate e P := by
  have hCa := C_ne_zero.mpr ha
  have hn : normalize P = P := (Polynomial.normalize_eq_self_iff_monic hi.ne_zero).mpr hP
  have hCu : IsUnit (C a : F[X]) := (IsUnit.map C (isUnit_iff_ne_zero.mpr ha))
  rw [normalizedFactors_mul (mul_ne_zero hCa hg.ne_zero) (pow_ne_zero _ hi.ne_zero),
    normalizedFactors_mul hCa hg.ne_zero, normalizedFactors_of_isUnit hCu, zero_add,
    hi.normalizedFactors_pow, hn]

/-- Exact multiplicity readback for a scalar times a cofactor times a prime power. -/
theorem polynomialPrimeExponent_scalar_mul_cofactor_mul_pow
    {P g : F[X]} {a : F} (hP : P.Monic) (hi : Irreducible P) (hg : g.Monic)
    (hd : ¬ P ∣ g) (ha : a ≠ 0) (e : ℕ) :
    polynomialPrimeExponent P (C a * g * P^e) = e := by
  have hmem : P ∉ normalizedFactors g := fun h ↦
    hd ((Polynomial.mem_normalizedFactors_iff hg.ne_zero).mp h).2.2
  rw [polynomialPrimeExponent, normalizedFactors_scalar_mul_cofactor_mul_pow hP hi hg ha e,
    Multiset.count_add, Multiset.count_eq_zero.mpr hmem, Multiset.count_replicate_self, zero_add]

/-- Exact monic cofactor readback for a scalar times a cofactor times a prime power. -/
theorem oneFreePrimeCofactor_scalar_mul_cofactor_mul_pow
    {P g : F[X]} {a : F} (hP : P.Monic) (hi : Irreducible P) (hg : g.Monic)
    (hd : ¬ P ∣ g) (ha : a ≠ 0) (e : ℕ) :
    oneFreePrimeCofactor P (C a * g * P^e) = g := by
  have hmem : P ∉ normalizedFactors g := fun h ↦
    hd ((Polynomial.mem_normalizedFactors_iff hg.ne_zero).mp h).2.2
  unfold oneFreePrimeCofactor oneFreePrimeCofactorFactors
  rw [normalizedFactors_scalar_mul_cofactor_mul_pow hP hi hg ha e, Multiset.filter_add]
  have h₁ : (normalizedFactors g).filter (· ≠ P) = normalizedFactors g := by
    apply Multiset.filter_eq_self.mpr
    intro p hp he
    exact hmem (he ▸ hp)
  have h₂ : (Multiset.replicate e P).filter (· ≠ P) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro p hp
    exact not_not.mpr (Multiset.eq_of_mem_replicate hp)
  rw [h₁, h₂, add_zero]
  simpa only [hg.leadingCoeff, map_one, one_mul] using Polynomial.leadingCoeff_mul_prod_normalizedFactors g

/-- A monic cofactor avoiding the chosen prime and satisfying the greedy
multiplicity restriction at each other prime. -/
def OneFreePrimeAdmissibleCofactor (P g : F[X]) : Prop :=
  g.Monic ∧ ¬ P ∣ g ∧ ∀ p : F[X], polynomialPrimeExponent p g ∈ greedyExponents

/-- Assign a possibly different exponent set to each admissible cofactor.
The choice is independent of the nonzero leading scalar. -/
def oneFreePrimeFamily (P : F[X]) (H : F[X] → Set ℕ) : Set F[X] :=
  {f | f ≠ 0 ∧ OneFreePrimeAdmissibleCofactor P (oneFreePrimeCofactor P f) ∧
    polynomialPrimeExponent P f ∈ H (oneFreePrimeCofactor P f)}

/-- Such an assignment is free of rational-function ratio progressions
if its individual exponent fibers are arithmetic-progression-free. -/
theorem rationalFunctionRatioThreeGPFree_oneFreePrimeFamily
    (P : F[X]) (H : F[X] → Set ℕ) (hH : ∀ g, ThreeAPFree (H g)) :
    RationalFunctionRatioThreeGPFree (oneFreePrimeFamily P H) := by
  intro a b c ha hb hc ha' hb' hc' he
  have heq (p : F[X]) : polynomialPrimeExponent p a + polynomialPrimeExponent p c =
      polynomialPrimeExponent p b + polynomialPrimeExponent p b := by
    have h := congrArg (polynomialPrimeExponent p) he
    simpa only [polynomialPrimeExponent_mul p ha hc, polynomialPrimeExponent_mul p hb hb] using h
  obtain ⟨_, haG, haE⟩ := ha'
  obtain ⟨_, hbG, hbE⟩ := hb'
  obtain ⟨_, hcG, hcE⟩ := hc'
  have hp (p : F[X]) (hne : p ≠ P) :
      polynomialPrimeExponent p a = polynomialPrimeExponent p b ∧
        polynomialPrimeExponent p b = polynomialPrimeExponent p c := by
    have hmem (f : F[X]) (hf : OneFreePrimeAdmissibleCofactor P (oneFreePrimeCofactor P f)) :
        polynomialPrimeExponent p f ∈ greedyExponents := by
      simpa only [polynomialPrimeExponent_oneFreePrimeCofactor, if_neg hne] using hf.2.2 p
    have h := (threeAPFree_iff_eq_right.mp threeAPFree_greedyExponents)
      (hmem a haG) (hmem b hbG) (hmem c hcG) (heq p)
    have h' := heq p
    omega
  have hcofactor (f g : F[X])
      (h : ∀ p : F[X], p ≠ P → polynomialPrimeExponent p f = polynomialPrimeExponent p g) :
      oneFreePrimeCofactor P f = oneFreePrimeCofactor P g := by
    apply congrArg Multiset.prod
    apply Multiset.ext.mpr
    intro p
    by_cases he : p = P
    · simp [oneFreePrimeCofactorFactors, he]
    · simpa [polynomialPrimeExponent, oneFreePrimeCofactorFactors, he] using h p he
  have hab := hcofactor a b (fun p h ↦ (hp p h).1)
  have hbc := hcofactor b c (fun p h ↦ (hp p h).2)
  have hep := (threeAPFree_iff_eq_right.mp (hH (oneFreePrimeCofactor P b)))
    (hab ▸ haE) hbE (hbc.symm ▸ hcE) (heq P)
  have habP : polynomialPrimeExponent P a = polynomialPrimeExponent P b := by
    have h := heq P
    omega
  let t := b.leadingCoeff / a.leadingCoeff
  have hs : a.leadingCoeff * t = b.leadingCoeff := by
    dsimp [t]
    field_simp [leadingCoeff_ne_zero.mpr ha]
  refine ⟨t, ?_⟩
  calc
    b = C b.leadingCoeff * oneFreePrimeCofactor P b * P^(polynomialPrimeExponent P b) :=
      (polynomial_eq_scalar_mul_oneFreePrimeCofactor_mul_pow P b).symm
    _ = (C a.leadingCoeff * oneFreePrimeCofactor P a * P^(polynomialPrimeExponent P a)) * C t := by
      rw [← hab, ← habP, ← hs, map_mul]
      ring
    _ = a * C t := by rw [polynomial_eq_scalar_mul_oneFreePrimeCofactor_mul_pow]

variable [Fintype F]

/-- The actual monic admissible cofactors of degree `n`. -/
noncomputable def oneFreePrimeCofactorLayer (P : F[X]) (n : ℕ) : Finset F[X] :=
  (monicLayer F n).filter (OneFreePrimeAdmissibleCofactor P)

/-- Membership in a cofactor layer includes monicity and exclusion of the chosen prime. -/
theorem mem_oneFreePrimeCofactorLayer {P g : F[X]} {n : ℕ} :
    g ∈ oneFreePrimeCofactorLayer P n ↔ g.natDegree = n ∧ OneFreePrimeAdmissibleCofactor P g := by
  simp only [oneFreePrimeCofactorLayer, Finset.mem_filter, mem_monicLayer]
  exact ⟨fun h ↦ ⟨h.1.2,h.2⟩, fun h ↦ ⟨⟨h.2.1,h.1⟩,h.2⟩⟩

end GRHArticle.ProgressionFree
