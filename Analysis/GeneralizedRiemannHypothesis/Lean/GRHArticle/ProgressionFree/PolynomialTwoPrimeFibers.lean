import GRHArticle.ProgressionFree.PolynomialDensitySupremum
import GRHArticle.ProgressionFree.PolynomialRoughCount
import Mathlib.Combinatorics.Additive.AP.Three.Defs

/-!
# Two linear primes in polynomial progression-free sets

Removing the two prime powers from a nonzero polynomial leaves a monic
residual polynomial and its leading coefficient. The resulting exponent
pairs in each class lie in a triangle, and the rows and columns are
three-term arithmetic-progression-free.
-/

namespace GRHArticle.ProgressionFree

open Polynomial UniqueFactorizationMonoid
open scoped Classical BigOperators

variable {F : Type*} [Field F]

/-- The sum of the one-coordinate Roth bounds for a triangle of side length `L`. -/
def twoPrimeRothRows (L : ℕ) : ℕ :=
  ∑ i ∈ Finset.range L, rothNumberNat (L-i)

/-- The three side lengths at which a new unit of deficit applies. -/
def twoPrimePenalty (L : ℕ) : ℕ :=
  (if 9 ≤ L then 1 else 0) + (if 20 ≤ L then 1 else 0) + (if 30 ≤ L then 1 else 0)

/-- The combinatorial input required by the density transfer. -/
def TwoPrimeTriangleBound : Prop :=
  ∀ {L : ℕ} (A : Finset (ℕ × ℕ)),
    (∀ x ∈ A, x.1+x.2 < L) →
    (∀ i : ℕ, ThreeAPFree {j : ℕ | (i,j) ∈ A}) →
    (∀ j : ℕ, ThreeAPFree {i : ℕ | (i,j) ∈ A}) →
    A.card + twoPrimePenalty L ≤ twoPrimeRothRows L

/-- The resulting bound on a class with remaining degree budget `t`. -/
def twoPrimeFiberMaximum (t : ℕ) : ℕ :=
  twoPrimeRothRows (t+1) - twoPrimePenalty (t+1)

namespace PolynomialTwoPrimeFibers

private noncomputable def residualFactors (P Q f : F[X]) : Multiset F[X] :=
  (normalizedFactors f).filter fun p ↦ p ≠ P ∧ p ≠ Q

private noncomputable def residual (P Q f : F[X]) : F[X] :=
  (residualFactors P Q f).prod

private noncomputable def exponents (P Q f : F[X]) : ℕ × ℕ :=
  ((normalizedFactors f).count P, (normalizedFactors f).count Q)

private theorem polynomial_eq (P Q f : F[X]) (hne : P ≠ Q) :
    C f.leadingCoeff * residual P Q f *
      P^(exponents P Q f).1 * Q^(exponents P Q f).2 = f := by
  let s := normalizedFactors f
  have hQ : (s.filter (fun p ↦ ¬ P = p)).filter (Eq Q) = s.filter (Eq Q) := by
    ext p
    simp only [Multiset.count_filter]
    by_cases h₁ : Q = p
    · subst p
      simp [hne]
    · simp [h₁]
  have hPQ : (s.filter (fun p ↦ ¬ P = p)).filter (fun p ↦ ¬ Q = p) =
      residualFactors P Q f := by
    ext p
    simp [s, residualFactors, ne_comm, and_comm]
  have h := Multiset.prod_filter_mul_prod_filter_not (s := s) (Eq P)
  have h' := Multiset.prod_filter_mul_prod_filter_not (s := s.filter (fun p ↦ ¬ P = p)) (Eq Q)
  rw [hQ, hPQ, ← Multiset.pow_count] at h'
  rw [← Multiset.pow_count, ← h'] at h
  unfold residual exponents
  change C f.leadingCoeff * (residualFactors P Q f).prod * P^s.count P * Q^s.count Q = f
  calc
    _ = C f.leadingCoeff * (P^s.count P * (Q^s.count Q * (residualFactors P Q f).prod)) := by ac_rfl
    _ = f := by rw [h, Polynomial.leadingCoeff_mul_prod_normalizedFactors]

private theorem residual_monic (P Q f : F[X]) : (residual P Q f).Monic := by
  simpa only [residual, Multiset.map_id] using
    Polynomial.monic_multiset_prod_of_monic (residualFactors P Q f) id (fun p hp ↦ by
      have hp' := (Multiset.mem_filter.mp hp).1
      exact (Polynomial.normalize_eq_self_iff_monic (irreducible_of_normalized_factor p hp').ne_zero).mp
        (normalize_normalized_factor p hp'))

private theorem normalizedFactors_residual (P Q f : F[X]) :
    normalizedFactors (residual P Q f) = residualFactors P Q f := by
  rw [residual, normalizedFactors_prod_eq (residualFactors P Q f) (fun p hp ↦
    irreducible_of_normalized_factor p (Multiset.mem_filter.mp hp).1)]
  rw [Multiset.map_congr (s := residualFactors P Q f) rfl (f := normalize) (g := id) (fun p hp ↦
    normalize_normalized_factor p (Multiset.mem_filter.mp hp).1), Multiset.map_id]

private theorem residual_excludes {P Q : F[X]} (hmP : P.Monic) (hmQ : Q.Monic)
    (hiP : Irreducible P) (hiQ : Irreducible Q) (f : F[X]) :
    ∀ p ∈ ({P,Q} : Finset F[X]), ¬ p ∣ residual P Q f := by
  intro p hp hd
  have hpair := Finset.mem_insert.mp hp
  have hmem : p ∈ normalizedFactors (residual P Q f) :=
    (Polynomial.mem_normalizedFactors_iff (residual_monic P Q f).ne_zero).mpr (by
      rcases hpair with rfl | h
      · exact ⟨hiP, hmP, hd⟩
      · rcases Finset.mem_singleton.mp h with rfl
        exact ⟨hiQ, hmQ, hd⟩)
  rw [normalizedFactors_residual] at hmem
  exact hpair.elim (Multiset.mem_filter.mp hmem).2.1
    (fun h ↦ (Multiset.mem_filter.mp hmem).2.2 (Finset.mem_singleton.mp h))

private theorem degree_eq {P Q f : F[X]} (hPQ : P ≠ Q)
    (hP : P.natDegree = 1) (hQ : Q.natDegree = 1) (hf : f ≠ 0) :
    f.natDegree = (residual P Q f).natDegree + ((exponents P Q f).1 + (exponents P Q f).2) := by
  have hp : P ≠ 0 := by intro h; simp [h] at hP
  have hq : Q ≠ 0 := by intro h; simp [h] at hQ
  have hC := C_ne_zero.mpr (leadingCoeff_ne_zero.mpr hf)
  have hr := (residual_monic P Q f).ne_zero
  have h := congrArg natDegree (polynomial_eq P Q f hPQ)
  rw [natDegree_mul (mul_ne_zero (mul_ne_zero hC hr) (pow_ne_zero _ hp)) (pow_ne_zero _ hq),
    natDegree_mul (mul_ne_zero hC hr) (pow_ne_zero _ hp),
    natDegree_C_mul (leadingCoeff_ne_zero.mpr hf), natDegree_pow, natDegree_pow, hP, hQ,
    mul_one, mul_one] at h
  omega

variable [Fintype F]

private noncomputable def selected (E : Set F[X]) (N : ℕ) : Finset F[X] :=
  (polynomialDegreeLTFinset F (N+1)).filter fun f ↦ f ∈ E ∧ f ≠ 0

private theorem mem_selected {E : Set F[X]} {N : ℕ} {f : F[X]} :
    f ∈ selected E N ↔ f ∈ E ∧ f ≠ 0 ∧ f.natDegree ≤ N := by
  simp only [selected, Finset.mem_filter, mem_polynomialDegreeLTFinset]
  constructor
  · rintro ⟨hd, he, h0⟩
    rw [degree_eq_natDegree h0, Nat.cast_lt, Nat.lt_succ_iff] at hd
    exact ⟨he, h0, hd⟩
  · rintro ⟨he, h0, hd⟩
    refine ⟨?_, he, h0⟩
    rwa [degree_eq_natDegree h0, Nat.cast_lt, Nat.lt_succ_iff]

private noncomputable def classKey (P Q f : F[X]) : F × F[X] :=
  (f.leadingCoeff, residual P Q f)

private noncomputable def budgetLayer (P Q : F[X]) (E : Set F[X]) (N t : ℕ) :
    Finset F[X] := (selected E N).filter fun f ↦ N - (residual P Q f).natDegree = t

omit [Fintype F] in
private theorem threeAPFree_pow {E : Set F[X]} (hE : PolynomialRatioThreeGPFree E)
    {b R : F[X]} (hb : b ≠ 0) (hR : R.natDegree = 1) :
    ThreeAPFree {n : ℕ | b * R^n ∈ E} := by
  rw [threeAPFree_iff_eq_right]
  intro a ha m hm c hc h
  change b * R^a ∈ E at ha
  change b * R^m ∈ E at hm
  change b * R^c ∈ E at hc
  have hR₀ : R ≠ 0 := by intro h0; simp [h0] at hR
  suffices ∀ x y z : ℕ, b * R^x ∈ E → b * R^y ∈ E → b * R^z ∈ E →
      x+z=y+y → x≤z → x=z by
    rcases le_total a c with hle | hle
    · exact this a m c ha hm hc h hle
    · exact (this c m a hc hm ha (by omega) hle).symm
  intro x y z hx hy hz hsum hle
  by_contra hne
  have hstep : 0 < y-x := by omega
  exact hE (b * R^x) (R^(y-x)) (mul_ne_zero hb (pow_ne_zero _ hR₀))
    (by simpa [natDegree_pow, hR] using hstep) ⟨hx, by
      rwa [mul_assoc, ← pow_add, show x+(y-x)=y by omega], by
      rwa [mul_assoc, mul_assoc, ← pow_add, ← pow_add, show x+((y-x)+(y-x))=z by omega]⟩

private theorem card_fiber_le {P Q : F[X]} (hPQ : P ≠ Q)
    (hP : P.natDegree = 1) (hQ : Q.natDegree = 1)
    {E : Set F[X]} (hE : PolynomialRatioThreeGPFree E) (htriangle : TwoPrimeTriangleBound)
    (N t : ℕ) (k : F × F[X]) :
    ((budgetLayer P Q E N t).filter fun f ↦ classKey P Q f = k).card ≤
      twoPrimeFiberMaximum t := by
  let B := (budgetLayer P Q E N t).filter fun f ↦ classKey P Q f = k
  let A := B.image (exponents P Q)
  have hrep (f : F[X]) (hf : f ∈ B) :
      C k.1 * k.2 * P^(exponents P Q f).1 * Q^(exponents P Q f).2 = f := by
    have hk := (Finset.mem_filter.mp hf).2
    have hc : f.leadingCoeff = k.1 := congrArg Prod.fst hk
    have hg : residual P Q f = k.2 := congrArg Prod.snd hk
    rw [← hc, ← hg]
    exact polynomial_eq P Q f hPQ
  have hbase (f : F[X]) (hf : f ∈ B) : f ∈ E ∧ f ≠ 0 ∧ f.natDegree ≤ N :=
    mem_selected.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).1
  have hcard : A.card = B.card := by
    apply Finset.card_image_of_injOn
    intro f hf g hg he
    rw [← hrep f hf, ← hrep g hg, he]
  have hbudget : ∀ e ∈ A, e.1+e.2 < t+1 := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨_, hf₀, hfN⟩ := hbase f hf
    have ht := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
    have hd := degree_eq hPQ hP hQ hf₀
    omega
  have heval (i j : ℕ) (h : (i,j) ∈ A) :
      C k.1 * k.2 * P^i * Q^j ∈ E := by
    obtain ⟨f, hf, he⟩ := Finset.mem_image.mp h
    have hfE := (hbase f hf).1
    rw [← hrep f hf, he] at hfE
    exact hfE
  by_cases hz : C k.1 * k.2 = 0
  · have hB : B = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun f hf ↦ by
      apply (hbase f hf).2.1
      simpa only [hz, zero_mul] using (hrep f hf).symm)
    change B.card ≤ _
    simp [hB]
  have hp : P ≠ 0 := by intro h; simp [h] at hP
  have hq : Q ≠ 0 := by intro h; simp [h] at hQ
  have hr (i : ℕ) : ThreeAPFree {j : ℕ | (i,j) ∈ A} :=
    (threeAPFree_pow hE (mul_ne_zero hz (pow_ne_zero _ hp)) hQ).mono
      (fun j hj ↦ heval i j hj)
  have hc (j : ℕ) : ThreeAPFree {i : ℕ | (i,j) ∈ A} :=
    (threeAPFree_pow hE (b := C k.1 * k.2 * Q^j) (mul_ne_zero hz (pow_ne_zero _ hq)) hP).mono
      (fun i hi ↦ by
        change C k.1 * k.2 * Q^j * P^i ∈ E
        simpa only [mul_right_comm (C k.1 * k.2) (P^i) (Q^j)] using heval i j hi)
  have h := htriangle A hbudget hr hc
  rw [hcard] at h
  unfold twoPrimeFiberMaximum
  change B.card ≤ _
  omega

private theorem card_budgetLayer_le {P Q : F[X]} (hPQ : P ≠ Q)
    (hmP : P.Monic) (hmQ : Q.Monic) (hiP : Irreducible P) (hiQ : Irreducible Q)
    (hP : P.natDegree = 1) (hQ : Q.natDegree = 1)
    {E : Set F[X]} (hE : PolynomialRatioThreeGPFree E) (ht : TwoPrimeTriangleBound)
    (N t : ℕ) :
    (budgetLayer P Q E N t).card ≤
      (Fintype.card F - 1) * (primeExcludingLayer {P,Q} (N-t)).card * twoPrimeFiberMaximum t := by
  let S := (Finset.univ.erase 0 : Finset F) ×ˢ primeExcludingLayer {P,Q} (N-t)
  have hmaps : Set.MapsTo (classKey P Q) (budgetLayer P Q E N t : Set F[X]) S := by
    intro f hf
    have hf' : f ∈ (selected E N).filter (fun f ↦ N-(residual P Q f).natDegree=t) := hf
    obtain ⟨hfB, hb⟩ := Finset.mem_filter.mp hf'
    obtain ⟨_, h0, hN⟩ := mem_selected.mp hfB
    have hd := degree_eq hPQ hP hQ h0
    have hrough : (residual P Q f).natDegree = N-t := by omega
    exact Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨leadingCoeff_ne_zero.mpr h0,
      Finset.mem_univ _⟩, mem_primeExcludingLayer.mpr
      ⟨residual_monic P Q f, hrough, residual_excludes hmP hmQ hiP hiQ f⟩⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hs := Finset.sum_le_sum (s := S) (fun k _ ↦ card_fiber_le hPQ hP hQ hE ht N t k)
  simpa only [S, Finset.sum_const, nsmul_eq_mul, Finset.card_product,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Nat.cast_id] using hs

/-- Finite degree-ball count after removing two chosen monic linear primes. -/
theorem card_polynomialBall_le {P Q : F[X]} (hPQ : P ≠ Q)
    (hmP : P.Monic) (hmQ : Q.Monic) (hiP : Irreducible P) (hiQ : Irreducible Q)
    (hP : P.natDegree = 1) (hQ : Q.natDegree = 1)
    {E : Set F[X]} (hE : PolynomialRatioThreeGPFree E) (ht : TwoPrimeTriangleBound)
    (N : ℕ) :
    ((polynomialDegreeLTFinset F (N+1)).filter (· ∈ E)).card ≤
      1 + (Fintype.card F - 1) * ∑ t ∈ Finset.range (N+1),
        (primeExcludingLayer {P,Q} (N-t)).card * twoPrimeFiberMaximum t := by
  let B := (polynomialDegreeLTFinset F (N+1)).filter (· ∈ E)
  have hpart := Finset.card_filter_add_card_filter_not (s := B) (fun f ↦ f ≠ 0)
  have hnz : (B.filter fun f ↦ f ≠ 0) = selected E N := by
    simp only [B, selected, Finset.filter_filter]
  have hzero : (B.filter fun f ↦ ¬ f ≠ 0).card ≤ 1 := by
    have hs : B.filter (fun f ↦ ¬ f ≠ 0) ⊆ {0} := by simp [Finset.subset_iff]
    simpa using Finset.card_le_card hs
  have hm : Set.MapsTo (fun f : F[X] ↦ N-(residual P Q f).natDegree)
      (selected E N : Set F[X]) (Finset.range (N+1)) :=
    fun f _ ↦ Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _))
  have hb := Finset.card_eq_sum_card_fiberwise hm
  change (selected E N).card = ∑ t ∈ Finset.range (N+1), (budgetLayer P Q E N t).card at hb
  have hbound := Finset.sum_le_sum (s := Finset.range (N+1))
    (fun t _ ↦ card_budgetLayer_le hPQ hmP hmQ hiP hiQ hP hQ hE ht N t)
  simp only [mul_assoc, ← Finset.mul_sum] at hbound
  rw [hnz, hb] at hpart
  change B.card ≤ _
  omega

end PolynomialTwoPrimeFibers
end GRHArticle.ProgressionFree
