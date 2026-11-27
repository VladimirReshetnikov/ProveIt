import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothProducts
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Arbitrary allowed exponents at finitely many prime ideals

Sum the exact cylinders for all allowed tuples. The joint law factors
into independent geometric laws even when each local rule allows
infinitely many exponents.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors Classical

variable {K : Type*} [Field K] [NumberField K]

/-- Exponent of the specified prime ideal in a nonzero integral ideal. -/
noncomputable def primeExponent (p : HeightOneSpectrum (𝓞 K)) (I : (Ideal (𝓞 K))⁰) : ℕ :=
  multiplicity p.asIdeal I.val

theorem primeExponent_eq_iff (p : HeightOneSpectrum (𝓞 K)) (I : (Ideal (𝓞 K))⁰) (n : ℕ) :
    primeExponent p I = n ↔ p.asIdeal^n ∣ I.val ∧ ¬p.asIdeal^(n+1) ∣ I.val :=
  (FiniteMultiplicity.of_prime_left (Ideal.prime_of_isPrime p.ne_bot p.isPrime)
    (mem_nonZeroDivisors_iff_ne_zero.mp I.property)).multiplicity_eq_iff

/-- Reciprocal absolute norm of a prime ideal. -/
noncomputable def primeWeight (p : HeightOneSpectrum (𝓞 K)) : ℝ := (absNorm p.asIdeal : ℝ)⁻¹

theorem primeWeight_pos_lt_one (p : HeightOneSpectrum (𝓞 K)) : 0 < primeWeight p ∧ primeWeight p < 1 := by
  have hp : 0 < absNorm p.asIdeal := absNorm_pos_of_nonZeroDivisors (primeIdeal p)
  have hn : absNorm p.asIdeal ≠ 1 := fun h ↦ p.isPrime.ne_top (absNorm_eq_one_iff.mp h)
  have ht : (1:ℝ) < absNorm p.asIdeal := by exact_mod_cast (by omega : 1 < absNorm p.asIdeal)
  exact ⟨inv_pos.mpr (Nat.cast_pos.mpr hp), inv_lt_one_of_one_lt₀ ht⟩

/-- The mass of an arbitrary set of exponents in the geometric law. -/
noncomputable def localRuleMass (p : HeightOneSpectrum (𝓞 K)) (A : Set ℕ) : ℝ :=
  (1-primeWeight p) * ∑' n, A.indicator (fun k ↦ primeWeight p^k) n

/-- Ideals satisfying the given conditions at the primes of `S`. -/
def finiteLocalRule (S : Finset (HeightOneSpectrum (𝓞 K))) (A : HeightOneSpectrum (𝓞 K) → Set ℕ) :
    Set (Ideal (𝓞 K))⁰ := {I | ∀ p ∈ S, primeExponent p I ∈ A p}

theorem hasNaturalDensity_finiteLocalRule (S : Finset (HeightOneSpectrum (𝓞 K)))
    (A : HeightOneSpectrum (𝓞 K) → Set ℕ) :
    HasNaturalDensity (finiteLocalRule S A) (∏ p ∈ S, localRuleMass p (A p)) := by
  let T : Set (S → ℕ) := {e | ∀ p, e p ∈ A p.val}
  let f (p : S) (n : ℕ) := (A p.val).indicator (fun k ↦ primeWeight p.val^k) n
  have hsum (p : S) : Summable (f p) :=
    (summable_geometric_of_lt_one (primeWeight_pos_lt_one p.val).1.le
      (primeWeight_pos_lt_one p.val).2).indicator _
  have hpos (p : S) (n : ℕ) : 0 ≤ f p n := Set.indicator_nonneg
    (fun i _ ↦ pow_nonneg (primeWeight_pos_lt_one p.val).1.le i) _
  have hs := (hasSum_finiteExponentProduct f (fun p ↦ ∑' n, f p n)
    (fun p ↦ (hsum p).hasSum) hpos).tsum_eq
  have heq : finiteLocalRule S A = ⋃ e : T, (smoothMultiplier S e.val * ·) '' roughIdeals S := by
    ext I
    rw [Set.mem_iUnion]
    constructor
    · intro hI
      let e (p : S) := primeExponent p.val I
      refine ⟨⟨e, fun p ↦ hI p.val p.property⟩, (mem_smoothMultiplier_image_iff S e I).mpr ?_⟩
      exact fun p ↦ (primeExponent_eq_iff _ _ _).mp rfl
    · rintro ⟨e,he⟩ p hp
      let q : S := ⟨p,hp⟩
      exact ((primeExponent_eq_iff p I (e.val q)).mpr ((mem_smoothMultiplier_image_iff S e.val I).mp he q)) ▸ e.property q
  have hweight : (∑' e : T, (absNorm (smoothMultiplier S e.val).val : ℝ)⁻¹) =
      ∏ p : S, ∑' n, f p n := by
    rw [← hs, _root_.tsum_subtype T (fun e : S → ℕ ↦ (absNorm (smoothMultiplier S e).val : ℝ)⁻¹)]
    apply tsum_congr
    intro e
    by_cases he : e ∈ T
    · rw [Set.indicator_of_mem he, smoothMultiplier_invNorm]
      exact prod_congr rfl (fun p _ ↦ (Set.indicator_of_mem (he p) _).symm)
    · rw [Set.indicator_of_notMem he]
      obtain ⟨p,hp⟩ := not_forall.mp he
      exact (prod_eq_zero (mem_univ p) (Set.indicator_of_notMem hp _)).symm
  rw [heq]
  have hd := hasNaturalDensity_smoothTemplateProducts S T Set.Subset.rfl (hasNaturalDensity_roughIdeals S)
  rw [hweight] at hd
  convert hd using 1
  rw [← prod_coe_sort S (fun p ↦ localRuleMass p (A p)), ← prod_coe_sort S (fun p ↦ 1-(absNorm p.asIdeal : ℝ)⁻¹)]
  exact prod_mul_distrib

end GRHArticle.ProgressionFree.NumberFieldIdeals
