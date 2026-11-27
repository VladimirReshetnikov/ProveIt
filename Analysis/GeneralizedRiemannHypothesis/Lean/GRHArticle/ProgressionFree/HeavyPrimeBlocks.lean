import GRHArticle.ProgressionFree.IntegerPrimeBlockPartitions
import GRHArticle.ProgressionFree.LightPrimeBlocks

/-!
# A uniform bound on exceptional prime blocks

A block is heavy when the reciprocal sum of all its smooth patterns is
greater than two. If a block has width at most `d` and all its primes
exceed `2d`, a finite union bound makes the block light.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped Classical BigOperators

/-- Blocks at which the light-block optimization cannot be applied. -/
def HeavyPrimeBlock (P : Finset ℕ) : Prop :=
  2 < ∏ p : ↥P, (1-1/(p.val : ℝ))⁻¹

private theorem one_sub_sum_le_prod_one_sub {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (h0 : ∀ i ∈ S, 0 ≤ w i) (h1 : ∀ i ∈ S, w i ≤ 1) :
    1 - (∑ i ∈ S,w i) ≤ ∏ i ∈ S, (1-w i) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hW : 0 ≤ ∑ i ∈ S, w i := sum_nonneg fun i hi ↦ h0 i (mem_insert_of_mem hi)
    rw [sum_insert ha,prod_insert ha]
    calc
      _ ≤ (1-w a) * (1-∑ i ∈ S, w i) := by
        nlinarith [mul_nonneg (h0 a (mem_insert_self _ _)) hW]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (ih (fun i hi ↦ h0 i (mem_insert_of_mem hi)) (fun i hi ↦ h1 i (mem_insert_of_mem hi)))
        (sub_nonneg.mpr (h1 a (mem_insert_self _ _)))

/-- A heavy block of width at most `d` contains some prime at most `2d`. -/
theorem exists_small_prime_of_heavyPrimeBlock {P : Finset ℕ} {d : ℕ}
    (hd : 0 < d) (hP : ∀ p ∈ P, p.Prime) (hcard : P.card ≤ d) (hheavy : HeavyPrimeBlock P) :
    ∃ p ∈ P, p ≤ 2*d := by
  by_contra! hsmall
  have hsum : (∑ p ∈ P, (1:ℝ)/p) ≤ 1/2 := by
    calc
      _ ≤ ∑ p ∈ P, 1 / (2*(d : ℝ)) := by
        apply sum_le_sum
        intro p hp
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast (hsmall p hp).le
      _ = (P.card : ℝ) / (2*(d : ℝ)) := by
        rw [sum_const,nsmul_eq_mul,mul_one_div]
      _ ≤ _ := by
        have hc : (P.card : ℝ) ≤ d := by exact_mod_cast hcard
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*(d:ℝ))]
        linarith only [hc]
  have hprod : (1/2 : ℝ) ≤ ∏ p ∈ P, (1-1/(p:ℝ)) := by
    refine (show (1/2 : ℝ) ≤ 1-(∑ p ∈ P,(1:ℝ)/p) by linarith).trans ?_
    exact one_sub_sum_le_prod_one_sub P (fun p ↦ (1:ℝ)/p)
      (fun p _ ↦ by positivity) (fun p hp ↦ (div_le_one (by exact_mod_cast (hP p hp).pos)).mpr
        (by exact_mod_cast (hP p hp).one_lt.le))
  apply not_lt_of_ge _ hheavy
  rw [univ_eq_attach,prod_attach P (fun p : ℕ ↦ (1-1/(p:ℝ))⁻¹),prod_inv_distrib,← one_div,
    div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) hprod)]
  linarith

/-- Across a width-`d` prime partition, the exceptional blocks involve
at most `d * π(2d)` primes. -/
theorem exists_heavyPrimeBlocks (π : PrimeBlockPartition) {d : ℕ} (hd : 0 < d)
    (hwidth : ∀ P ∈ π.blocks, P.card ≤ d) :
    ∃ H : Finset (Finset ℕ), (∀ P, P ∈ H ↔ P ∈ π.blocks ∧ HeavyPrimeBlock P) ∧
      H.card ≤ (Nat.primesLE (2*d)).card ∧
      (H.biUnion id).card ≤ d * (Nat.primesLE (2*d)).card := by
  let S : Set (Finset ℕ) := {P | P ∈ π.blocks ∧ HeavyPrimeBlock P}
  have hp (P : S) : ∃ p : ↥(Nat.primesLE (2*d)), p.val ∈ P.val := by
    obtain ⟨p,hp,hp'⟩ := exists_small_prime_of_heavyPrimeBlock hd
      (π.primes P.val P.property.1) (hwidth P.val P.property.1) P.property.2
    exact ⟨⟨p,Nat.mem_primesLE.mpr ⟨hp',π.primes P.val P.property.1 p hp⟩⟩,hp⟩
  choose f hf using hp
  have hinj : Function.Injective f := by
    intro P Q he
    apply Subtype.ext
    by_contra hh
    exact (disjoint_left.mp (π.pairwiseDisjoint P.property.1 Q.property.1 hh)) (hf P) (he.symm ▸ hf Q)
  letI : Finite S := Finite.of_injective f hinj
  letI : Fintype S := Fintype.ofFinite S
  let H := S.toFinite.toFinset
  have hH (P : Finset ℕ) : P ∈ H ↔ P ∈ π.blocks ∧ HeavyPrimeBlock P :=
    S.toFinite.mem_toFinset
  have hcard : H.card ≤ (Nat.primesLE (2*d)).card := by
    rw [show H.card = Fintype.card S from S.toFinite.card_toFinset, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective f hinj
  refine ⟨H,hH,hcard,?_⟩
  calc
    _ ≤ ∑ P ∈ H, P.card := card_biUnion_le
    _ ≤ ∑ P ∈ H, d := sum_le_sum fun P hP ↦ hwidth P ((hH P).mp hP).1
    _ = H.card*d := by simp
    _ ≤ _ := by
      rw [Nat.mul_comm d]
      exact Nat.mul_le_mul_right d hcard

end GRHArticle.ProgressionFree
