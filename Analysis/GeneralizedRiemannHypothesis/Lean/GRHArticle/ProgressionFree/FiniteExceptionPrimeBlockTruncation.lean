import GRHArticle.ProgressionFree.ExteriorPrimeBlockDensity
import GRHArticle.ProgressionFree.GreedyBlockWitnesses

/-!
# Removing large primes from a bounded set of exceptions

Freeze every removed coordinate at exponent zero. The resulting slices
remain progression-free. The discarded multiples of exceptional primes
have density at most the number of exceptions divided by the cutoff.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped Classical BigOperators

/-- Extend an exponent vector by zero on the removed coordinates. -/
noncomputable def zeroExtendPrimeBlockPattern (P Q : Finset ℕ) (v : ↥Q → ℕ) : ↥P → ℕ :=
  fun p ↦ if h : p.val ∈ Q then v ⟨p.val,h⟩ else 0

/-- A fixed zero slice of a prime-block rule. -/
def zeroSlicePrimeBlockRule {P Q : Finset ℕ} (R : Set (↥P → ℕ)) : Set (↥Q → ℕ) :=
  {v | zeroExtendPrimeBlockPattern P Q v ∈ R}

/-- Passing to a zero slice cannot introduce a nonconstant affine
progression of exponent vectors. -/
theorem kTermVectorAPFree_zeroSlicePrimeBlockRule {k : ℕ} {P Q : Finset ℕ}
    (hQP : Q ⊆ P) {R : Set (↥P → ℕ)} (hR : KTermVectorAPFree k R) :
    KTermVectorAPFree k (zeroSlicePrimeBlockRule (Q := Q) R) := by
  intro v a d hv ha
  let a' (p : ↥P) : ℤ := if h : p.val ∈ Q then a ⟨p.val,h⟩ else 0
  let d' (p : ↥P) : ℤ := if h : p.val ∈ Q then d ⟨p.val,h⟩ else 0
  have hAff (i : Fin k) (p : ↥P) :
      (zeroExtendPrimeBlockPattern P Q (v i) p : ℤ) = a' p + (i.val : ℤ)*d' p := by
    by_cases h : p.val ∈ Q
    · simpa only [zeroExtendPrimeBlockPattern,a',d',dif_pos h] using ha i ⟨p.val,h⟩
    · simp [zeroExtendPrimeBlockPattern,a',d',h]
  have hzero := hR (fun i ↦ zeroExtendPrimeBlockPattern P Q (v i)) a' d' hv hAff
  intro q
  simpa only [d',dif_pos q.property] using hzero ⟨q.val,hQP q.property⟩

/-- A reduced rule can move all its exceptions into the primes at most
`Z`, losing at most one reciprocal cutoff for each removed prime. -/
theorem exists_small_finiteExceptionPrimeRule_of_density {k d Z : ℕ} (hZ : 0 < Z)
    (S : Finset (Finset ℕ)) (R : (P : Finset ℕ) → Set (↥P → ℕ))
    (hpr : ∀ P ∈ S, ∀ p ∈ P, p.Prime)
    (hPair : (S : Set (Finset ℕ)).PairwiseDisjoint id)
    (hWidth : ∀ P ∈ S, P.card ≤ d) (hFree : ∀ P ∈ S, KTermVectorAPFree k (R P))
    {G : Set ℕ} (h0 : 0 ∈ G) (h1 : 1 ∈ G) {e : ℝ}
    (he : HasNaturalDensity (finiteExceptionPrimeRule S R G) e) :
    ∃ (T : Finset (Finset ℕ)) (L : (P : Finset ℕ) → Set (↥P → ℕ)) (f : ℝ),
      (∀ Q ∈ T, Q.Nonempty ∧ Q ⊆ Nat.primesLE Z ∧ Q.card ≤ d ∧ KTermVectorAPFree k (L Q)) ∧
      (T : Set (Finset ℕ)).PairwiseDisjoint id ∧
      HasNaturalDensity (finiteExceptionPrimeRule T L G) f ∧
      e ≤ f + ((S.biUnion id).card : ℝ)/(Z : ℝ) := by
  classical
  let project (P : Finset ℕ) := P.filter (· ≤ Z)
  let T := (S.image project).erase ∅
  have hSource (Q : Finset ℕ) (hQ : Q ∈ T) : ∃ P ∈ S, project P = Q :=
    mem_image.mp (mem_of_mem_erase hQ)
  choose P hP heq using hSource
  have hsub (Q : Finset ℕ) (hQ : Q ∈ T) : Q ⊆ P Q hQ := by
    intro p hp
    have h : p ∈ project (P Q hQ) := (heq Q hQ).symm ▸ hp
    exact (mem_filter.mp h).1
  let L (Q : Finset ℕ) : Set (↥Q → ℕ) :=
    if hQ : Q ∈ T then zeroSlicePrimeBlockRule (R (P Q hQ)) else Set.univ
  have hpL (Q : Finset ℕ) (hQ : Q ∈ T) :
      Q.Nonempty ∧ Q ⊆ Nat.primesLE Z ∧ Q.card ≤ d ∧ KTermVectorAPFree k (L Q) := by
    refine ⟨nonempty_iff_ne_empty.mpr (ne_of_mem_erase hQ),?_,?_,?_⟩
    · intro p hp
      have hp' : p ∈ project (P Q hQ) := (heq Q hQ).symm ▸ hp
      exact Nat.mem_primesLE.mpr ⟨(mem_filter.mp hp').2,
        hpr _ (hP Q hQ) p (hsub Q hQ hp)⟩
    · exact (card_le_card (hsub Q hQ)).trans (hWidth _ (hP Q hQ))
    · rw [show L Q = zeroSlicePrimeBlockRule (R (P Q hQ)) from dif_pos hQ]
      exact kTermVectorAPFree_zeroSlicePrimeBlockRule (hsub Q hQ) (hFree _ (hP Q hQ))
  have htPair : (T : Set (Finset ℕ)).PairwiseDisjoint id := by
    intro Q hQ U hU hne
    have hpne : P Q hQ ≠ P U hU := fun h ↦ hne ((heq Q hQ).symm.trans
      ((congrArg project h).trans (heq U hU)))
    exact disjoint_left.mpr fun p hp hpu ↦
      (disjoint_left.mp (hPair (hP Q hQ) (hP U hU) hpne)) (hsub Q hQ hp) (hsub U hU hpu)
  obtain ⟨f,hf⟩ := exists_hasNaturalDensity_finiteExceptionPrimeRule T L h0 h1
    (fun Q hQ _ hp ↦ Nat.prime_of_mem_primesLE ((hpL Q hQ).2.1 hp)) htPair
  refine ⟨T,L,f,hpL,htPair,hf,?_⟩
  let H := S.biUnion id
  let Hbig := H.filter (Z < ·)
  let bad : Set ℕ := {n | ∃ p ∈ Hbig, p ∣ n}
  have hIn {p : ℕ} (hp : p ∈ H) (hle : p ≤ Z) : p ∈ T.biUnion id := by
    obtain ⟨U,hU,hpU⟩ := mem_biUnion.mp hp
    have hproj : p ∈ project U := mem_filter.mpr ⟨hpU,hle⟩
    have hne : project U ≠ ∅ := (show (project U).Nonempty from ⟨p,hproj⟩).ne_empty
    exact mem_biUnion.mpr ⟨project U,mem_erase.mpr ⟨hne,mem_image_of_mem _ hU⟩,hproj⟩
  have hSubset : finiteExceptionPrimeRule S R G ⊆ finiteExceptionPrimeRule T L G ∪ bad := by
    intro n hn
    by_cases hbad : n ∈ bad
    · exact Or.inr hbad
    · left
      have hZero {p : ℕ} (hp : p ∈ H) (hbig : Z < p) : n.factorization p = 0 :=
        Nat.factorization_eq_zero_of_not_dvd fun hd ↦ hbad ⟨p,mem_filter.mpr ⟨hp,hbig⟩,hd⟩
      refine ⟨⟨hn.1.1,fun Q hQ ↦ ?_⟩,fun p hp hOut ↦ ?_⟩
      · rw [show L Q = zeroSlicePrimeBlockRule (R (P Q hQ)) from dif_pos hQ]
        have hRebuild :
            zeroExtendPrimeBlockPattern (P Q hQ) Q (fun q ↦ n.factorization q.val) =
                (fun p : ↥(P Q hQ) ↦ n.factorization p.val) := by
          funext p
          by_cases hp : p.val ∈ Q
          · simp [zeroExtendPrimeBlockPattern,hp]
          · have hbig : Z < p.val := lt_of_not_ge fun h ↦ by
              have he : p.val ∈ project (P Q hQ) := mem_filter.mpr ⟨p.property,h⟩
              exact hp (Eq.mp (congrArg (fun A : Finset ℕ ↦ p.val ∈ A) (heq Q hQ)) he)
            have hzero := hZero (mem_biUnion.mpr ⟨P Q hQ,hP Q hQ,p.property⟩) hbig
            simp [zeroExtendPrimeBlockPattern,hp,hzero]
        change zeroExtendPrimeBlockPattern (P Q hQ) Q (fun q ↦ n.factorization q.val) ∈ R (P Q hQ)
        rw [hRebuild]
        exact hn.1.2 _ (hP Q hQ)
      · by_cases h : p ∈ H
        · have hpZ : Z < p := lt_of_not_ge fun hle ↦ hOut (hIn h hle)
          rw [hZero h hpZ]
          exact h0
        · exact hn.2 p hp h
  have hError (N : ℕ) : densityUpTo bad N ≤ (H.card : ℝ)/(Z : ℝ) := by
    have hZr : (0 : ℝ) < Z := by exact_mod_cast hZ
    calc
      _ ≤ ∑ p ∈ Hbig, 1/(p : ℝ) :=
        densityUpTo_divisibleByOneOf_le Hbig id N (fun p hp ↦ hZ.trans (mem_filter.mp hp).2)
      _ ≤ ∑ _ ∈ Hbig, 1/(Z : ℝ) := sum_le_sum fun p hp ↦
        one_div_le_one_div_of_le hZr (by exact_mod_cast (mem_filter.mp hp).2.le)
      _ = (Hbig.card : ℝ)/(Z : ℝ) := by rw [sum_const,nsmul_eq_mul,mul_one_div]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast card_le_card (filter_subset _ H)) hZr.le
  apply le_of_tendsto_of_tendsto' he (hf.add tendsto_const_nhds)
  intro N
  exact (densityUpTo_mono hSubset N).trans
    ((densityUpTo_union_le _ bad N).trans (add_le_add le_rfl (hError N)))

end GRHArticle.ProgressionFree
