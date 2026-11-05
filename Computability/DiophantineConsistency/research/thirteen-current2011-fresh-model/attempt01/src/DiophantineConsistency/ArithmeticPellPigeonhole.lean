import DiophantineConsistency.ArithmeticPellRecurrence
import DiophantineConsistency.ModelDifferenceRing
import Mathlib.Tactic.LinearCombination
/-! # Internal pigeonhole and Pell ordinates divisible by an arbitrary modulus

In every model of `𝗜𝚺₁`:

* `pigeonhole`: a coded sequence of length `k+1` with all values below `k`
  repeats a value. The proof is the usual relabelling induction on `k`, a `𝚷₁`
  induction, with the relabelled sequence built by `sigmaOne_skolem_seq`.
* `ordinate_dvd`: for every `N > 0` (standard or not) some Pell ordinate
  `ycoord t b` with `t > 0` is divisible by `N`. Two of the residue pairs
  `(xcoord n b mod N, ycoord n b mod N)`, `n ≤ N²`, coincide, and the exact
  identity `x_i y_j = y_{j-i} + y_i x_j` turns the coincidence into
  divisibility. Over `ℕ` this is `Pell.exists_dvd_yn`-style pigeonhole. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.ArithmeticPellPigeonhole
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ModelDifferenceRing

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Pigeonhole for coded sequences: `k+1` entries below `k` contain a repeat. -/
theorem pigeonhole (k : V) : ∀ s : V, Seq s → lh s = k + 1 → (∀ i < k + 1, znth s i < k) →
    ∃ i < k + 1, ∃ j < k + 1, i < j ∧ znth s i = znth s j := by
  induction k using ISigma1.pi1_succ_induction
  · definability
  case zero =>
    intro s _ _ hv
    exact absurd (hv 0 (by simp)) (by simp)
  case succ k ih =>
    intro s hs hl hv
    have hlast : k + 1 < k + 1 + 1 := by simp
    by_cases hA : ∃ i < k + 1, znth s i = znth s (k + 1)
    · obtain ⟨i, hi, he⟩ := hA
      exact ⟨i, lt_trans hi hlast, k + 1, hlast, hi, he⟩
    push_neg at hA
    have hR : 𝚺₁-Relation (fun i y : V =>
        (znth s i = k ∧ y = znth s (k + 1)) ∨ (znth s i ≠ k ∧ y = znth s i)) := by
      definability
    obtain ⟨t, ht, htl, htm⟩ := sigmaOne_skolem_seq hR (l := k + 1) (fun i _ => by
      by_cases h : znth s i = k
      · exact ⟨_, Or.inl ⟨h, rfl⟩⟩
      · exact ⟨_, Or.inr ⟨h, rfl⟩⟩)
    have tval : ∀ i < k + 1, (znth s i = k ∧ znth t i = znth s (k + 1)) ∨
        (znth s i ≠ k ∧ znth t i = znth s i) := by
      intro i hi
      have hmem := ht.nth_mem (show i < lh t by rw [htl]; exact hi)
      rw [ht.znth_eq_of_mem hmem]
      exact htm i _ hmem
    have hbound : ∀ i < k + 1, znth t i < k := by
      intro i hi
      rcases tval i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2]
        have hL : znth s (k + 1) ≤ k := le_iff_lt_succ.mpr (hv (k + 1) hlast)
        exact lt_of_le_of_ne hL (fun h => hA i hi (h1.trans h.symm))
      · rw [h2]
        exact lt_of_le_of_ne (le_iff_lt_succ.mpr (hv i (lt_trans hi hlast))) h1
    obtain ⟨i, hi, j, hj, hij, he⟩ := ih t ht htl hbound
    refine ⟨i, lt_trans hi hlast, j, lt_trans hj hlast, hij, ?_⟩
    rcases tval i hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;>
      rcases tval j hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
    · exact hi1.trans hj1.symm
    · exact absurd (hj2.symm.trans (he.symm.trans hi2)) (hA j hj)
    · exact absurd (hi2.symm.trans (he.trans hj2)) (hA i hi)
    · exact hi2.symm.trans (he.trans hj2)

/-- Base-`N` digit pairs are determined by their value. -/
theorem digit_pair_inj {N a b a' b' : V} (hN : 0 < N) (ha : a < N) (ha' : a' < N)
    (h : a + N * b = a' + N * b') : a = a' ∧ b = b' := by
  have hmod : (a + N * b) % N = a := by rw [mod_add_mul' a b hN, mod_eq_self_of_lt ha]
  have hmod' : (a' + N * b') % N = a' := by rw [mod_add_mul' a' b' hN, mod_eq_self_of_lt ha']
  have haa : a = a' := by rw [← hmod, ← hmod', h]
  subst haa
  exact ⟨rfl, (mul_left_cancel₀ hN.ne' (add_left_cancel h))⟩

/-- The residue code of the `n`-th Pell pair. -/
def code (N b n : V) : V := xcoord n b % N + N * (ycoord n b % N)

theorem code_lt {N b : V} (hN : 0 < N) (n : V) : code N b n < N * N := by
  have hx : xcoord n b % N < N := mod_lt _ hN
  have hy : ycoord n b % N < N := mod_lt _ hN
  have hy' : ycoord n b % N + 1 ≤ N := lt_iff_succ_le.mp hy
  calc code N b n < N + N * (ycoord n b % N) := by unfold code; simpa using hx
    _ = N * (ycoord n b % N + 1) := by ring
    _ ≤ N * N := mul_le_mul_left' hy' N

/-- The exact subtraction identity for Pell pairs, without natural subtraction. -/
theorem cross_identity (b i t : V) :
    xcoord i b * ycoord (i + t) b = ycoord t b + ycoord i b * xcoord (i + t) b := by
  obtain ⟨hx, hy⟩ := addition i t b
  have hn := norm i b
  rw [hx, hy]
  calc xcoord i b * (xcoord i b * ycoord t b + ycoord i b * xcoord t b)
      = (xcoord i b * xcoord i b) * ycoord t b + xcoord i b * ycoord i b * xcoord t b := by ring
    _ = (1 + delta b * ycoord i b * ycoord i b) * ycoord t b +
        xcoord i b * ycoord i b * xcoord t b := by rw [hn]
    _ = ycoord t b + ycoord i b * (xcoord i b * xcoord t b +
        delta b * ycoord i b * ycoord t b) := by ring

/-- Equal residues modulo `N` differ by a multiple of `N` in the ring of differences. -/
theorem sub_eq_mul_of_mod_eq {N a a' : V} (h : a % N = a' % N) :
    ∃ u : DiffRing V, ι a - ι a' = ι N * u := by
  refine ⟨ι (a / N) - ι (a' / N), ?_⟩
  have e1 := congrArg (ι : V →+* DiffRing V) (div_add_mod a N)
  have e2 := congrArg (ι : V →+* DiffRing V) (div_add_mod a' N)
  simp only [map_add, map_mul] at e1 e2
  rw [h] at e1
  linear_combination e2 - e1

/-- **Every modulus divides some positive-index Pell ordinate.** -/
theorem ordinate_dvd (b N : V) (hN : 0 < N) : ∃ t, 0 < t ∧ N ∣ ycoord t b := by
  have hR : 𝚺₁-Relation (fun n y : V => y = code N b n) := by
    unfold code; definability
  obtain ⟨s, hs, hsl, hsm⟩ := sigmaOne_skolem_seq hR (l := N * N + 1) (fun n _ => ⟨_, rfl⟩)
  have sval : ∀ n < N * N + 1, znth s n = code N b n := by
    intro n hn
    have hmem := hs.nth_mem (show n < lh s by rw [hsl]; exact hn)
    rw [hs.znth_eq_of_mem hmem]
    exact hsm n _ hmem
  obtain ⟨i, hi, j, hj, hij, he⟩ := pigeonhole (N * N) s hs hsl (fun n hn => by
    rw [sval n hn]; exact code_lt hN n)
  rw [sval i hi, sval j hj] at he
  obtain ⟨hxm, hym⟩ := digit_pair_inj hN (mod_lt _ hN) (mod_lt _ hN) he
  obtain ⟨t, rfl⟩ := exists_add_of_le hij.le
  have ht : 0 < t := by
    rcases (eq_zero_or_pos t) with h0 | h0
    · subst h0; simp at hij
    · exact h0
  refine ⟨t, ht, ?_⟩
  obtain ⟨u, hu⟩ := sub_eq_mul_of_mod_eq hxm
  obtain ⟨w, hw⟩ := sub_eq_mul_of_mod_eq hym
  have hc := congrArg (ι : V →+* DiffRing V) (cross_identity b i t)
  simp only [map_add, map_mul] at hc
  have hyt : ι (ycoord t b) = ι N * (u * ι (ycoord (i + t) b) - w * ι (xcoord (i + t) b)) := by
    linear_combination -hc + ι (ycoord (i + t) b) * hu - ι (xcoord (i + t) b) * hw
  have hz : 0 ≤ u * ι (ycoord (i + t) b) - w * ι (xcoord (i + t) b) := by
    have hNpos : (0 : DiffRing V) < ι N := by rw [← map_zero ι]; exact ι_lt_ι.mpr hN
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_pos_of_neg hNpos hneg
    rw [← hyt] at this
    exact absurd (ι_nonneg _) (not_le.mpr this)
  obtain ⟨z, hz'⟩ := nonneg_iff.mp hz
  refine ⟨z, ι_injective ?_⟩
  rw [map_mul, ← hz', hyt]

end DiophantineConsistency.ArithmeticPellPigeonhole
