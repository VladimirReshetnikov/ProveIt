import OAI.Combinatorics.Progressions.Lattices.IntegerIntervalOverlap
import OAI.Combinatorics.Progressions.Linear.NativeRankPairs

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem native_interval_weight_pairs {I : Type} [Fintype I] [Nonempty I]
    {s r d N : ℕ} [NeZero N] {p b : ℝ}
    (W : NativeDegreeRankFamily s r (ZMod N) b) (out : Fin W.outputDim)
    (a k : ZMod N) (δ : ℤ) (h : I → ZMod N) (c len : I → ℕ)
    (weight : ℤ → ℂ) (v : I → ℤ → ℂ)
    (E : ∀ i, NativeIntegerExpansion (fun _ : Unit => 1) d p (fun x => v i (x ())))
    (hp : 2 ≤ p) (hw : ∀ n, ‖weight n‖ ≤ 1)
    (hN : ∀ i, c i + len i ≤ N) (hshort : ∀ i, 2 * ((len i : ℤ) - 1) < N)
    (hsize : ∀ i, Real.exp (-p) ≤ (len i : ℝ) / N)
    (hcorr : ∀ i, Real.exp (-p) ≤ ‖𝔼 n ∈ Finset.Ico (c i : ℤ) (c i + len i),
      fourPointProduct (W.eval out (h i)) (W.eval out (h i - a))
        (W.eval out k) (W.eval out (k - a)) δ n * weight n * v i n‖) :
    ∃ Q : Finset (I × I), Q.Nonempty ∧
      Real.exp (-(8 * p + 1)) * (Fintype.card I : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
      ∀ t ∈ Q, ∃ c' len' : ℕ, 0 < len' ∧ c' + len' ≤ N ∧
        2 * ((len' : ℤ) - 1) < N ∧ Real.exp (-(8 * p + 1)) ≤ (len' : ℝ) / N ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) d (mixedErrorPairBudget p)
          (fun x => v t.1 (x ()) * star (v t.2 (x ())))) ∧
        Real.exp (-(8 * p + 1)) ≤ ‖𝔼 n ∈ Finset.Ico (c' : ℤ) (c' + len'),
          fourPointProduct (W.eval out (h t.1)) (W.eval out (h t.1 - a))
            (W.eval out (h t.2)) (W.eval out (h t.2 - a)) δ n * (v t.1 n * star (v t.2 n))‖ := by
  let A := Finset.Ico (0 : ℤ) N
  let S (i : I) := Finset.Ico (c i : ℤ) (c i + len i)
  let B (n : ℤ) := weight n * star (W.shiftPair out a k δ n)
  have hA : A.Nonempty := by
    exact ⟨0, Finset.mem_Ico.mpr ⟨le_rfl, by exact_mod_cast NeZero.pos N⟩⟩
  have hAcard : A.card = N := by simpa only [A, Nat.cast_zero, zero_add] using integerIco_card 0 N
  have hB (n : ℤ) (_ : n ∈ A) : ‖B n‖ ≤ 1 := by
    dsimp only [B]
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw n)).trans (W.shiftPair_norm out a k δ n)
  have hcor (i : I) : Real.exp (-p) ≤ ‖𝔼 n ∈ S i, B n * (W.shiftPair out a (h i) δ n * v i n)‖ := by
    simpa only [S, B, W.quadruple_common_anchor] using hcorr i
  have hvol (i : I) : Real.exp (-p) ≤ (S i).card / (A.card : ℝ) := by
    simpa only [S, integerIco_card, hAcard] using hsize i
  obtain ⟨Q, hQ, hQsize, hpairs⟩ := native_weight_pair_removal hp A hA S
    (fun i => integerIco_subset_range (c i) (len i) N (hN i)) B
    (fun i => W.shiftPair out a (h i) δ) v E hB
    (fun i n _ => W.shiftPair_norm out a (h i) δ n) hvol hcor
  refine ⟨Q, hQ, hQsize, ?_⟩
  intro t ht
  obtain ⟨hJ, hJvol, hE, hJcor⟩ := hpairs t ht
  obtain ⟨c', len', hlen', hN', hle, _, heq⟩ := integerIco_intersection
    (c t.1) (len t.1) (c t.2) (len t.2) N (hN t.1) (hN t.2) hJ
  refine ⟨c', len', hlen', hN', ?_, ?_, hE, ?_⟩
  · have hs := hshort t.1
    omega
  · simpa only [S, heq, integerIco_card, hAcard] using hJvol
  · simpa only [S, heq, W.shiftPair_mul_star] using hJcor

end Erdos3

end

end OAI
