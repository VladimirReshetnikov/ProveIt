import GowersSzemeredi.Proofs16SpanBallSplit

/-! Tools for the iteration of Milićević's Proposition 9.3
(arXiv:2601.01682, printed pp. 65–67).

* `exists_good_of_potential`: if every non-final state of an invariant
  family has a successor whose potential is larger by at least `k > 0`, and
  potentials are capped by `M`, then a final state is reached with potential
  at least the starting one. Proposition 9.3's potential is
  `∑_{x,a} |I_{x,a}|`. It rises by `δN²` per application of Claim 9.4 and
  is capped by `s₀N²`, so at most `s₀/δ` rounds occur.
* `centeredAbs_intCast_le_natAbs`: `|n mod N|_centered ≤ |n|`.
* `spanBall_subset_boundedFrequencySpan`: for `V ⊆ W`,
  `⟨V⟩_R ⊆ boundedFrequencySpan W R`. A frequency escaping the bounded
  span of the current values over `I_{x+a,x} ∪ I_{y+a,y}` therefore
  escapes `⟨θ_i(a) : i ∈ I_{x+a,x}⟩_1`, the forbidden set of
  `claim_9_4`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- **Termination by a capped potential.** -/
theorem exists_good_of_potential {σ : Type*} (Inv Good : σ → Prop) (Φ : σ → Nat)
    (M k : Nat) (hk : 0 < k) (hcap : ∀ s, Inv s → Φ s ≤ M)
    (hstep : ∀ s, Inv s → ¬ Good s → ∃ s', Inv s' ∧ Φ s + k ≤ Φ s')
    (s₀ : σ) (h0 : Inv s₀) : ∃ s, Inv s ∧ Good s ∧ Φ s₀ ≤ Φ s := by
  suffices h : ∀ n, ∀ s, Inv s → M - Φ s ≤ n → ∃ t, Inv t ∧ Good t ∧ Φ s ≤ Φ t from
    h _ s₀ h0 le_rfl
  intro n
  induction n with
  | zero =>
    intro s hs hn
    by_cases hg : Good s
    · exact ⟨s, hs, hg, le_rfl⟩
    · obtain ⟨s', hs', hΦ⟩ := hstep s hs hg
      have := hcap s hs
      have := hcap s' hs'
      omega
  | succ n ih =>
    intro s hs hn
    by_cases hg : Good s
    · exact ⟨s, hs, hg, le_rfl⟩
    · obtain ⟨s', hs', hΦ⟩ := hstep s hs hg
      have := hcap s' hs'
      obtain ⟨t, ht, hgt, hΦt⟩ := ih s' hs' (by omega)
      exact ⟨t, ht, hgt, by omega⟩

theorem centeredAbs_intCast_le_natAbs {N : Nat} [NeZero N] (i : Int) :
    centeredAbs (i : ZMod N) ≤ i.natAbs := by
  have hnat (n : Nat) : centeredAbs (n : ZMod N) ≤ n := by
    rw [centeredAbs, ZMod.valMinAbs_natAbs_eq_min, ZMod.val_natCast]
    exact (Nat.min_le_left _ _).trans (Nat.mod_le n N)
  cases i with
  | ofNat n => simpa using hnat n
  | negSucc n =>
      have heq : ((Int.negSucc n : Int) : ZMod N) = -((n + 1 : Nat) : ZMod N) := by
        push_cast
        ring
      rw [heq, centeredAbs, ZMod.natAbs_valMinAbs_neg]
      exact hnat (n + 1)

/-- **Span balls of a subset lie in the bounded span of the whole set.** -/
theorem spanBall_subset_boundedFrequencySpan {N : Nat} [NeZero N] {V W : Finset (ZMod N)}
    (hVW : V ⊆ W) (R : Nat) :
    spanBall V R ⊆ boundedFrequencySpan (fun w : W => (w : ZMod N)) R := by
  intro ξ hξ
  obtain ⟨n, hn, rfl⟩ := (mem_spanBall_iff V R ξ).mp hξ
  let c : ZMod N → ZMod N := fun γ => if γ ∈ V then ((n γ : Int) : ZMod N) else 0
  have hc : ∀ γ, c γ ∈ centeredBall N R := by
    intro γ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp only [c]
    split_ifs with h
    · have h1 := centeredAbs_intCast_le_natAbs (N := N) (n γ)
      have h2 := hn γ h
      omega
    · simp [centeredAbs]
  refine Finset.mem_image.mpr ⟨fun w => ⟨c w, hc w⟩, by convert Finset.mem_univ _, ?_⟩
  simp only
  rw [Finset.sum_coe_sort W (fun γ => c γ * γ)]
  have hsum : ∑ γ ∈ W, c γ * γ = ∑ γ ∈ V, c γ * γ := by
    refine (Finset.sum_subset hVW fun γ _ hγ => ?_).symm
    simp only [c, if_neg hγ, zero_mul]
  rw [hsum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  simp only [c, if_pos hγ]
  rw [zsmul_eq_mul]

end LeanProofs.GowersSzemeredi
