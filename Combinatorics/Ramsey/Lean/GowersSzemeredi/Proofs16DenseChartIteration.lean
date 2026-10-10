import GowersSzemeredi.Proofs16DenseChartRounds

/-! The frequency iteration retains uniform density for every actual chart.
The potential and numerical termination bound are unchanged; the extra
state field is supplied by the extraction rounds, not assumed at the end. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem milicevic_prop_9_3_iteration_dense {N : Nat} [NeZero N] [Fact N.Prime]
    (Γ : ZMod N → Finset (ZMod N)) {d : Nat} (hΓ : ∀ z, (Γ z).card ≤ d) {r : Nat}
    (hr : 8 * d ≤ r) (M : Nat) [NeZero M] {rho : Real} (hrho : 0 < rho) (hrho1 : rho < 1)
    (hM : 2 ≤ rho * M) {s₀ : Nat}
    (hs₀ : ∀ s, 2 ^ s ≤ (2 * s * (2 * propNineThreeRadius r M rho) + 1) ^ (2 * d) →
      s ≤ s₀)
    {η : Real} (hη0 : 0 ≤ η) (hη : 32 * (s₀ : Real) * η ≤ 1 / 4) {ε : Real} (hε : 0 < ε) :
    ∃ (m : Nat) (θ : Nat → ZMod N → ZMod N) (D : Nat → Finset (ZMod N))
      (I : ZMod N → ZMod N → Finset Nat),
      PropNineThreeInvariant Γ (2 * propNineThreeRadius r M rho) m θ D I ∧
      (∀ i < m, min (claimNineFourDensity ε (propNineThreeRadius r M rho) d)
        (claimNineFiveDensity ε (propNineThreeRadius r M rho) d) * (N : Real) ≤ ((D i).card : Real)) ∧
      ((propNineThreeBad Γ rho η θ I).card : Real) < ε * (N : Real) ^ 3 ∧
      ((propNineThreeBad12 Γ rho η θ I).card : Real) < ε * (N : Real) ^ 11 ∧
      ⌈min (claimNineFourDensity ε (propNineThreeRadius r M rho) d)
          (claimNineFiveDensity ε (propNineThreeRadius r M rho) d) * (N : Real) ^ 2⌉₊ * m ≤
        N * N * s₀ := by
  set R := propNineThreeRadius r M rho with hRdef
  set R' := 2 * R with hR'
  set δ := min (claimNineFourDensity ε R d) (claimNineFiveDensity ε R d) with hδ
  have hNpos : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hKpos : (0 : Real) < (((2 * R + 1) ^ d : Nat) : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (by positivity)
  have hδ4 : 0 < claimNineFourDensity ε R d := by
    simp only [claimNineFourDensity]
    positivity
  have hδ12 : 0 < claimNineFiveDensity ε R d := by
    simp only [claimNineFiveDensity]
    positivity
  have hδpos : 0 < δ := lt_min hδ4 hδ12
  have hη2 : 2 * (s₀ : Real) * η ≤ 1 / 4 := by
    have : (0 : Real) ≤ s₀ * η := mul_nonneg (Nat.cast_nonneg _) hη0
    nlinarith
  have hr2 : 2 * d ≤ r := by omega
  set k := ⌈δ * (N : Real) ^ 2⌉₊ with hk
  have hN2 : (0 : Real) < (N : Real) ^ 2 := by positivity
  have hkpos : 0 < k := Nat.ceil_pos.mpr (mul_pos hδpos hN2)
  let σ := Nat × (Nat → ZMod N → ZMod N) × (Nat → Finset (ZMod N)) ×
    (ZMod N → ZMod N → Finset Nat)
  let Inv : σ → Prop := fun s => PropNineThreeInvariant Γ R' s.1 s.2.1 s.2.2.1 s.2.2.2 ∧
    (∀ i < s.1, δ*(N : Real) ≤ ((s.2.2.1 i).card : Real)) ∧
    k * s.1 ≤ propNineThreePotential s.2.2.2
  let Good : σ → Prop := fun s =>
    ((propNineThreeBad Γ rho η s.2.1 s.2.2.2).card : Real) < ε * (N : Real) ^ 3 ∧
    ((propNineThreeBad12 Γ rho η s.2.1 s.2.2.2).card : Real) < ε * (N : Real) ^ 11
  have hcap : ∀ s, Inv s → propNineThreePotential s.2.2.2 ≤ N * N * s₀ := by
    intro s hs
    unfold propNineThreePotential
    calc ∑ p : ZMod N × ZMod N, (s.2.2.2 p.1 p.2).card ≤ ∑ _p : ZMod N × ZMod N, s₀ :=
          Finset.sum_le_sum fun p _ => propNineThree_index_card_le Γ hΓ hs₀ hs.1 p.1 p.2
      _ = N * N * s₀ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, ZMod.card, smul_eq_mul]
  -- a round raising the potential by `δN²` raises it by `k`
  have hraise : ∀ (s : σ) (I' : ZMod N → ZMod N → Finset Nat),
      (propNineThreePotential s.2.2.2 : Real) + δ * (N : Real) ^ 2 ≤ propNineThreePotential I' →
      propNineThreePotential s.2.2.2 + k ≤ propNineThreePotential I' := by
    intro s I' h
    have h3 : propNineThreePotential s.2.2.2 ≤ propNineThreePotential I' := by
      have : (propNineThreePotential s.2.2.2 : Real) ≤ propNineThreePotential I' := by
        have : 0 < δ * (N : Real) ^ 2 := mul_pos hδpos hN2
        linarith
      exact_mod_cast this
    have h4 : k ≤ propNineThreePotential I' - propNineThreePotential s.2.2.2 := by
      apply Nat.ceil_le.mpr
      rw [Nat.cast_sub h3]
      linarith
    omega
  have hstep : ∀ s, Inv s → ¬ Good s → ∃ s', Inv s' ∧
      propNineThreePotential s.2.2.2 + k ≤ propNineThreePotential s'.2.2.2 := by
    intro s hs hg
    have hnew : ∃ (θ' : Nat → ZMod N → ZMod N) (D' : Nat → Finset (ZMod N))
        (I' : ZMod N → ZMod N → Finset Nat),
        PropNineThreeInvariant Γ R' (s.1 + 1) θ' D' I' ∧
        (∀ i < s.1+1, δ*(N : Real) ≤ ((D' i).card : Real)) ∧
        (propNineThreePotential s.2.2.2 : Real) + δ * (N : Real) ^ 2 ≤
          propNineThreePotential I' := by
      by_cases h4 : ((propNineThreeBad Γ rho η s.2.1 s.2.2.2).card : Real) < ε * (N : Real) ^ 3
      · have h12 : ε * (N : Real) ^ 11 ≤ (propNineThreeBad12 Γ rho η s.2.1 s.2.2.2).card :=
          not_lt.mp fun h => hg ⟨h4, h⟩
        obtain ⟨θ', D', I', hinv', hdense', hpot⟩ := milicevic_prop_9_3_round_twelve_dense Γ hΓ hr M hrho
          hrho1 hM hs₀ hη0 hη hε hs.1 (min_le_right _ _) hs.2.1 h12
        refine ⟨θ', D', I', hinv', hdense', ?_⟩
        have : δ ≤ claimNineFiveDensity ε R d := min_le_right _ _
        nlinarith [sq_nonneg (N : Real)]
      · obtain ⟨θ', D', I', hinv', hdense', hpot⟩ := milicevic_prop_9_3_round_dense Γ hΓ hr2 M hrho
          hrho1 hM hs₀ hη0 hη2 hε hs.1 (min_le_left _ _) hs.2.1 (not_lt.mp h4)
        refine ⟨θ', D', I', hinv', hdense', ?_⟩
        have : δ ≤ claimNineFourDensity ε R d := min_le_left _ _
        nlinarith [sq_nonneg (N : Real)]
    obtain ⟨θ', D', I', hinv', hdense', hpot⟩ := hnew
    have hk' := hraise s I' hpot
    refine ⟨(s.1 + 1, θ', D', I'), ⟨hinv', hdense', ?_⟩, hk'⟩
    have := hs.2.2
    show k * (s.1 + 1) ≤ propNineThreePotential I'
    rw [Nat.mul_succ]
    omega
  have h0 : Inv (0, fun _ _ => 0, fun _ => ∅, fun _ _ => ∅) := by
    refine ⟨⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun x a => ?_⟩,
      fun i hi => absurd hi (Nat.not_lt_zero i), by simp⟩
    refine ⟨Finset.empty_subset _, fun i hi => absurd hi (Finset.notMem_empty i),
      by simp, ?_⟩
    intro A hA B hB _
    rw [Finset.image_empty, Finset.subset_empty] at hA hB
    rw [hA, hB]
  obtain ⟨s, hs, hg, -⟩ := exists_good_of_potential Inv Good
    (fun s => propNineThreePotential s.2.2.2) (N * N * s₀) k hkpos hcap hstep _ h0
  exact ⟨s.1, s.2.1, s.2.2.1, s.2.2.2, hs.1, hs.2.1, hg.1, hg.2, hs.2.2.trans (hcap s hs)⟩

end LeanProofs.GowersSzemeredi
