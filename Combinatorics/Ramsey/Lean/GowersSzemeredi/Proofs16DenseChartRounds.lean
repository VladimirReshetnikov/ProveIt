import GowersSzemeredi.Proofs16DenseChartAppend

/-! Both frequency-iteration rounds retain a uniform domain-density field.
The lower bound is the minimum of the two actual claim densities, so it
can be carried through arbitrary alternations of the rounds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem milicevic_prop_9_3_round_dense {N : Nat} [NeZero N] [Fact N.Prime] (Γ : ZMod N → Finset (ZMod N))
    {d : Nat} (hΓ : ∀ z, (Γ z).card ≤ d) {r : Nat} (hr : 2 * d ≤ r) (M : Nat) [NeZero M]
    {rho : Real} (hrho : 0 < rho) (hrho1 : rho < 1) (hM : 2 ≤ rho * M) {s₀ : Nat}
    (hs₀ : ∀ s, 2 ^ s ≤ (2 * s * (2 * propNineThreeRadius r M rho) + 1) ^ (2 * d) →
      s ≤ s₀)
    {η : Real} (hη0 : 0 ≤ η) (hη : 2 * (s₀ : Real) * η ≤ 1 / 4) {ε : Real} (hε : 0 < ε)
    {m : Nat} {θ : Nat → ZMod N → ZMod N} {D : Nat → Finset (ZMod N)}
    {I : ZMod N → ZMod N → Finset Nat}
    (hinv : PropNineThreeInvariant Γ (2 * propNineThreeRadius r M rho) m θ D I)
    {delta : Real} (hdelta : delta ≤ claimNineFourDensity ε (propNineThreeRadius r M rho) d)
    (hdense : ∀ i < m, delta*(N : Real) ≤ ((D i).card : Real))
    (hbad : ε * (N : Real) ^ 3 ≤ (propNineThreeBad Γ rho η θ I).card) :
    ∃ (θ' : Nat → ZMod N → ZMod N) (D' : Nat → Finset (ZMod N))
      (I' : ZMod N → ZMod N → Finset Nat),
      PropNineThreeInvariant Γ (2 * propNineThreeRadius r M rho) (m + 1) θ' D' I' ∧
      (∀ i < m+1, delta*(N : Real) ≤ ((D' i).card : Real)) ∧
      (propNineThreePotential I : Real) +
          claimNineFourDensity ε (propNineThreeRadius r M rho) d * (N : Real) ^ 2 ≤
        propNineThreePotential I' := by
  set R := propNineThreeRadius r M rho with hRdef
  set Bad := propNineThreeBad Γ rho η θ I with hBad
  have hcap := propNineThree_index_card_le Γ hΓ hs₀ hinv
  -- the decompositions on the bad triples
  have key : ∀ t : ZMod N × ZMod N × ZMod N, ∃ ξ4 : Fin 4 → ZMod N, t ∈ Bad →
      (ξ4 0 ∈ spanBall (Γ (t.1 + t.2.2)) R ∧ ξ4 1 ∈ spanBall (Γ t.1) R ∧
        ξ4 2 ∈ spanBall (Γ (t.2.1 + t.2.2)) R ∧ ξ4 3 ∈ spanBall (Γ t.2.1) R) ∧
      ξ4 0 - ξ4 1 = ξ4 2 - ξ4 3 ∧
      ξ4 0 - ξ4 1 ∉ spanBall ((I t.1 t.2.2).image fun i => θ i t.2.2) 1 := by
    intro t
    by_cases ht : t ∈ Bad
    · obtain ⟨-, dd, hdd, hnot⟩ := Finset.mem_filter.mp ht
      set W := (I t.1 t.2.2 ∪ I t.2.1 t.2.2).image fun i => θ i t.2.2 with hW
      have hWcard : (Fintype.card W : Real) * ((1 : Nat) : Real) * η ≤ 1 / 4 := by
        rw [Fintype.card_coe, Nat.cast_one, mul_one]
        have h1 : W.card ≤ 2 * s₀ := by
          refine (Finset.card_image_le).trans ((Finset.card_union_le _ _).trans ?_)
          have := hcap t.1 t.2.2
          have := hcap t.2.1 t.2.2
          omega
        have h2 : (W.card : Real) ≤ 2 * s₀ := by exact_mod_cast h1
        nlinarith
      have hWd : ∀ w : W, (centeredAbs ((w : ZMod N) * dd) : Real) ≤ η * N := by
        intro w
        obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp w.2
        rw [← hiw]
        exact hdd i hi
      have hK : (Γ (t.1 + t.2.2) ∪ Γ t.1).card ≤ r :=
        (Finset.card_union_le _ _).trans
          (by have := hΓ (t.1 + t.2.2); have := hΓ t.1; omega)
      have hL : (Γ (t.2.1 + t.2.2) ∪ Γ t.2.1).card ≤ r :=
        (Finset.card_union_le _ _).trans
          (by have := hΓ (t.2.1 + t.2.2); have := hΓ t.2.1; omega)
      obtain ⟨ξ, hξKL, hξesc⟩ := escape_frequency_uniform _ _ r M hK hL hrho hrho1 hM
        (fun w : W => (w : ZMod N)) 1 hWcard hWd hnot
      obtain ⟨hξK, hξL⟩ := Finset.mem_inter.mp hξKL
      obtain ⟨ξ₀, h₀, ξ₁, h₁, ξ₂, h₂, ξ₃, h₃, hξ, hdec⟩ :=
        escape_split Γ t.1 t.2.1 t.2.2 le_rfl le_rfl hξK hξL
      refine ⟨![ξ₀, ξ₁, ξ₂, ξ₃], fun _ => ⟨⟨h₀, h₁, h₂, h₃⟩, hdec, ?_⟩⟩
      show ξ₀ - ξ₁ ∉ _
      rw [← hξ]
      intro hmem
      apply hξesc
      refine spanBall_subset_boundedFrequencySpan ?_ 1 hmem
      exact Finset.image_subset_image Finset.subset_union_left
    · exact ⟨0, fun h => absurd h ht⟩
  choose ξ hξ using key
  obtain ⟨Θ, B, P, hF, hPcard, hP⟩ := claim_9_4 Γ hΓ Bad ξ (fun t ht => (hξ t ht).1)
    (fun t ht => (hξ t ht).2.1)
    (fun x a => spanBall ((I x a).image fun i => θ i a) 1) (fun t ht => (hξ t ht).2.2)
    hε hbad
  have hBmass : delta*(N : Real) ≤ (B.card : Real) :=
    pair_support_second_density P B (fun p hp => (hP p hp).1)
      ((mul_le_mul_of_nonneg_right hdelta (by positivity)).trans hPcard)
  obtain ⟨θ', D', I', hinv', hdense', hpot⟩ := propNineThree_append_dense hinv hdense Θ B P hF hBmass hP
  refine ⟨θ', D', I', hinv', hdense', ?_⟩
  rw [hpot]
  push_cast
  linarith

theorem milicevic_prop_9_3_round_twelve_dense {N : Nat} [NeZero N] [Fact N.Prime]
    (Γ : ZMod N → Finset (ZMod N)) {d : Nat} (hΓ : ∀ z, (Γ z).card ≤ d) {r : Nat}
    (hr : 8 * d ≤ r) (M : Nat) [NeZero M] {rho : Real} (hrho : 0 < rho) (hrho1 : rho < 1)
    (hM : 2 ≤ rho * M) {s₀ : Nat}
    (hs₀ : ∀ s, 2 ^ s ≤ (2 * s * (2 * propNineThreeRadius r M rho) + 1) ^ (2 * d) →
      s ≤ s₀)
    {η : Real} (hη0 : 0 ≤ η) (hη : 32 * (s₀ : Real) * η ≤ 1 / 4) {ε : Real} (hε : 0 < ε)
    {m : Nat} {θ : Nat → ZMod N → ZMod N} {D : Nat → Finset (ZMod N)}
    {I : ZMod N → ZMod N → Finset Nat}
    (hinv : PropNineThreeInvariant Γ (2 * propNineThreeRadius r M rho) m θ D I)
    {delta : Real} (hdelta : delta ≤ claimNineFiveDensity ε (propNineThreeRadius r M rho) d)
    (hdense : ∀ i < m, delta*(N : Real) ≤ ((D i).card : Real))
    (hbad : ε * (N : Real) ^ 11 ≤ (propNineThreeBad12 Γ rho η θ I).card) :
    ∃ (θ' : Nat → ZMod N → ZMod N) (D' : Nat → Finset (ZMod N))
      (I' : ZMod N → ZMod N → Finset Nat),
      PropNineThreeInvariant Γ (2 * propNineThreeRadius r M rho) (m + 1) θ' D' I' ∧
      (∀ i < m+1, delta*(N : Real) ≤ ((D' i).card : Real)) ∧
      (propNineThreePotential I : Real) +
          claimNineFiveDensity ε (propNineThreeRadius r M rho) d * (N : Real) ^ 2 ≤
        propNineThreePotential I' := by
  set R := propNineThreeRadius r M rho with hRdef
  set Bad := propNineThreeBad12 Γ rho η θ I with hBad
  have hcap := propNineThree_index_card_le Γ hΓ hs₀ hinv
  let V : (Fin 11 → ZMod N) → Fin 4 → Finset (ZMod N) := fun u j =>
    (I (twelveX u j) (twelveA u j)).image fun i => θ i (twelveA u j)
  have key : ∀ u : Fin 11 → ZMod N, ∃ ξ : Fin 4 → Fin 4 → ZMod N, u ∈ Bad →
      (∀ j k, ξ j k ∈ spanBall (Γ (twelvePoint u j k)) R) ∧
      ∑ j, (ξ j 0 - ξ j 1) = ∑ j, (ξ j 2 - ξ j 3) ∧
      ∃ j, ξ j 0 - ξ j 1 ∉ spanBall (V u j) 1 := by
    intro u
    by_cases hu : u ∈ Bad
    · obtain ⟨-, dd, hdd, hnot⟩ := Finset.mem_filter.mp hu
      set W := Finset.univ.biUnion fun j : Fin 4 =>
        (I (twelveX u j) (twelveA u j) ∪ I (twelveY u j) (twelveA u j)).image
          fun i => θ i (twelveA u j) with hW
      have hWcard : (Fintype.card W : Real) * ((4 : Nat) : Real) * η ≤ 1 / 4 := by
        rw [Fintype.card_coe]
        have h1 : W.card ≤ 8 * s₀ := by
          refine Finset.card_biUnion_le.trans ?_
          calc ∑ j : Fin 4, ((I (twelveX u j) (twelveA u j) ∪
                I (twelveY u j) (twelveA u j)).image fun i => θ i (twelveA u j)).card
              ≤ ∑ _j : Fin 4, 2 * s₀ := Finset.sum_le_sum fun j _ =>
                Finset.card_image_le.trans ((Finset.card_union_le _ _).trans (by
                  have := hcap (twelveX u j) (twelveA u j)
                  have := hcap (twelveY u j) (twelveA u j)
                  omega))
            _ = 8 * s₀ := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]; ring
        have h2 : (W.card : Real) ≤ 8 * s₀ := by exact_mod_cast h1
        push_cast
        nlinarith
      have hWd : ∀ w : W, (centeredAbs ((w : ZMod N) * dd) : Real) ≤ η * N := by
        intro w
        obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp w.2
        obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hj
        rw [← hiw]
        exact hdd j i hi
      obtain ⟨ξ, hξKL, hξesc⟩ := escape_frequency_uniform (twelveK Γ u) (twelveL Γ u) r M
        ((twelveK_card_le Γ hΓ u).trans hr) ((twelveL_card_le Γ hΓ u).trans hr)
        hrho hrho1 hM (fun w : W => (w : ZMod N)) 4 hWcard hWd hnot
      obtain ⟨hξK, hξL⟩ := Finset.mem_inter.mp hξKL
      obtain ⟨α, hα, hαsum⟩ := spanBall_biUnion_split _ _ R
        (boundedFrequencySpan_subset_spanBall _ R hξK)
      obtain ⟨α', hα', hα'sum⟩ := spanBall_biUnion_split _ _ R
        (boundedFrequencySpan_subset_spanBall _ R hξL)
      have hsplit : ∀ j, ∃ β₀ ∈ spanBall (Γ (twelvePoint u j 0)) R,
          ∃ β₁ ∈ spanBall (Γ (twelvePoint u j 1)) R, α j = β₀ + β₁ := fun j =>
        spanBall_union_split _ _ R (hα j (Finset.mem_univ _))
      have hsplit' : ∀ j, ∃ β₂ ∈ spanBall (Γ (twelvePoint u j 2)) R,
          ∃ β₃ ∈ spanBall (Γ (twelvePoint u j 3)) R, α' j = β₂ + β₃ := fun j =>
        spanBall_union_split _ _ R (hα' j (Finset.mem_univ _))
      choose β₀ hβ₀ β₁ hβ₁ hβ using hsplit
      choose β₂ hβ₂ β₃ hβ₃ hβ' using hsplit'
      refine ⟨fun j => ![β₀ j, -β₁ j, β₂ j, -β₃ j], fun _ => ⟨?_, ?_, ?_⟩⟩
      · intro j k
        fin_cases k
        · exact hβ₀ j
        · exact neg_mem_spanBall (hβ₁ j)
        · exact hβ₂ j
        · exact neg_mem_spanBall (hβ₃ j)
      · show ∑ j, (β₀ j - -β₁ j) = ∑ j, (β₂ j - -β₃ j)
        simp only [sub_neg_eq_add]
        rw [← Finset.sum_congr rfl fun j _ => hβ j, ← Finset.sum_congr rfl fun j _ => hβ' j,
          ← hαsum, ← hα'sum]
      · by_contra hall
        push Not at hall
        apply hξesc
        have hmem : ∑ j, α j ∈ spanBall W (Finset.univ : Finset (Fin 4)).card := by
          refine sum_mem_spanBall_of_subset Finset.univ (V u) α (fun j _ => ?_) (fun j _ => ?_)
          · intro w hw
            obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
            exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
              Finset.mem_image.mpr ⟨i, Finset.mem_union_left _ hi, rfl⟩⟩
          · have := hall j
            simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_neg_eq_add] at this
            rw [hβ j]
            exact this
        rw [Finset.card_univ, Fintype.card_fin, ← hαsum] at hmem
        exact spanBall_subset_boundedFrequencySpan le_rfl 4 hmem
    · exact ⟨fun _ _ => 0, fun h => absurd h hu⟩
  choose ξ hξ using key
  obtain ⟨Θ, B, P, hF, hPcard, hP⟩ := claim_9_5 Γ hΓ Bad ξ (fun u hu => (hξ u hu).1)
    (fun u hu => (hξ u hu).2.1)
    (fun x a => spanBall ((I x a).image fun i => θ i a) 1) (fun u hu => (hξ u hu).2.2)
    hε hbad
  have hBmass : delta*(N : Real) ≤ (B.card : Real) :=
    pair_support_second_density P B (fun p hp => (hP p hp).1)
      ((mul_le_mul_of_nonneg_right hdelta (by positivity)).trans hPcard)
  obtain ⟨θ', D', I', hinv', hdense', hpot⟩ := propNineThree_append_dense hinv hdense Θ B P hF hBmass hP
  refine ⟨θ', D', I', hinv', hdense', ?_⟩
  rw [hpot]
  push_cast
  linarith


end LeanProofs.GowersSzemeredi
