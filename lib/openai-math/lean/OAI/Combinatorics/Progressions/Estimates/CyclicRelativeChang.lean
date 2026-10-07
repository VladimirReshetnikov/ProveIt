-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Combinatorics.Additive.Randomisation
import OAI.Combinatorics.Progressions.Fourier.RelativeSpectrumDimension
import OAI.Combinatorics.Progressions.Fourier.TranslatedBohrDifference
import OAI.Compat.BigOperators

namespace OAI

section

noncomputable section

open Finset Real
open scoped BigOperators ComplexConjugate

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

def AddDissociatedMod (S Delta : Finset (AddChar G ℂ)) : Prop :=
  ∀ t u : Finset (AddChar G ℂ), t ⊆ Delta → u ⊆ Delta →
    Disjoint t u → (t ∪ u).Nonempty →
      (∑ psi ∈ t, psi) - ∑ psi ∈ u, psi ∉ S

omit [Fintype G] in
theorem addDissociatedMod_empty (S : Finset (AddChar G ℂ)) :
    AddDissociatedMod S ∅ := by
  intro t u ht hu htu hne
  simp only [Finset.subset_empty] at ht hu
  subst t
  subst u
  simp at hne

omit [Fintype G] in
theorem AddDissociatedMod.mono {S : Finset (AddChar G ℂ)}
    {Delta Gamma : Finset (AddChar G ℂ)}
    (h : AddDissociatedMod S Delta) (hsub : Gamma ⊆ Delta) :
    AddDissociatedMod S Gamma := by
  intro t u ht hu
  exact h t u (ht.trans hsub) (hu.trans hsub)

omit [Fintype G] in

theorem exists_maximal_addDissociatedMod [Finite G]
    (S T : Finset (AddChar G ℂ))
    (hzero : 0 ∈ S)
    (hS : ∀ s, s ∈ S → -s ∈ S) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ T ∧ AddDissociatedMod S Delta ∧
        ∀ psi ∈ T, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s := by
  let := Fintype.ofFinite G
  classical
  let candidates := T.powerset.filter (AddDissociatedMod S)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, addDissociatedMod_empty]
  obtain ⟨Delta, hDelta_mem, hDelta_max⟩ := candidates.exists_maximal hcandidates
  have hDelta := Finset.mem_filter.mp hDelta_mem
  refine ⟨Delta, Finset.mem_powerset.mp hDelta.1, hDelta.2, ?_⟩
  intro psi hpsiT
  by_cases hpsiDelta : psi ∈ Delta
  · exact ⟨psi, Finset.subset_addSpan hpsiDelta, 0, hzero, by simp⟩
  · have hinsert_subset : insert psi Delta ⊆ T :=
      Finset.insert_subset hpsiT (Finset.mem_powerset.mp hDelta.1)
    have hnot : ¬ AddDissociatedMod S (insert psi Delta) := by
      intro hins
      have hinsert_mem : insert psi Delta ∈ candidates := by
        simp [candidates, hinsert_subset, hins]
      have hsub := hDelta_max hinsert_mem (Finset.subset_insert psi Delta)
      exact hpsiDelta (hsub (Finset.mem_insert_self psi Delta))
    rw [AddDissociatedMod] at hnot
    push Not at hnot
    obtain ⟨t, u, ht, hu, htu, hne, hsumS⟩ := hnot
    have hpsi_tu : psi ∈ t ∪ u := by
      by_contra hpsi
      have htDelta : t ⊆ Delta := by
        intro a ha
        have ha' := ht ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi (h ▸ Finset.mem_union_left u ha))
      have huDelta : u ⊆ Delta := by
        intro a ha
        have ha' := hu ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi (h ▸ Finset.mem_union_right t ha))
      exact hDelta.2 t u htDelta huDelta htu hne hsumS
    rw [Finset.mem_union] at hpsi_tu
    rcases hpsi_tu with hpsi_t | hpsi_u
    · have hpsi_not_u : psi ∉ u := fun h ↦ Finset.disjoint_left.mp htu hpsi_t h
      have htErase : t.erase psi ⊆ Delta := by
        intro a ha
        have ha' := ht (Finset.mem_of_mem_erase ha)
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (Finset.ne_of_mem_erase ha)
      have huDelta : u ⊆ Delta := by
        intro a ha
        have ha' := hu ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi_not_u (h ▸ ha))
      let z := (∑ a ∈ u, a) - ∑ a ∈ t.erase psi, a
      have hz : z ∈ Delta.addSpan := by
        exact Finset.sum_sub_sum_mem_addSpan huDelta htErase
      refine ⟨z, hz, (∑ a ∈ t, a) - ∑ a ∈ u, a, hsumS, ?_⟩
      dsimp [z]
      rw [← Finset.sum_erase_add _ _ hpsi_t]
      abel
    · have hpsi_not_t : psi ∉ t := fun h ↦ Finset.disjoint_left.mp htu h hpsi_u
      have huErase : u.erase psi ⊆ Delta := by
        intro a ha
        have ha' := hu (Finset.mem_of_mem_erase ha)
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (Finset.ne_of_mem_erase ha)
      have htDelta : t ⊆ Delta := by
        intro a ha
        have ha' := ht ha
        rw [Finset.mem_insert] at ha'
        exact ha'.resolve_left (fun h ↦ hpsi_not_t (h ▸ ha))
      let z := (∑ a ∈ t, a) - ∑ a ∈ u.erase psi, a
      have hz : z ∈ Delta.addSpan := by
        exact Finset.sum_sub_sum_mem_addSpan htDelta huErase
      let s := -((∑ a ∈ t, a) - ∑ a ∈ u, a)
      have hs : s ∈ S := hS _ hsumS
      refine ⟨z, hz, s, hs, ?_⟩
      dsimp [z, s]
      rw [← Finset.sum_erase_add _ _ hpsi_u]
      abel

omit [Fintype G] in

theorem exists_maximal_addDissociatedMod_card_le [Finite G]
    (S T : Finset (AddChar G ℂ)) (hzero : 0 ∈ S)
    (hS : ∀ s, s ∈ S → -s ∈ S) (D : ℝ) (k : ℕ)
    (hDk : D < k)
    (hdim : ∀ Gamma : Finset (AddChar G ℂ), Gamma ⊆ T →
      AddDissociatedMod S Gamma → Gamma.card ≤ k →
        (Gamma.card : ℝ) ≤ D) :
    ∃ Delta : Finset (AddChar G ℂ),
      Delta ⊆ T ∧ AddDissociatedMod S Delta ∧
        (Delta.card : ℝ) ≤ D ∧
        ∀ psi ∈ T, ∃ z ∈ Delta.addSpan, ∃ s ∈ S, psi = z + s := by
  let := Fintype.ofFinite G
  obtain ⟨Delta, hDeltaT, hDelta, hcover⟩ :=
    exists_maximal_addDissociatedMod S T hzero hS
  have hcard : Delta.card ≤ k := by
    by_contra hnot
    have hkDelta : k ≤ Delta.card := Nat.le_of_lt (Nat.lt_of_not_ge hnot)
    obtain ⟨Gamma, hGammaDelta, hGammaCard⟩ :=
      Finset.exists_subset_card_eq hkDelta
    have hGammaReal : (Gamma.card : ℝ) ≤ D :=
      hdim Gamma (hGammaDelta.trans hDeltaT) (hDelta.mono hGammaDelta)
        (by omega)
    have hkD : (k : ℝ) ≤ D := by simpa [hGammaCard] using hGammaReal
    exact (not_le_of_gt hDk) hkD
  exact ⟨Delta, hDeltaT, hDelta, hdim Delta hDeltaT hDelta hcard, hcover⟩

private def signedFrequency (t u : Finset (AddChar G ℂ)) : AddChar G ℂ :=
  (∑ psi ∈ u, psi) - ∑ psi ∈ t \ u, psi

private def signedCoefficient (v : AddChar G ℂ → ℂ)
    (t u : Finset (AddChar G ℂ)) : ℂ :=
  ((∏ psi ∈ u, v psi) * ∏ psi ∈ t \ u, conj (v psi)) /
    (2 : ℂ) ^ t.card

omit [Fintype G] in
private lemma rieszProduct_eq_signedExpansion [Finite G]
    (Delta : Finset (AddChar G ℂ)) (v : AddChar G ℂ → ℂ) (x : G) :
    ∏ psi ∈ Delta, ((1 + (v psi * psi x).re : ℝ) : ℂ) =
      ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u * signedFrequency t u x := by
  let := Fintype.ofFinite G
  calc
    ∏ psi ∈ Delta, ((1 + (v psi * psi x).re : ℝ) : ℂ) =
        ∏ psi ∈ Delta,
          (((v psi * psi x) + conj (v psi * psi x)) / 2 + 1) := by
      apply Finset.prod_congr rfl
      intro psi hpsi
      rw [add_comm, ← Complex.re_eq_add_conj]
      push_cast
      rfl
    _ = ∑ t ∈ Delta.powerset,
        ∏ psi ∈ t, ((v psi * psi x) + conj (v psi * psi x)) / 2 := by
      rw [Finset.prod_add]
      simp
    _ = ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u * signedFrequency t u x := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.prod_div_distrib]
      rw [Finset.prod_add]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u hu
      rw [signedCoefficient, signedFrequency]
      simp only [AddChar.sum_apply, AddChar.sub_apply,
        AddChar.map_neg_eq_conj]
      simp only [Finset.prod_const]
      simp_rw [map_mul, Finset.prod_mul_distrib]
      rw [map_prod]
      ring

private lemma weightedRiesz_eq_signedExpansion
    (w : G → ℝ) (Delta : Finset (AddChar G ℂ))
    (v : AddChar G ℂ → ℂ) :
    ((∑ x : G, w x *
        ∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) =
      ∑ t ∈ Delta.powerset, ∑ u ∈ t.powerset,
        signedCoefficient v t u *
          Erdos3.massCoeff w (signedFrequency t u) := by
  simp_rw [Complex.ofReal_prod]
  simp_rw [rieszProduct_eq_signedExpansion]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Erdos3.massCoeff, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

omit [Fintype G] in
private lemma signedFrequency_not_mem
    {S Delta t u : Finset (AddChar G ℂ)}
    (hDelta : AddDissociatedMod S Delta)
    (ht : t ⊆ Delta) (ht0 : t.Nonempty) (hu : u ⊆ t) :
    signedFrequency t u ∉ S := by
  apply hDelta u (t \ u)
  · exact hu.trans ht
  · exact Finset.sdiff_subset.trans ht
  · rw [Finset.disjoint_left]
    intro psi hpsiu hpsitu
    exact (Finset.mem_sdiff.mp hpsitu).2 hpsiu
  · simpa [Finset.union_sdiff_of_subset hu] using ht0

omit [Fintype G] in
private lemma norm_signedCoefficient_le
    {v : AddChar G ℂ → ℂ} {t u : Finset (AddChar G ℂ)}
    (hu : u ⊆ t) (hv : ∀ psi ∈ t, ‖v psi‖ ≤ 1) :
    ‖signedCoefficient v t u‖ ≤ ((2 : ℝ) ^ t.card)⁻¹ := by
  have hvu : ‖∏ psi ∈ u, v psi‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun psi hpsi ↦ norm_nonneg _)
      (fun psi hpsi ↦ hv psi (hu hpsi))
  have hvtu : ‖∏ psi ∈ t \ u, conj (v psi)‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun psi hpsi ↦ norm_nonneg _)
      (fun psi hpsi ↦ by
        rw [RCLike.norm_conj]
        exact hv psi (Finset.sdiff_subset hpsi))
  have hnum :
      ‖(∏ psi ∈ u, v psi) * ∏ psi ∈ t \ u, conj (v psi)‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul hvu hvtu (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  rw [signedCoefficient, norm_div]
  calc
    _ ≤ 1 / ‖(2 : ℂ) ^ t.card‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ = ((2 : ℝ) ^ t.card)⁻¹ := by
      rw [norm_pow]
      norm_num

theorem AddDissociatedMod.weighted_riesz_randomisation_le
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ}
    (hDelta : AddDissociatedMod S Delta)
    (_hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos3.massCoeff w psi‖ ≤ q)
    (v : AddChar G ℂ → ℂ) (hv : ∀ psi ∈ Delta, ‖v psi‖ ≤ 1) :
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re) ≤
      1 + q * (2 : ℝ) ^ Delta.card := by
  classical
  let F : Finset (AddChar G ℂ) → ℂ := fun t ↦
    ∑ u ∈ t.powerset, signedCoefficient v t u *
      Erdos3.massCoeff w (signedFrequency t u)
  let E : ℂ := ∑ t ∈ Delta.powerset.erase ∅, F t
  have hempty : (∅ : Finset (AddChar G ℂ)) ∈ Delta.powerset := by simp
  have hw1c : ∑ x : G, (w x : ℂ) = 1 := by exact_mod_cast hw1
  have hFempty : F ∅ = 1 := by
    simp [F, signedCoefficient, signedFrequency, Erdos3.massCoeff, hw1c]
  have hexp :
      ((∑ x : G, w x *
          ∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) = 1 + E := by
    rw [weightedRiesz_eq_signedExpansion]
    rw [← Finset.sum_erase_add _ _ hempty]
    simp only [hFempty, E, F]
    ring
  have hinner (t : Finset (AddChar G ℂ))
      (ht : t ∈ Delta.powerset.erase ∅) : ‖F t‖ ≤ q := by
    have htDelta : t ⊆ Delta := Finset.mem_powerset.mp (Finset.mem_of_mem_erase ht)
    have ht0 : t.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase ht)
    calc
      ‖F t‖ ≤ ∑ u ∈ t.powerset,
          ‖signedCoefficient v t u *
            Erdos3.massCoeff w (signedFrequency t u)‖ := by
        exact norm_sum_le _ _
      _ ≤ ∑ _u ∈ t.powerset, ((2 : ℝ) ^ t.card)⁻¹ * q := by
        apply Finset.sum_le_sum
        intro u hu
        rw [norm_mul]
        apply mul_le_mul
        · exact norm_signedCoefficient_le (Finset.mem_powerset.mp hu)
            (fun psi hpsi ↦ hv psi (htDelta hpsi))
        · exact hq _ (signedFrequency_not_mem hDelta htDelta ht0
            (Finset.mem_powerset.mp hu))
        · exact norm_nonneg _
        · exact inv_nonneg.mpr (pow_nonneg (by norm_num) _)
      _ = q := by
        rw [Finset.sum_const, Finset.card_powerset]
        simp [nsmul_eq_mul]
  have hEnorm : ‖E‖ ≤ q * (2 : ℝ) ^ Delta.card := by
    calc
      ‖E‖ ≤ ∑ t ∈ Delta.powerset.erase ∅, ‖F t‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ Delta.powerset.erase ∅, q := by
        exact Finset.sum_le_sum fun t ht ↦ hinner t ht
      _ ≤ ∑ _t ∈ Delta.powerset, q := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ ↦ hq0)
      _ = q * (2 : ℝ) ^ Delta.card := by
        simp [Finset.card_powerset]
        ring
  let R : ℝ :=
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re)
  have hexpR : (R : ℂ) = 1 + E := by
    calc
      (R : ℂ) = ∑ x : G, (w x : ℂ) *
          (↑(∏ psi ∈ Delta, (1 + (v psi * psi x).re)) : ℂ) := by
        dsimp [R]
        push_cast
        rfl
      _ = 1 + E := hexp
  have hre : R = 1 + E.re := by
    have := congrArg Complex.re hexpR
    simpa using this
  change R ≤ 1 + q * (2 : ℝ) ^ Delta.card
  calc
    R = 1 + E.re := hre
    _ ≤ 1 + ‖E‖ := add_le_add (le_refl 1) (Complex.re_le_norm E)
    _ ≤ 1 + q * (2 : ℝ) ^ Delta.card := add_le_add (le_refl 1) hEnorm

theorem AddDissociatedMod.isWeightedDissociated
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ} {k : ℕ}
    (hDelta : AddDissociatedMod S Delta)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos3.massCoeff w psi‖ ≤ q)
    (hcard : Delta.card ≤ k) (hqk : q * (2 : ℝ) ^ k ≤ 1) :
    IsWeightedDissociated w 1 Delta := by
  intro v hv
  have hpowNat : 2 ^ Delta.card ≤ 2 ^ k :=
    Nat.pow_le_pow_right (by norm_num) hcard
  have hpow : (2 : ℝ) ^ Delta.card ≤ (2 : ℝ) ^ k := by
    exact_mod_cast hpowNat
  have htail : q * (2 : ℝ) ^ Delta.card ≤ 1 :=
    (mul_le_mul_of_nonneg_left hpow hq0).trans hqk
  calc
    ∑ x : G, w x * ∏ psi ∈ Delta, (1 + (v psi * psi x).re) ≤
        1 + q * (2 : ℝ) ^ Delta.card :=
      hDelta.weighted_riesz_randomisation_le hw0 hw1 hq0 hq v hv
    _ ≤ 2 := by linarith
    _ ≤ exp 1 := Real.exp_one_gt_two.le

theorem AddDissociatedMod.isWeightedDissociated_of_le_quarter_pow
    {S Delta : Finset (AddChar G ℂ)} {w : G → ℝ} {q : ℝ} {k : ℕ}
    (hDelta : AddDissociatedMod S Delta)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∑ x : G, w x = 1)
    (hq0 : 0 ≤ q)
    (hq : ∀ psi, psi ∉ S → ‖Erdos3.massCoeff w psi‖ ≤ q)
    (hcard : Delta.card ≤ k) (hq_quarter : q ≤ (1 / 4 : ℝ) ^ k) :
    IsWeightedDissociated w 1 Delta := by
  apply hDelta.isWeightedDissociated hw0 hw1 hq0 hq hcard
  calc
    q * (2 : ℝ) ^ k ≤ (1 / 4 : ℝ) ^ k * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hq_quarter (pow_nonneg (by norm_num) _)
    _ = (1 / 2 : ℝ) ^ k := by rw [← mul_pow]; congr 1; norm_num
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

theorem zero_mem_chang_largeSpectrum_half (A : Finset G) :
    (0 : AddChar G ℂ) ∈ Erdos3.Chang.largeSpectrum A (1 / 2 : ℝ) := by
  rw [Erdos3.Chang.mem_largeSpectrum]
  simp [Erdos3.Chang.spectrumSum]
  have hcard : (0 : ℝ) ≤ A.card := by exact_mod_cast Nat.zero_le A.card
  nlinarith

theorem neg_mem_chang_largeSpectrum {A : Finset G} {eta : ℝ}
    {psi : AddChar G ℂ}
    (hpsi : psi ∈ Erdos3.Chang.largeSpectrum A eta) :
    -psi ∈ Erdos3.Chang.largeSpectrum A eta := by
  rw [Erdos3.Chang.mem_largeSpectrum] at hpsi ⊢
  have hsum : Erdos3.Chang.spectrumSum A (-psi) =
      conj (Erdos3.Chang.spectrumSum A psi) := by
    unfold Erdos3.Chang.spectrumSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [AddChar.neg_apply, AddChar.map_neg_eq_conj]
  rw [hsum, RCLike.norm_conj]
  exact hpsi

end Erdos3.RelativeChangSanders

end

end

section

open Finset Real
open scoped BigOperators NNReal

namespace Erdos3.RelativeChangSanders

noncomputable section

variable {N : ℕ} [NeZero N]

def localChangDimension (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) : ℝ :=
  2 * (1 + log (2 * (B.carrier.card : ℝ) / X.card)) / eta ^ 2

def localChangCap (B : CyclicBohr.Set N) (X : Finset (ZMod N)) (eta : ℝ) : ℕ :=
  ⌈localChangDimension B X eta⌉₊ + 1

def localChangBaseScale (B : CyclicBohr.Set N) (X : Finset (ZMod N))
    (eta : ℝ) : NNReal :=
  (100 * ((2 * max B.rank 1 : ℕ) : NNReal) *
    (((2 * localChangCap B X eta + 1 : ℕ) : NNReal)))⁻¹

theorem exists_relativeLargeSpectrum_cover
    (B : CyclicBohr.Set N) (hBpos : 0 < B.radius) (hBreg : B.IsRankRegular)
    (X : Finset (ZMod N)) (hX : X.Nonempty) (hXB : X ⊆ B.carrier)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ rho : NNReal, ∃ C : CyclicBohr.Set N,
      ∃ Delta : Finset (AddChar (ZMod N) ℂ),
        1 / 2 ≤ rho ∧ rho ≤ 1 ∧
        C = B.ndilate (rho * localChangBaseScale B X eta) ∧
        C.IsRankRegular ∧
        (Delta.card : ℝ) ≤ localChangDimension B X eta ∧
        Delta ⊆ Chang.largeSpectrum X eta ∧
        ∀ psi ∈ Chang.largeSpectrum X eta,
          ∃ z ∈ Delta.addSpan,
            ∃ s ∈ Chang.largeSpectrum C.carrier (1 / 2), psi = z + s := by
  classical
  let D : ℝ := localChangDimension B X eta
  let k : ℕ := localChangCap B X eta
  let d : ℕ := 2 * max B.rank 1
  let a : NNReal := localChangBaseScale B X eta
  have haPos : 0 < a := by
    dsimp [a, localChangBaseScale]
    positivity
  have haposR : (0 : ℝ) < a := by exact_mod_cast haPos
  have hbasePos : 0 < (B.ndilate a).radius := by
    rw [CyclicBohr.Set.radius_ndilate]
    exact mul_pos haposR hBpos
  obtain ⟨rho, hrhoHalf, hrhoOne, hregular⟩ :=
    CyclicBohr.Set.exists_rankRegular_ndilate (B.ndilate a) hbasePos
  let tau : NNReal := rho * a
  let C : CyclicBohr.Set N := B.ndilate tau
  have hCreg : C.IsRankRegular := by
    simpa [C, tau] using hregular
  have hd : 0 < d := by simp [d]
  have hk : 0 < k := by simp [k, localChangCap]
  have ha : a =
      (100 * (d : NNReal) * (((2 * k + 1 : ℕ) : NNReal)))⁻¹ := by
    simp [a, localChangBaseScale, d, k]
  have hsmall : (((2 * k : ℕ) : NNReal) * tau) ≤
      1 / (100 * (d : NNReal)) := by
    have hkden : (0 : NNReal) < (((2 * k + 1 : ℕ) : NNReal)) := by positivity
    have hdb : (0 : NNReal) < 100 * (d : NNReal) := by positivity
    calc
      (((2 * k : ℕ) : NNReal) * tau) =
          ((2 * k : ℕ) : NNReal) * (rho * a) := rfl
      _ ≤ ((2 * k : ℕ) : NNReal) * (1 * a) := by gcongr
      _ = (((2 * k : ℕ) : NNReal) /
          (((2 * k + 1 : ℕ) : NNReal))) /
            (100 * (d : NNReal)) := by rw [ha]; field_simp
      _ ≤ 1 / (100 * (d : NNReal)) := by
        gcongr
        exact (div_le_one hkden).2 (by
          exact_mod_cast Nat.le_add_right (2 * k) 1)
  let T : Finset (AddChar (ZMod N) ℂ) := Chang.largeSpectrum X eta
  let S : Finset (AddChar (ZMod N) ℂ) :=
    Chang.largeSpectrum C.carrier (1 / 2)
  let w : (ZMod N) → ℝ := Erdos3.bohrSmoothingMeasure B tau (2 * k)
  let outer : Finset (ZMod N) :=
    (B.ndilate (1 + (((2 * k : ℕ) : NNReal) * tau))).carrier
  let c : ℝ := (outer.card : ℝ)⁻¹
  let R : ℝ := 2 * (B.carrier.card : ℝ) / X.card
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    exact Erdos3.bohrSmoothingMeasure_nonneg B tau (2 * k) x
  have hw1 : ∑ x : (ZMod N), w x = 1 := by
    exact Erdos3.sum_bohrSmoothingMeasure B tau (2 * k)
  have hwconst : ∀ x ∈ B.carrier, w x = c := by
    intro x hx
    simpa [w, c, outer] using
      (Erdos3.bohrSmoothingMeasure_apply_of_mem B tau (2 * k) hx)
  have hOuterCard : outer.card ≤ 2 * B.carrier.card := by
    simpa [outer, d] using
      (Erdos3.card_dilate_one_add_le_two_mul hBreg (2 * k) hsmall)
  have hOuterPos : 0 < outer.card := by
    exact outer.card_pos.mpr (by
      simpa [outer] using
        (B.ndilate (1 + (((2 * k : ℕ) : NNReal) * tau))).carrier_nonempty)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hR : (c * X.card)⁻¹ ≤ R := by
    have hOr : (0 : ℝ) < outer.card := by exact_mod_cast hOuterPos
    have hXr : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    have hOr' : (outer.card : ℝ) ≤ 2 * B.carrier.card := by
      exact_mod_cast hOuterCard
    calc
      (c * (X.card : ℝ))⁻¹ = (outer.card : ℝ) / X.card := by
        dsimp [c]
        field_simp
      _ ≤ (2 * B.carrier.card : ℝ) / X.card :=
        (div_le_div_iff_of_pos_right hXr).2 hOr'
      _ = R := by simp [R]
  have hzero : (0 : AddChar (ZMod N) ℂ) ∈ S := by
    exact zero_mem_chang_largeSpectrum_half C.carrier
  have hneg : ∀ s ∈ S, -s ∈ S := by
    intro s hs
    exact neg_mem_chang_largeSpectrum hs
  have hDk : D < (k : ℝ) := by
    calc
      D ≤ (⌈D⌉₊ : ℝ) := Nat.le_ceil D
      _ < ((⌈D⌉₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.lt_succ_self ⌈D⌉₊
      _ = (k : ℝ) := by simp [k, localChangCap, D]
  have hdim : ∀ Gamma, Gamma ⊆ T → AddDissociatedMod S Gamma →
      Gamma.card ≤ k → (Gamma.card : ℝ) ≤ D := by
    intro Gamma hGammaT hGammaMod hGammaCard
    have hq : ∀ psi, psi ∉ S →
        ‖Erdos3.massCoeff w psi‖ ≤ (1 / 2 : ℝ) ^ (2 * k) := by
      intro psi hpsi
      calc
        ‖Erdos3.massCoeff w psi‖ ≤
            ‖Erdos3.massCoeff
              (realUniformMass (B.ndilate tau).carrier) psi‖ ^ (2 * k) := by
          exact Erdos3.norm_massCoeff_bohrSmoothingMeasure_le
            B tau (2 * k) psi
        _ ≤ (1 / 2 : ℝ) ^ (2 * k) := by
          gcongr
          exact (Erdos3.norm_massCoeff_realUniformMass_lt_half_of_not_mem_largeSpectrum
            (B.ndilate tau).carrier (B.ndilate tau).carrier_nonempty psi
              (by simpa [S, C] using hpsi)).le
    have hweighted : IsWeightedDissociated w 1 Gamma := by
      apply hGammaMod.isWeightedDissociated_of_le_quarter_pow
        hw0 hw1 (by positivity) hq hGammaCard
      rw [pow_mul]
      norm_num
    have hcard := card_weightedDissociated_realFinsetIndicator_le
      B.carrier X hXB hX w c R eta hw0 hwconst hc hR heta Gamma
        hweighted (by simpa [T] using hGammaT)
    simpa [D, localChangDimension, R] using hcard
  obtain ⟨Delta, hDeltaT, _, hDeltaCard, hcover⟩ :=
    exists_maximal_addDissociatedMod_card_le S T hzero hneg D k hDk hdim
  refine ⟨rho, C, Delta, hrhoHalf, hrhoOne, ?_, hCreg, ?_, ?_, ?_⟩
  · simp [C, tau, a]
  · simpa [D] using hDeltaCard
  · simpa [T] using hDeltaT
  · simpa [T, S] using hcover

end

end Erdos3.RelativeChangSanders

end

end OAI
