import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealPurePowerExchange

/-!
# Incompatible cutoff optima for ideals in every number field

Greedy predecessors occur at strictly smaller norms. Thus simultaneous
optimality at all cutoffs forces the whole greedy template at each norm
layer, even when several different ideals have the same norm. The pure
power exchange contradicts optimality at the eighth prime-power cutoff.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

omit [NumberField K] in
theorem greedySmoothIdeals_subset_range (S : Finset (HeightOneSpectrum (𝓞 K))) :
    greedySmoothIdeals S ⊆ Set.range (smoothMultiplier S) := Set.image_subset_range _ _

/-- A nongreedy smooth ideal is the last term of an integral-ratio progression
from two greedy ideals with smaller norms. -/
theorem exists_greedySmooth_predecessors (S : Finset (HeightOneSpectrum (𝓞 K)))
    {I : (Ideal (𝓞 K))⁰} (hI : I ∈ Set.range (smoothMultiplier S)) (hn : I ∉ greedySmoothIdeals S) :
    ∃ A ∈ greedySmoothIdeals S, ∃ B ∈ greedySmoothIdeals S,
      absNorm A.val < absNorm B.val ∧ absNorm B.val < absNorm I.val ∧ A*I = B*B ∧ A ∣ B := by
  classical
  obtain ⟨e,rfl⟩ := hI
  have hng : ¬ ∀ p : S, e p ∈ greedyExponents := fun h ↦ hn ⟨e,h,rfl⟩
  push Not at hng
  obtain ⟨p,hp⟩ := hng
  choose a b ha hb hab hbe he hlt using fun p : S ↦ exists_greedyPredecessors (e p)
  have hp' := hlt p hp
  refine ⟨smoothMultiplier S a, ⟨a,ha,rfl⟩, smoothMultiplier S b, ⟨b,hb,rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact profileNorm_strict_of_le S hab (fun h ↦ hp'.1.ne (congrArg (fun f : S → ℕ ↦ f p) h))
  · exact profileNorm_strict_of_le S hbe (fun h ↦ hp'.2.ne (congrArg (fun f : S → ℕ ↦ f p) h))
  · rw [← smoothMultiplier_add, ← smoothMultiplier_add]
    exact congrArg (smoothMultiplier S) (funext he)
  · exact (smoothMultiplier_dvd_iff S).mpr hab

/-- For each admissible smooth ideal set, there is an integer cutoff at most
`Norm(p)^8` where another admissible smooth set has at least one more ideal.
This holds for both ratio conventions. -/
theorem exists_better_smooth_cutoff (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S)
    (integral : Bool) {D : Set (Ideal (𝓞 K))⁰} (hD : D ⊆ Set.range (smoothMultiplier S))
    (hvalid : IdealAdmissible integral D) :
    ∃ k : ℕ, 0 < k ∧ k ≤ absNorm p.val.asIdeal ^ 8 ∧
      ∃ E : Set (Ideal (𝓞 K))⁰, E ⊆ Set.range (smoothMultiplier S) ∧ IdealAdmissible integral E ∧
        countUpTo D (k : ℝ) < countUpTo E (k : ℝ) := by
  classical
  let M := absNorm p.val.asIdeal ^ 8
  let G := greedySmoothIdeals S
  by_contra hNo
  have noBetter (k : ℕ) (hk : 0 < k) (hkM : k ≤ M) (E : Set (Ideal (𝓞 K))⁰)
      (hE : E ⊆ Set.range (smoothMultiplier S)) (hEf : IdealAdmissible integral E) :
      countUpTo E (k : ℝ) ≤ countUpTo D (k : ℝ) :=
    le_of_not_gt fun h ↦ hNo ⟨k,hk,hkM,E,hE,hEf,h⟩
  have layers (k : ℕ) : k ≤ M → idealNormCutoff D k = idealNormCutoff G k := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hsub : idealNormCutoff D k ⊆ idealNormCutoff G k := by
        intro I hI
        refine ⟨?_,hI.2⟩
        by_contra hIg
        obtain ⟨A,hAg,B,hBg,hAB,hBI,he,hd⟩ := exists_greedySmooth_predecessors S (hD hI.1) hIg
        have earlier {J : (Ideal (𝓞 K))⁰} (hJ : J ∈ G) (hJk : absNorm J.val < k) : J ∈ D := by
          have h₁ := ih _ hJk (hJk.le.trans hk)
          have h₂ : J ∈ idealNormCutoff G (absNorm J.val) := ⟨hJ,le_rfl⟩
          rw [← h₁] at h₂
          exact h₂.1
        have hIk : absNorm I.val ≤ k := hI.2
        have hBD := earlier hBg (hBI.trans_le hIk)
        have hAD := earlier hAg (hAB.trans (hBI.trans_le hIk))
        have hab := hvalid hAD hBD hI.1 he (fun _ ↦ hd)
        exact hAB.ne (congrArg (fun J : (Ideal (𝓞 K))⁰ ↦ absNorm J.val) hab)
      have hcount : (idealNormCutoff G k).ncard ≤ (idealNormCutoff D k).ncard := by
        by_cases hk₀ : 0 < k
        · rw [← countUpTo_nat_eq_ncard, ← countUpTo_nat_eq_ncard]
          exact noBetter k hk₀ hk G (greedySmoothIdeals_subset_range S) (idealAdmissible_greedySmoothIdeals S integral)
        · have h₀ : idealNormCutoff G k = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro I hI
            have h₁ : absNorm I.val ≤ k := hI.2
            have h₂ := absNorm_pos_of_nonZeroDivisors I
            omega
          simp [h₀]
      exact Set.eq_of_subset_of_ncard_le hsub hcount (idealNormCutoff_finite _ _)
  have hm := layers M le_rfl
  have hsame : countUpTo D (M : ℝ) = countUpTo G (M : ℝ) := by
    rw [countUpTo_nat_eq_ncard, countUpTo_nat_eq_ncard, hm]
  have hm₀ : 0 < M := Nat.pow_pos (zero_lt_one.trans (primeIdeal_norm_gt_one p.val))
  have hle := noBetter M hm₀ le_rfl (purePowerExchange S p) (purePowerExchange_subset_range S p)
    (idealAdmissible_purePowerExchange S p integral)
  rw [countUpTo_purePowerExchange] at hle
  change countUpTo G (M : ℝ) + 1 ≤ countUpTo D (M : ℝ) at hle
  rw [hsame] at hle
  omega

end GRHArticle.ProgressionFree.NumberFieldIdeals
