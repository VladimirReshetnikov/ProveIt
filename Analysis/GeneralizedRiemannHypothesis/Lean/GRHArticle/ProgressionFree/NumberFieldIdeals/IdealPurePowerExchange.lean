import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothAdmissibility

/-!
# A better ideal template at the eighth prime power

Replace the pure powers of one prime by the exponents `0, 1, 3, 7, 8`.
Any new progression has zero valuation at every other prime, where the
binary ternary rules still apply.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The admissible smooth ideals whose exponents have only binary ternary digits. -/
noncomputable def greedySmoothIdeals (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Set (Ideal (𝓞 K))⁰ :=
  smoothMultiplier S '' {e | ∀ p, e p ∈ greedyExponents}

theorem idealAdmissible_greedySmoothIdeals (S : Finset (HeightOneSpectrum (𝓞 K))) (integral : Bool) :
    IdealAdmissible integral (greedySmoothIdeals S) := by
  apply (idealAdmissible_smoothMultiplier_image_iff S integral _).mpr
  intro a b c ha hb hc he _
  exact funext fun p ↦ threeAPFree_greedyExponents (ha p) (hb p) (hc p)
    (congrArg (fun e : S → ℕ ↦ e p) he)

/-- The profile supported at one prime. -/
noncomputable def pureProfile {ι : Type*} (p : ι) (e : ℕ) : ι → ℕ := by
  classical
  exact fun q ↦ if q = p then e else 0

@[simp] theorem pureProfile_self {ι : Type*} (p : ι) (e : ℕ) : pureProfile p e p = e := by
  classical
  simp [pureProfile]

@[simp] theorem pureProfile_other {ι : Type*} {p q : ι} (h : q ≠ p) (e : ℕ) :
    pureProfile p e q = 0 := by
  classical
  simp [pureProfile, h]

private theorem pureProfile_injective {ι : Type*} (p : ι) : Function.Injective (pureProfile p) := by
  intro a b h
  simpa only [pureProfile_self] using congrArg (fun e : ι → ℕ ↦ e p) h

omit [NumberField K] in
theorem smoothMultiplier_pureProfile (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) (e : ℕ) :
    smoothMultiplier S (pureProfile p e) = primeIdeal p.val ^ e := by
  classical
  rw [smoothMultiplier, Finset.prod_eq_single p]
  · rw [pureProfile_self]
  · intro q _ hq
    simp only [pureProfile_other hq, pow_zero]
  · simp

theorem profileNorm_pureProfile (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) (e : ℕ) :
    profileNorm S (pureProfile p e) = absNorm p.val.asIdeal ^ e := by
  simp [profileNorm, smoothMultiplier_pureProfile, primeIdeal]

private def greedyProfiles {ι : Type*} : Set (ι → ℕ) := {a | ∀ q, a q ∈ greedyExponents}

private noncomputable def greedyCutProfiles (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) :
    Set (S → ℕ) := {a | a ∈ greedyProfiles ∧ profileNorm S a ≤ absNorm p.val.asIdeal ^ 8}

private noncomputable def exchangedProfiles (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) :
    Set (S → ℕ) := (greedyCutProfiles S p \ {pureProfile p 4}) ∪ {pureProfile p 7, pureProfile p 8}

private theorem pureProfile_mem_greedy_iff {ι : Type*} (p : ι) (e : ℕ) :
    pureProfile p e ∈ greedyProfiles ↔ e ∈ greedyExponents := by
  constructor
  · intro h
    show e ∈ greedyExponents
    simpa only [pureProfile_self] using h p
  · intro h q
    by_cases hq : q = p
    · subst q
      simpa only [pureProfile_self]
    · rw [pureProfile_other hq]
      exact zero_mem_greedyExponents

private theorem pureProfile_mem_exchanged_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) (e : ℕ) :
    pureProfile p e ∈ exchangedProfiles S p ↔ e ∈ exchangedExponents := by
  classical
  have hpow : absNorm p.val.asIdeal ^ e ≤ absNorm p.val.asIdeal ^ 8 ↔ e ≤ 8 := by
    constructor
    · intro h
      by_contra! hn
      exact (Nat.pow_lt_pow_right (primeIdeal_norm_gt_one p.val) hn).not_ge h
    · exact Nat.pow_le_pow_right (zero_lt_one.trans (primeIdeal_norm_gt_one p.val))
  simp only [exchangedProfiles, greedyCutProfiles, Set.mem_union, Set.mem_sdiff, Set.mem_setOf_eq,
    Set.mem_singleton_iff, Set.mem_insert_iff, (pureProfile_injective p).eq_iff,
    pureProfile_mem_greedy_iff, profileNorm_pureProfile, hpow, exchangedExponents,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases h : e ≤ 8
  · simp only [mem_greedyExponents_of_le_eight h, Finset.mem_insert, Finset.mem_singleton]
    omega
  · omega

private theorem profileAdmissible_exchanged (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S)
    (integral : Bool) : ProfileAdmissible integral (exchangedProfiles S p) := by
  intro a b c ha hb hc he _
  have hev (q : S) : a q + c q = b q + b q := congrArg (fun e : S → ℕ ↦ e q) he
  by_cases hg : a ∈ greedyProfiles ∧ b ∈ greedyProfiles ∧ c ∈ greedyProfiles
  · exact funext fun q ↦ threeAPFree_greedyExponents (hg.1 q) (hg.2.1 q) (hg.2.2 q) (hev q)
  have offGreedy {e} (h : e ∈ exchangedProfiles S p) {q : S} (hq : q ≠ p) :
      e q ∈ greedyExponents := by
    rcases h with h | h
    · exact h.1.1 q
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl <;> rw [pureProfile_other hq] <;> exact zero_mem_greedyExponents
  have offZero {e} (h : e ∈ exchangedProfiles S p) (hn : e ∉ greedyProfiles) {q : S} (hq : q ≠ p) :
      e q = 0 := by
    rcases h with h | h
    · exact (hn h.1.1).elim
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl <;> exact pureProfile_other hq _
  have hall (q : S) (hq : q ≠ p) : a q = 0 ∧ b q = 0 ∧ c q = 0 := by
    have hab := threeAPFree_greedyExponents (offGreedy ha hq) (offGreedy hb hq)
      (offGreedy hc hq) (hev q)
    have hzero : a q = 0 ∨ b q = 0 ∨ c q = 0 := by
      by_cases hga : a ∈ greedyProfiles
      · by_cases hgb : b ∈ greedyProfiles
        · exact Or.inr (Or.inr (offZero hc (fun hgc ↦ hg ⟨hga,hgb,hgc⟩) hq))
        · exact Or.inr (Or.inl (offZero hb hgb hq))
      · exact Or.inl (offZero ha hga hq)
    have := hev q
    omega
  have samePure {e : S → ℕ} (h : ∀ q ≠ p, e q = 0) : pureProfile p (e p) = e := by
    funext q
    by_cases hq : q = p
    · subst q
      exact pureProfile_self p (e p)
    · rw [pureProfile_other hq, h q hq]
  have ha' := samePure fun q hq ↦ (hall q hq).1
  have hb' := samePure fun q hq ↦ (hall q hq).2.1
  have hc' := samePure fun q hq ↦ (hall q hq).2.2
  have ha'' : pureProfile p (a p) ∈ exchangedProfiles S p := by rwa [ha']
  have hb'' : pureProfile p (b p) ∈ exchangedProfiles S p := by rwa [hb']
  have hc'' : pureProfile p (c p) ∈ exchangedProfiles S p := by rwa [hc']
  have hu := threeAPFree_exchangedExponents
    ((pureProfile_mem_exchanged_iff S p _).mp ha'')
    ((pureProfile_mem_exchanged_iff S p _).mp hb'')
    ((pureProfile_mem_exchanged_iff S p _).mp hc'') (hev p)
  exact ha'.symm.trans ((congrArg (pureProfile p) hu).trans hb')

/-- The improved smooth ideal set at the cutoff given by the eighth power
of the distinguished prime's norm. -/
noncomputable def purePowerExchange (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) :
    Set (Ideal (𝓞 K))⁰ :=
  smoothMultiplier S '' exchangedProfiles S p

theorem idealAdmissible_purePowerExchange (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S)
    (integral : Bool) : IdealAdmissible integral (purePowerExchange S p) :=
  (idealAdmissible_smoothMultiplier_image_iff S integral _).mpr (profileAdmissible_exchanged S p integral)

/-- An integer norm bound on an ideal set. -/
def idealNormCutoff (A : Set (Ideal (𝓞 K))⁰) (k : ℕ) : Set (Ideal (𝓞 K))⁰ :=
  {I | I ∈ A ∧ absNorm I.val ≤ k}

theorem idealNormCutoff_finite (A : Set (Ideal (𝓞 K))⁰) (k : ℕ) : (idealNormCutoff A k).Finite :=
  (finite_setOf_absNorm_le₀ (S := 𝓞 K) k).subset fun _ h ↦ h.2

theorem countUpTo_nat_eq_ncard (A : Set (Ideal (𝓞 K))⁰) (k : ℕ) :
    countUpTo A (k : ℝ) = (idealNormCutoff A k).ncard := by
  change ({I : (Ideal (𝓞 K))⁰ | I ∈ A ∧ (absNorm I.val : ℝ) ≤ k} : Set _).ncard = _
  congr 1
  ext I
  simp [idealNormCutoff]

private theorem pure_mem_greedyIdeals_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) (e : ℕ) :
    primeIdeal p.val ^ e ∈ greedySmoothIdeals S ↔ e ∈ greedyExponents := by
  rw [← smoothMultiplier_pureProfile S p, greedySmoothIdeals, (smoothMultiplier_injective S).mem_set_image]
  exact pureProfile_mem_greedy_iff p e

theorem purePowerExchange_subset_range (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) :
    purePowerExchange S p ⊆ Set.range (smoothMultiplier S) := Set.image_subset_range _ _

private theorem exchangedProfiles_norm_le (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S)
    {e : S → ℕ} (he : e ∈ exchangedProfiles S p) : profileNorm S e ≤ absNorm p.val.asIdeal ^ 8 := by
  rcases he with he | he
  · exact he.1.2
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl
    · rw [profileNorm_pureProfile]
      exact Nat.pow_le_pow_right (zero_lt_one.trans (primeIdeal_norm_gt_one p.val)) (by decide)
    · rw [profileNorm_pureProfile]

private theorem purePowerExchange_eq_sdiff_union (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) :
    purePowerExchange S p =
      (idealNormCutoff (greedySmoothIdeals S) (absNorm p.val.asIdeal ^ 8) \ {primeIdeal p.val ^ 4}) ∪
        {primeIdeal p.val ^ 7, primeIdeal p.val ^ 8} := by
  have hcut : smoothMultiplier S '' greedyCutProfiles S p =
      idealNormCutoff (greedySmoothIdeals S) (absNorm p.val.asIdeal ^ 8) := by
    ext I
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha.1,rfl⟩,ha.2⟩
    · rintro ⟨⟨a,ha,rfl⟩,hN⟩
      exact ⟨a,⟨ha,hN⟩,rfl⟩
  simp only [purePowerExchange, exchangedProfiles, Set.image_union,
    Set.image_sdiff (smoothMultiplier_injective S), hcut, Set.image_insert_eq, Set.image_singleton,
    smoothMultiplier_pureProfile]

/-- Replacing one pure power by two increases the exact norm-ball count by one. -/
theorem countUpTo_purePowerExchange (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) :
    countUpTo (purePowerExchange S p) ↑(absNorm p.val.asIdeal ^ 8) =
      countUpTo (greedySmoothIdeals S) ↑(absNorm p.val.asIdeal ^ 8) + 1 := by
  let k := absNorm p.val.asIdeal ^ 8
  let G := idealNormCutoff (greedySmoothIdeals S) k
  let x := primeIdeal p.val ^ 4
  let y := primeIdeal p.val ^ 7
  let z := primeIdeal p.val ^ 8
  have hG : G.Finite := idealNormCutoff_finite _ _
  have hx : x ∈ G := by
    constructor
    · rw [pure_mem_greedyIdeals_iff S p, mem_greedyExponents_of_le_eight (by decide)]
      decide
    · change absNorm ((primeIdeal p.val ^ 4 : (Ideal (𝓞 K))⁰).val) ≤ absNorm p.val.asIdeal ^ 8
      rw [← smoothMultiplier_pureProfile S p]
      change profileNorm S (pureProfile p 4) ≤ absNorm p.val.asIdeal ^ 8
      rw [profileNorm_pureProfile]
      exact Nat.pow_le_pow_right (zero_lt_one.trans (primeIdeal_norm_gt_one p.val)) (by decide : 4 ≤ 8)
  have hy : y ∉ G := fun hy ↦ by
    have hyg := (pure_mem_greedyIdeals_iff S p 7).mp hy.1
    rw [mem_greedyExponents_of_le_eight (by decide)] at hyg
    exact (by decide : 7 ∉ ({0, 1, 3, 4} : Finset ℕ)) hyg
  have hz : z ∉ G := fun hz ↦ by
    have hzg := (pure_mem_greedyIdeals_iff S p 8).mp hz.1
    rw [mem_greedyExponents_of_le_eight (by decide)] at hzg
    exact (by decide : 8 ∉ ({0, 1, 3, 4} : Finset ℕ)) hzg
  have hyz : y ≠ z := by
    intro h
    have h' := congrArg (fun I : (Ideal (𝓞 K))⁰ ↦ absNorm I.val) h
    have hpow : absNorm p.val.asIdeal ^ 7 = absNorm p.val.asIdeal ^ 8 := by
      simpa [y, z, primeIdeal] using h'
    exact (Nat.pow_lt_pow_right (primeIdeal_norm_gt_one p.val) (by decide : 7 < 8)).ne hpow
  have hd : Disjoint (G \ {x}) ({y,z} : Set (Ideal (𝓞 K))⁰) := by
    rw [Set.disjoint_left]
    intro I hI hmem
    rcases hmem with rfl | rfl
    · exact hy hI.1
    · exact hz hI.1
  have hbounded : idealNormCutoff (purePowerExchange S p) k = purePowerExchange S p := by
    ext I
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, by
      obtain ⟨e,he,rfl⟩ := h
      exact exchangedProfiles_norm_le S p he⟩⟩
  rw [countUpTo_nat_eq_ncard, countUpTo_nat_eq_ncard, hbounded,
    purePowerExchange_eq_sdiff_union S p, Set.ncard_union_eq hd (hG.sdiff) ((Set.finite_singleton z).insert y),
    Set.ncard_pair hyz]
  have hrem := Set.ncard_sdiff_singleton_add_one hx hG
  change (G \ {x}).ncard + 2 = G.ncard + 1
  omega

end GRHArticle.ProgressionFree.NumberFieldIdeals
