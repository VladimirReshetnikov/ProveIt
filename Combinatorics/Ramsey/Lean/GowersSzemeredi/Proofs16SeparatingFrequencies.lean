import GowersSzemeredi.Proofs16BohrAnnulus

/-! Milićević's Lemma 2.6 in `ℤ/N`: few frequencies separate a finite set.

arXiv:2601.01682, Lemma 2.6. A set `S` of size `k` admits `O(log k)`
characters such that the translates `s + B(Γ, 1/10)`, `s ∈ S`, are
disjoint. The paper picks the characters at random. Here the same halving
argument is made deterministic by averaging:
* for `d ≠ 0` in `ℤ/N`, `N ≥ 7` prime, at most `2⌊N/5⌋ + 1 ≤ N/2`
  frequencies `γ` have `5·|γd| ≤ N` (`small_multiples_card_le`);
* so some `γ` separates at least half of any set `D` of nonzero
  differences (`exists_halving_frequency`);
* iterating, `|D| < 2^m` differences are separated by `m` frequencies
  (`separating_frequencies`).

Applied to `D = (S − S) ∖ {0}`, with `|D| < k²`, this gives `2⌈log₂ k⌉`
frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- `γ` separates `d`: `γd` is farther than `N/5` from zero. -/
def Separates {N : Nat} (γ d : ZMod N) : Prop := N < 5 * centeredAbs (γ * d)

/-- Few residues are within `N/5` of zero. -/
theorem near_zero_card_le {N : Nat} [NeZero N] (h7 : 7 ≤ N) :
    2 * (Finset.univ.filter fun y : ZMod N => 5 * centeredAbs y ≤ N).card ≤ N := by
  let T := Finset.univ.filter fun y : ZMod N => 5 * centeredAbs y ≤ N
  have hinj : Set.InjOn (fun y : ZMod N => y.valMinAbs) T := by
    intro y _ z _ h
    have := congrArg (fun v : Int => (v : ZMod N)) h
    simpa only [ZMod.coe_valMinAbs] using this
  have hmaps : ∀ y ∈ T, y.valMinAbs ∈ Finset.Icc (-((N / 5 : Nat) : Int)) ((N / 5 : Nat) : Int) := by
    intro y hy
    have h := (Finset.mem_filter.mp hy).2
    unfold centeredAbs at h
    have h' : y.valMinAbs.natAbs ≤ N / 5 := by omega
    rw [Finset.mem_Icc]
    constructor <;> omega
  have hcard : T.card ≤ 2 * (N / 5) + 1 := by
    calc T.card ≤ (Finset.Icc (-((N / 5 : Nat) : Int)) ((N / 5 : Nat) : Int)).card :=
          Finset.card_le_card_of_injOn _ hmaps hinj
      _ = 2 * (N / 5) + 1 := by rw [Int.card_Icc]; omega
  show 2 * T.card ≤ N
  omega

/-- For `d ≠ 0`, few frequencies fail to separate `d`. -/
theorem small_multiples_card_le {N : Nat} [NeZero N] [Fact N.Prime] (h7 : 7 ≤ N)
    {d : ZMod N} (hd : d ≠ 0) :
    2 * (Finset.univ.filter fun γ : ZMod N => ¬ Separates γ d).card ≤ N := by
  have himage : (Finset.univ.filter fun γ : ZMod N => ¬ Separates γ d).image (fun γ => γ * d) =
      Finset.univ.filter fun y : ZMod N => 5 * centeredAbs y ≤ N := by
    ext y
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Separates, not_lt]
    constructor
    · rintro ⟨γ, hγ, rfl⟩
      exact hγ
    · intro hy
      refine ⟨y * d⁻¹, ?_, ?_⟩
      · rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
        exact hy
      · rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  have hinj : Function.Injective fun γ : ZMod N => γ * d := fun a b h => mul_right_cancel₀ hd h
  rw [← Finset.card_image_of_injective _ hinj, himage]
  exact near_zero_card_le h7

/-- **The halving step.** Some frequency separates at least half of any
set of nonzero differences. -/
theorem exists_halving_frequency {N : Nat} [NeZero N] [Fact N.Prime] (h7 : 7 ≤ N)
    (D : Finset (ZMod N)) (hD : (0 : ZMod N) ∉ D) :
    ∃ γ : ZMod N, 2 * (D.filter fun d => ¬ Separates γ d).card ≤ D.card := by
  by_contra hcon
  push Not at hcon
  -- double count the non-separated pairs
  have hsum : ∑ γ : ZMod N, (D.filter fun d => ¬ Separates γ d).card =
      ∑ d ∈ D, (Finset.univ.filter fun γ : ZMod N => ¬ Separates γ d).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hright : 2 * ∑ d ∈ D, (Finset.univ.filter fun γ : ZMod N => ¬ Separates γ d).card ≤
      D.card * N := by
    rw [Finset.mul_sum]
    calc ∑ d ∈ D, 2 * (Finset.univ.filter fun γ : ZMod N => ¬ Separates γ d).card
        ≤ ∑ _d ∈ D, N := Finset.sum_le_sum fun d hd =>
          small_multiples_card_le h7 (fun h => hD (h ▸ hd))
      _ = D.card * N := by rw [Finset.sum_const, smul_eq_mul]
  have hleft : D.card * N < 2 * ∑ γ : ZMod N, (D.filter fun d => ¬ Separates γ d).card := by
    rw [Finset.mul_sum]
    calc D.card * N = ∑ _γ : ZMod N, D.card := by
          rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, mul_comm]
      _ < ∑ γ : ZMod N, 2 * (D.filter fun d => ¬ Separates γ d).card :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun γ _ => hcon γ
  rw [hsum] at hleft
  omega

/-- **Separating frequencies.** `|D| < 2^m` nonzero differences are
separated by at most `m` frequencies. -/
theorem separating_frequencies {N : Nat} [NeZero N] [Fact N.Prime] (h7 : 7 ≤ N) :
    ∀ (m : Nat) (D : Finset (ZMod N)), (0 : ZMod N) ∉ D → D.card < 2 ^ m →
      ∃ Γ : Finset (ZMod N), Γ.card ≤ m ∧ ∀ d ∈ D, ∃ γ ∈ Γ, Separates γ d := by
  intro m
  induction m with
  | zero =>
    intro D _ hcard
    have hD : D = ∅ := Finset.card_eq_zero.mp (by simpa using hcard)
    exact ⟨∅, by simp, fun d hd => absurd (hD ▸ hd) (Finset.notMem_empty d)⟩
  | succ m ih =>
    intro D hD hcard
    obtain ⟨γ, hγ⟩ := exists_halving_frequency h7 D hD
    have hU : (D.filter fun d => ¬ Separates γ d).card < 2 ^ m := by
      rw [pow_succ] at hcard
      omega
    obtain ⟨Γ', hΓ', hsep⟩ := ih (D.filter fun d => ¬ Separates γ d)
      (fun h => hD (Finset.mem_filter.mp h).1) hU
    refine ⟨insert γ Γ', (Finset.card_insert_le _ _).trans (by omega), fun d hd => ?_⟩
    by_cases hγd : Separates γ d
    · exact ⟨γ, Finset.mem_insert_self _ _, hγd⟩
    · obtain ⟨γ', hγ', h'⟩ := hsep d (Finset.mem_filter.mpr ⟨hd, hγd⟩)
      exact ⟨γ', Finset.mem_insert_of_mem hγ', h'⟩

end LeanProofs.GowersSzemeredi
