import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem exists_exponential_constant_fiber {α β : Type*}
    (S : Finset α) (hS : S.Nonempty) (f : α → β) (A : Set β) (hA : A.Finite)
    (hf : ∀ x ∈ S, f x ∈ A) {C : ℝ} (hcount : (A.ncard : ℝ) ≤ Real.exp C) :
    ∃ y ∈ A, ∃ T : Finset α, T ⊆ S ∧ T.Nonempty ∧ (∀ x ∈ T, f x = y) ∧
      Real.exp (-C) * S.card ≤ (T.card : ℝ) := by
  classical
  have hf' : ∀ x ∈ S, f x ∈ hA.toFinset := fun x hx => hA.mem_toFinset.mpr (hf x hx)
  have hAne : hA.toFinset.Nonempty := by
    obtain ⟨x, hx⟩ := hS
    exact ⟨f x, hf' x hx⟩
  have hn : hA.toFinset.card • (Real.exp (-C) * S.card) ≤ (S.card : ℝ) := by
    rw [nsmul_eq_mul, ← Set.ncard_eq_toFinset_card A hA]
    calc
      (A.ncard : ℝ) * (Real.exp (-C) * S.card) ≤
          Real.exp C * (Real.exp (-C) * S.card) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = (S.card : ℝ) := by rw [← mul_assoc, ← Real.exp_add]; simp
  obtain ⟨y, hy, hlarge⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := S) (t := hA.toFinset) (f := f) hf' hAne hn
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr hS
  have htpos : 0 < (S.filter (fun x => f x = y)).card := by
    exact_mod_cast (mul_pos (Real.exp_pos (-C)) hpos).trans_le hlarge
  exact ⟨y, hA.mem_toFinset.mp hy, S.filter (fun x => f x = y), Finset.filter_subset _ _,
    Finset.card_pos.mp htpos, fun x hx => (Finset.mem_filter.mp hx).2, hlarge⟩

end Erdos3

end

section

namespace Erdos3

def CyclicShortShiftSet {N : ℕ} (H : Finset (ZMod N)) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, 2 * |(x.val : ℤ) - y.val| < (N : ℤ)

theorem exists_cyclicShortShiftSet {N : ℕ} [NeZero N]
    (H : Finset (ZMod N)) (hH : H.Nonempty) :
    ∃ S : Finset (ZMod N), S ⊆ H ∧ S.Nonempty ∧
      (H.card : ℝ) / 2 ≤ (S.card : ℝ) ∧ CyclicShortShiftSet S := by
  classical
  let label (x : ZMod N) : Bool := decide (2 * x.val < N)
  have hcount : (Finset.univ : Finset Bool).card • ((H.card : ℝ) / 2) ≤ (H.card : ℝ) := by
    norm_num
    linarith
  obtain ⟨b, _, hb⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := H) (t := (Finset.univ : Finset Bool)) (f := label)
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty hcount
  let S := H.filter (fun x => label x = b)
  have hpos : (0 : ℝ) < H.card := by exact_mod_cast hH.card_pos
  have hS : S.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (half_pos hpos).trans_le hb
  refine ⟨S, Finset.filter_subset _ _, hS, hb, ?_⟩
  intro x hx y hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  have hxN := x.val_lt
  have hyN := y.val_lt
  cases b <;> simp only [label, decide_eq_false_iff_not, decide_eq_true_eq] at hx' hy'
  · by_cases hxy : (y.val : ℤ) ≤ x.val
    · rw [abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonpos (by omega)]
      omega
  · by_cases hxy : (y.val : ℤ) ≤ x.val
    · rw [abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonpos (by omega)]
      omega

theorem CyclicShortShiftSet.integer_relation {N : ℕ} [NeZero N]
    {H : Finset (ZMod N)} (hH : CyclicShortShiftSet H)
    {x₁ x₂ x₃ x₄ : ZMod N} (h₁ : x₁ ∈ H) (h₂ : x₂ ∈ H)
    (h₃ : x₃ ∈ H) (h₄ : x₄ ∈ H) (hrel : x₁ - x₂ = x₃ - x₄) :
    (x₁.val : ℤ) - x₂.val = (x₃.val : ℤ) - x₄.val := by
  let d₁ : ℤ := (x₁.val : ℤ) - x₂.val
  let d₂ : ℤ := (x₃.val : ℤ) - x₄.val
  have hd₁ : 2 * |d₁| < (N : ℤ) := hH x₁ h₁ x₂ h₂
  have hd₂ : 2 * |d₂| < (N : ℤ) := hH x₃ h₃ x₄ h₄
  have hcast : (d₁ : ZMod N) = (d₂ : ZMod N) := by
    simpa only [d₁, d₂, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val] using hrel
  have hdvd : (N : ℤ) ∣ d₂ - d₁ :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub d₁ d₂ N).mp hcast
  have habs : |d₂ - d₁| < (N : ℤ) :=
    (abs_sub d₂ d₁).trans_lt (by omega)
  have hsmall : (d₂ - d₁).natAbs < (N : ℤ).natAbs := by
    apply Int.ofNat_lt.mp
    simpa only [Int.natCast_natAbs, abs_of_nonneg (Int.natCast_nonneg N)] using habs
  have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd hsmall
  change d₁ = d₂
  omega

theorem CyclicShortShiftSet.quadruple_relation {N : ℕ} [NeZero N]
    {H : Finset (ZMod N)} (hH : CyclicShortShiftSet H) (a h k : ZMod N)
    (h₁ : h ∈ H) (h₂ : h - a ∈ H) (h₃ : k ∈ H) (h₄ : k - a ∈ H) :
    -(h.val : ℤ) + (h - a).val + k.val - (k - a).val = 0 := by
  have heq := hH.integer_relation h₁ h₂ h₃ h₄ (by abel : h - (h - a) = k - (k - a))
  omega

end Erdos3

end

end OAI
