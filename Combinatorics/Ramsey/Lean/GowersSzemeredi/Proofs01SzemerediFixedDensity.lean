import GowersSzemeredi.Sections01_03
import OAI.Combinatorics.Progressions.FixedDensity.Conclusions

/-!
# Theorem 1.2 (Szemerédi) from the vendored fixed-density theorem

The catalogue's qualitative Theorem 1.2 is proved here by a route different
from Gowers's: the vendored subset of the openai/math Lean library
(`lib/openai-math`, Apache-2.0; see its README) proves, by ordered hypergraph
regularity and removal, that for every `k ≥ 2` and `δ > 0` there is `c > 0`
such that every subset of `ZMod M` of density at least `δ` spans at least
`c M²` pairs `(a, d)` with `a, a + d, …, a + (k-1)d` in the set
(`OAI.Erdos3.FixedDensity.szemeredi`).

A set `A ⊆ [1, N]` of density `δ` is a subset of `ZMod (2N + 1)` of density
at least `δ / 3`; no reduction wraps around, so a cyclic progression with
nonzero difference lifts to an integer progression in `A`
(`hasNatAP_of_cyclic`), and once `2N + 1 > 1 / c` the trivial pairs with
`d = 0` cannot account for all `c M²` pairs (`exists_pos_product`).

This does not prove the quantitative Theorems 1.3 or 18.2: the vendored
constant `c` is not explicit.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace LeanProofs.GowersSzemeredi

namespace SzemerediFixedDensity

open OAI.Erdos3.FixedDensity

/-- Cyclic progressions with nonzero difference among the residues of a set of
integers in `[1, N]`, modulo `M > 2N`, are integer progressions. -/
theorem hasNatAP_of_cyclic {N M k : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N)
    (hk : 2 ≤ k) (hM : 2 * N < M) (a d : ZMod M) (hd : d ≠ 0)
    (hmem : ∀ j : Fin k, cyclicAPTerm a d j ∈ A.image (fun n : ℕ => (n : ZMod M))) :
    HasNatAP A k := by
  classical
  have hx : ∀ i, i < k → ∃ n ∈ A, (n : ZMod M) = a + (i : ZMod M) * d := by
    intro i hi
    obtain ⟨n, hn, h⟩ := Finset.mem_image.mp (hmem ⟨i, hi⟩)
    refine ⟨n, hn, ?_⟩
    simpa [cyclicAPTerm] using h
  choose! x hxA hxeq using hx
  have hbound : ∀ i, i < k → 1 ≤ x i ∧ x i ≤ N := fun i hi =>
    Finset.mem_Icc.mp (hA (hxA i hi))
  have hcast : ∀ i, i + 1 < k →
      ((x (i + 1) : ZMod M) - (x i : ZMod M)) = d := by
    intro i hi
    rw [hxeq (i + 1) hi, hxeq i (by omega)]
    push_cast
    ring
  have hstep : ∀ i, i + 1 < k →
      (x (i + 1) : ℤ) - x i = (x 1 : ℤ) - x 0 := by
    intro i hi
    have h1 := hcast i hi
    have h2 := hcast 0 (by omega)
    have hdvd : (M : ℤ) ∣ ((x (i + 1) : ℤ) - x i) - ((x 1 : ℤ) - x 0) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp only [zero_add] at h2
      linear_combination h1 - h2
    have hb1 := hbound (i + 1) hi
    have hb2 := hbound i (by omega)
    have hb3 := hbound 1 (by omega)
    have hb4 := hbound 0 (by omega)
    have habs : |((x (i + 1) : ℤ) - x i) - ((x 1 : ℤ) - x 0)| < M := by
      rw [abs_lt]
      constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    linarith
  have hlin : ∀ i, i < k → (x i : ℤ) = x 0 + i * ((x 1 : ℤ) - x 0) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 := hstep i hi
      have h2 := ih (by omega)
      push_cast
      linarith
  have he : (x 1 : ℤ) - x 0 ≠ 0 := by
    intro he0
    apply hd
    have h2 := hcast 0 (by omega)
    have h3 : (x 1 : ZMod M) = (x 0 : ZMod M) := by
      have : (x 1 : ℤ) = x 0 := by linarith
      exact_mod_cast congrArg (fun z : ℤ => (z : ZMod M)) this
    simp only [zero_add] at h2
    rw [← h2, h3, sub_self]
  rcases lt_or_gt_of_ne he with hneg | hpos
  · -- negative difference: read the progression backwards from `x (k - 1)`
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = -((x 1 : ℤ) - x 0) :=
      ⟨(-((x 1 : ℤ) - x 0)).toNat, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨x (k - 1), t, by omega, fun i hi => ?_⟩
    have h := hlin (k - 1 - i) (by omega)
    have h' := hlin (k - 1) (by omega)
    have c1 : ((k - 1 - i : ℕ) : ℤ) = (k : ℤ) - 1 - i := by omega
    have c2 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    have key : ((x (k - 1) + i * t : ℕ) : ℤ) = (x (k - 1 - i) : ℤ) := by
      push_cast
      rw [h, h', c1, c2, ht]
      ring
    have key' : x (k - 1) + i * t = x (k - 1 - i) := by exact_mod_cast key
    rw [key']
    exact hxA _ (by omega)
  · obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = (x 1 : ℤ) - x 0 :=
      ⟨((x 1 : ℤ) - x 0).toNat, Int.toNat_of_nonneg hpos.le⟩
    refine ⟨x 0, t, by omega, fun i hi => ?_⟩
    have h := hlin i hi
    have key : ((x 0 + i * t : ℕ) : ℤ) = (x i : ℤ) := by
      push_cast
      rw [h, ht]
    have key' : x 0 + i * t = x i := by exact_mod_cast key
    rw [key']
    exact hxA i hi

/-- If the normalized count of cyclic `k`-progressions of a `[0, 1]`-valued
function exceeds `1 / M`, some progression with nonzero difference has
positive weight: the pairs with `d = 0` contribute at most `1 / M`. -/
theorem exists_pos_product {k M : ℕ} [NeZero M] (g : ZMod M → ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) {c : ℝ}
    (hc : c ≤ cyclicAPCount k M g) (hcM : 1 / (M : ℝ) < c) :
    ∃ a d : ZMod M, d ≠ 0 ∧ 0 < cyclicAPProduct k M g a d := by
  classical
  by_contra hcon
  push_neg at hcon
  have hle : ∀ a d, cyclicAPProduct k M g a d ≤ finsetIndicator ({0} : Finset (ZMod M)) d := by
    intro a d
    by_cases hd : d = 0
    · subst hd
      rw [finsetIndicator_of_mem (by simp)]
      exact Finset.prod_le_one (fun j _ => hg0 _) (fun j _ => hg1 _)
    · rw [finsetIndicator_of_not_mem (by simpa using hd)]
      exact hcon a d hd
  have hinner : ∀ a, mean (fun d => cyclicAPProduct k M g a d) ≤ 1 / (M : ℝ) := by
    intro a
    calc mean (fun d => cyclicAPProduct k M g a d)
        ≤ mean (finsetIndicator ({0} : Finset (ZMod M))) :=
          Finset.expect_le_expect (fun d _ => hle a d)
      _ = 1 / (M : ℝ) := by rw [mean_finsetIndicator]; simp [ZMod.card]
  have hmean : cyclicAPCount k M g ≤ 1 / (M : ℝ) := by
    calc cyclicAPCount k M g = mean (fun a => mean (fun d => cyclicAPProduct k M g a d)) := rfl
      _ ≤ mean (fun _ : ZMod M => 1 / (M : ℝ)) := Finset.expect_le_expect (fun a _ => hinner a)
      _ = 1 / (M : ℝ) := mean_const _
  linarith

end SzemerediFixedDensity

open SzemerediFixedDensity OAI.Erdos3.FixedDensity in
/-- **Theorem 1.2 (Szemerédi).** -/
theorem theorem_1_2_holds : theorem_1_2 := by
  intro k δ hk hδ
  classical
  obtain ⟨c, hc, hcount⟩ := szemeredi (max k 2) (le_max_right _ _) (δ := δ / 3) (by positivity)
  refine ⟨⌈1 / c⌉₊ + 1, by omega, fun A hA hdens => ?_⟩
  set N := ⌈1 / c⌉₊ + 1 with hNdef
  set M := 2 * N + 1 with hMdef
  haveI : NeZero M := ⟨by omega⟩
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hMpos : (0 : ℝ) < M := by positivity
  have hMle : (M : ℝ) ≤ 3 * N := by
    have : M ≤ 3 * N := by omega
    exact_mod_cast this
  let A' : Finset (ZMod M) := A.image (fun n : ℕ => (n : ZMod M))
  have hinj : Set.InjOn (fun n : ℕ => (n : ZMod M)) A := by
    intro n hn m hm h
    have hn' := Finset.mem_Icc.mp (hA hn)
    have hm' := Finset.mem_Icc.mp (hA hm)
    have := congrArg ZMod.val h
    simp only at this
    rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this
  have hcard : A'.card = A.card := Finset.card_image_of_injOn hinj
  have hdensA' : δ / 3 ≤ mean (finsetIndicator A') := by
    rw [mean_finsetIndicator, ZMod.card, hcard]
    rw [div_le_div_iff₀ (by norm_num) hMpos]
    nlinarith
  have hcM : 1 / (M : ℝ) < c := by
    have h1 : 1 / c ≤ (⌈1 / c⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈1 / c⌉₊ : ℝ) < M := by
      have : ⌈1 / c⌉₊ < M := by omega
      exact_mod_cast this
    have h3 : 1 / c < M := lt_of_le_of_lt h1 h2
    rw [div_lt_iff₀ hMpos]
    rw [div_lt_iff₀ hc] at h3
    linarith
  have hg0 : ∀ x, 0 ≤ finsetIndicator A' x := fun x => by
    unfold finsetIndicator; split_ifs <;> norm_num
  have hg1 : ∀ x, finsetIndicator A' x ≤ 1 := fun x => by
    unfold finsetIndicator; split_ifs <;> norm_num
  obtain ⟨a, d, hd, hpos⟩ :=
    exists_pos_product (finsetIndicator A') hg0 hg1 (hcount M A' hdensA') hcM
  have hmem : ∀ j : Fin (max k 2), cyclicAPTerm a d j ∈ A' := by
    intro j
    by_contra hj
    have hzero : cyclicAPProduct (max k 2) M (finsetIndicator A') a d = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (finsetIndicator_of_not_mem hj)
    linarith
  obtain ⟨a₀, d₀, hd₀, hap⟩ :=
    hasNatAP_of_cyclic A hA (le_max_right k 2) (by omega) a d hd hmem
  exact ⟨a₀, d₀, hd₀, fun i hi => hap i (lt_of_lt_of_le hi (le_max_left k 2))⟩

end LeanProofs.GowersSzemeredi
