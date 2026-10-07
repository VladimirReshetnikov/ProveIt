-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3

theorem abs_finset_prod_sub_prod_le {ι : Type*} (S : Finset ι) (f g : ι → ℝ)
    {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ S, |f i| ≤ B) (hg : ∀ i ∈ S, |g i| ≤ B)
    (hdiff : ∀ i ∈ S, |f i - g i| ≤ δ) :
    |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| ≤ S.card * δ * B ^ S.card := by
  classical
  revert hf hg hdiff
  induction S using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert a S ha ih =>
    intro hf hg hdiff
    have hfS := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgS := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hdS := fun i hi => hdiff i (Finset.mem_insert_of_mem hi)
    have hrec := ih hfS hgS hdS
    have hprod : |∏ i ∈ S, g i| ≤ B ^ S.card := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _i ∈ S, B := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) hgS
        _ = _ := by simp
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = |f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) + (f a - g a) * ∏ i ∈ S, g i| := by
        congr 1
        ring
      _ ≤ |f a| * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| + |f a - g a| * |∏ i ∈ S, g i| := by
        simpa only [abs_mul] using abs_add_le
          (f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)) ((f a - g a) * ∏ i ∈ S, g i)
      _ ≤ B * (S.card * δ * B ^ S.card) + δ * B ^ S.card :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self _ _)) hrec
          (abs_nonneg _) (by linarith))
          (mul_le_mul (hdiff a (Finset.mem_insert_self _ _)) hprod (abs_nonneg _) hδ)
      _ = (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ S.card := by rw [pow_succ]; ring
      _ ≤ (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ (S.card + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.le_succ _)) hδ)
      _ = _ := by push_cast; ring

theorem abs_pow_sub_pow_box_bound {x y B δ : ℝ} {n s : ℕ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (hxy : |x - y| ≤ δ) (hn : n ≤ s) :
    |x ^ n - y ^ n| ≤ δ * s * B ^ s := by
  apply (abs_pow_sub_pow_le x y n).trans
  apply mul_le_mul (mul_le_mul hxy (Nat.cast_le.mpr hn) (Nat.cast_nonneg _) hδ)
  · exact (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) (max_le hx hy) _).trans
      (pow_le_pow_right₀ hB (by omega))
  · positivity
  · positivity

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_finset_prod_sub_prod_le {ι : Type*} (S : Finset ι) (f g : ι → ℂ)
    {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ B) (hg : ∀ i ∈ S, ‖g i‖ ≤ B)
    (hdiff : ∀ i ∈ S, ‖f i - g i‖ ≤ δ) :
    ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ ≤ S.card * δ * B ^ S.card := by
  classical
  revert hf hg hdiff
  induction S using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert a S ha ih =>
    intro hf hg hdiff
    have hrec := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hdiff i (Finset.mem_insert_of_mem hi))
    have hprod : ‖∏ i ∈ S, g i‖ ≤ B ^ S.card := by
      rw [norm_prod]
      calc
        _ ≤ ∏ _i ∈ S, B := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
          (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        _ = _ := by simp
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = ‖f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) +
          (f a - g a) * ∏ i ∈ S, g i‖ := by congr 1; ring
      _ ≤ ‖f a‖ * ‖(∏ i ∈ S, f i) - ∏ i ∈ S, g i‖ +
          ‖f a - g a‖ * ‖∏ i ∈ S, g i‖ := by
        simpa only [norm_mul] using norm_add_le
          (f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)) ((f a - g a) * ∏ i ∈ S, g i)
      _ ≤ B * (S.card * δ * B ^ S.card) + δ * B ^ S.card :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self _ _)) hrec
          (norm_nonneg _) (zero_le_one.trans hB))
          (mul_le_mul (hdiff a (Finset.mem_insert_self _ _)) hprod (norm_nonneg _) hδ)
      _ = (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ S.card := by rw [pow_succ]; ring
      _ ≤ (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ (S.card + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.le_succ _)) hδ)
      _ = _ := by push_cast; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem abs_prod_sub_prod_le_envelope {I : Type*} (s : Finset I) (f g : I → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      (∏ i ∈ s, (f i + |f i - g i|)) - ∏ i ∈ s, f i := by
  classical
  revert hf hg
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert a s ha ih =>
    intro hf hg
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hrec := ih hf' hg'
    have hga : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg hg'
    have hprod : (∏ i ∈ s, g i) ≤ ∏ i ∈ s, (f i + |f i - g i|) := by
      apply Finset.prod_le_prod₀ hg'
      intro i hi
      linarith [neg_abs_le (f i - g i)]
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    calc
      _ = |f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) +
          (f a - g a) * ∏ i ∈ s, g i| := by congr 1; ring
      _ ≤ f a * |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| +
          |f a - g a| * ∏ i ∈ s, g i := by
        simpa only [abs_mul, abs_of_nonneg (hf a (Finset.mem_insert_self _ _)),
          abs_of_nonneg hga] using abs_add_le
            (f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
            ((f a - g a) * ∏ i ∈ s, g i)
      _ ≤ f a * ((∏ i ∈ s, (f i + |f i - g i|)) - ∏ i ∈ s, f i) +
          |f a - g a| * ∏ i ∈ s, (f i + |f i - g i|) :=
        add_le_add (mul_le_mul_of_nonneg_left hrec (hf a (Finset.mem_insert_self _ _)))
          (mul_le_mul_of_nonneg_left hprod (abs_nonneg _))
      _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def uniformProductAccuracy (N : ℕ) (C δ : ℝ) : ℝ :=
  min 1 (δ / (((N : ℝ) + 1) * (C + 2) ^ N))

theorem uniformProductAccuracy_spec (N : ℕ) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    0 < uniformProductAccuracy N C δ ∧ uniformProductAccuracy N C δ ≤ 1 ∧
      (N : ℝ) * uniformProductAccuracy N C δ * (C + 2) ^ N ≤ δ := by
  have hD : 0 < ((N : ℝ) + 1) * (C + 2) ^ N := by positivity
  have he : 0 < uniformProductAccuracy N C δ := lt_min zero_lt_one (div_pos hδ hD)
  refine ⟨he, min_le_left _ _, ?_⟩
  have hbound : uniformProductAccuracy N C δ * (((N : ℝ) + 1) * (C + 2) ^ N) ≤ δ :=
    (le_div_iff₀ hD).mp (min_le_right _ _)
  have hp : 0 ≤ uniformProductAccuracy N C δ * (C + 2) ^ N := by positivity
  nlinarith

theorem norm_prod_sub_prod_le_uniform_accuracy {A : Type*} [Fintype A]
    (N : ℕ) (hcard : Fintype.card A ≤ N) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (f g : A → ℂ) (hg : ∀ a, ‖g a‖ ≤ C)
    (herr : ∀ a, ‖f a - g a‖ ≤ uniformProductAccuracy N C δ) :
    ‖(∏ a, f a) - ∏ a, g a‖ ≤ δ := by
  obtain ⟨he0, he1, heδ⟩ := uniformProductAccuracy_spec N hC hδ
  have hB : 1 ≤ C + 2 := by linarith
  have hf (a : A) : ‖f a‖ ≤ C + 2 := by
    have hn : ‖f a‖ ≤ ‖f a - g a‖ + ‖g a‖ := by
      simpa only [sub_add_cancel] using norm_add_le (f a - g a) (g a)
    linarith [herr a, hg a]
  have hprod := norm_finset_prod_sub_prod_le Finset.univ f g hB he0.le
    (fun a _ => hf a) (fun a _ => (hg a).trans (by linarith)) (fun a _ => herr a)
  have hc : (Fintype.card A : ℝ) ≤ N := by exact_mod_cast hcard
  calc
    _ ≤ (Fintype.card A : ℝ) * uniformProductAccuracy N C δ * (C + 2) ^ Fintype.card A := by
      simpa only [Finset.card_univ] using hprod
    _ ≤ (N : ℝ) * uniformProductAccuracy N C δ * (C + 2) ^ N :=
      mul_le_mul (mul_le_mul_of_nonneg_right hc he0.le)
        (pow_le_pow_right₀ hB hcard) (pow_nonneg (by linarith) _) (by positivity)
    _ ≤ δ := heδ

end Erdos3

end

end OAI
