import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

def modularTagWeight (h : ℕ) : ℕ := 2 ^ h * h.factorial

theorem modularTagWeight_pos (h : ℕ) : 0 < modularTagWeight h :=
  Nat.mul_pos (pow_pos (by decide) _) (Nat.factorial_pos _)

theorem modularTagWeight_mono : Monotone modularTagWeight := by
  intro i j hij
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hij) (Nat.factorial_le hij)

theorem modularTagWeight_succ (h : ℕ) :
    modularTagWeight (h + 1) = 2 * (h + 1) * modularTagWeight h := by
  simp only [modularTagWeight, pow_succ, Nat.factorial_succ]
  ring

theorem exists_modular_tag_gap {s : ℕ} (hs : 0 < s) (depth : Fin s → ℕ) :
    ∃ h : Fin s,
      (∀ i, depth i ≤ (2 ^ s * s.factorial) * depth h) ∧
      (∀ j : Fin s, h.val < j.val → 2 * (h.val + 1) * depth j < depth h) := by
  let : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  let weight (i : Fin s) := depth i * modularTagWeight i.val
  let score (i : Fin s) := weight i * (s + 1) + i.val
  obtain ⟨h, _, hmax⟩ := Finset.exists_max_image Finset.univ score Finset.univ_nonempty
  have hweight (i : Fin s) : weight i ≤ weight h := by
    have hi := hmax i (Finset.mem_univ i)
    dsimp only [score] at hi
    have hh := h.isLt
    have hs0 : 0 < s + 1 := by omega
    nlinarith
  refine ⟨h, ?_, ?_⟩
  · intro i
    have hi1 : 1 ≤ modularTagWeight i.val := modularTagWeight_pos i.val
    have hhbound : modularTagWeight h.val ≤ modularTagWeight s := modularTagWeight_mono h.isLt.le
    calc
      _ ≤ weight i := by dsimp only [weight]; nlinarith
      _ ≤ weight h := hweight i
      _ ≤ (2 ^ s * s.factorial) * depth h := by
        dsimp only [weight]
        simpa only [modularTagWeight, Nat.mul_comm] using Nat.mul_le_mul_left (depth h) hhbound
  · intro j hj
    by_contra! hbad
    have hwj : 2 * (h.val + 1) * modularTagWeight h.val ≤ modularTagWeight j.val := by
      rw [← modularTagWeight_succ]
      exact modularTagWeight_mono (Nat.succ_le_of_lt hj)
    have hW : weight h ≤ weight j := by
      calc
        _ = depth h * modularTagWeight h.val := rfl
        _ ≤ (2 * (h.val + 1) * depth j) * modularTagWeight h.val :=
          Nat.mul_le_mul_right _ hbad
        _ = depth j * (2 * (h.val + 1) * modularTagWeight h.val) := by ring
        _ ≤ depth j * modularTagWeight j.val := Nat.mul_le_mul_left _ hwj
        _ = weight j := rfl
    have hscore := hmax j (Finset.mem_univ j)
    dsimp only [score] at hscore
    nlinarith

theorem exists_modular_uncharged_depth {s : ℕ} (hs : 0 < s)
    (depth : Fin s → ℕ) (a b e : ℕ)
    (hmax : ∀ i, depth i ≤ a) (hattained : ∃ i, depth i = a)
    (hlarge : 4 * s * (2 ^ s * s.factorial) * (b + e) < a) :
    ∃ (h : Fin s) (k B : ℕ),
      a ≤ (2 ^ s * s.factorial) * depth h ∧
      e ≤ k ∧ (∀ j : Fin s, h.val < j.val → depth j ≤ k) ∧
      2 * (h.val + 1) * k < depth h ∧
      B = depth h - (h.val + 1) * k ∧
      depth h < 2 * B ∧ b < B ∧ B ≤ a - k := by
  classical
  obtain ⟨h, hbound, hgap⟩ := exists_modular_tag_gap hs depth
  obtain ⟨i, hi⟩ := hattained
  have habound : a ≤ (2 ^ s * s.factorial) * depth h := hi ▸ hbound i
  let D := 2 ^ s * s.factorial
  have hD : 0 < D := Nat.mul_pos (pow_pos (by decide) _) (Nat.factorial_pos _)
  have hsmall : 4 * s * (b + e) < depth h := by
    apply (Nat.mul_lt_mul_left hD).mp
    have hlarge' : D * (4 * s * (b + e)) < a := by
      dsimp only [D]
      nlinarith [hlarge]
    exact hlarge'.trans_le habound
  have hdeg : h.val + 1 ≤ s := Nat.succ_le_of_lt h.isLt
  have he : 2 * (h.val + 1) * e < depth h := by
    calc
      _ ≤ 2 * s * e := Nat.mul_le_mul_right e (Nat.mul_le_mul_left 2 hdeg)
      _ ≤ 4 * s * (b + e) := by nlinarith
      _ < _ := hsmall
  let Q := insert e ((Finset.univ.filter (fun j : Fin s => h.val < j.val)).image depth)
  have hQ : Q.Nonempty := Finset.insert_nonempty _ _
  let k := Q.max' hQ
  have hek : e ≤ k := Finset.le_max' Q e (Finset.mem_insert_self _ _)
  have hjk (j : Fin s) (hj : h.val < j.val) : depth j ≤ k :=
    Finset.le_max' Q _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩))
  have hk : 2 * (h.val + 1) * k < depth h := by
    have hkQ : k ∈ Q := Finset.max'_mem Q hQ
    rcases Finset.mem_insert.mp hkQ with hke | hki
    · simpa only [hke] using he
    · obtain ⟨j, hj, hjk⟩ := Finset.mem_image.mp hki
      simpa only [← hjk] using hgap j (Finset.mem_filter.mp hj).2
  have hk2 : 2 * ((h.val + 1) * k) < depth h := by nlinarith [hk]
  let B := depth h - (h.val + 1) * k
  have hprod : (h.val + 1) * k ≤ depth h := by omega
  have hsum : B + (h.val + 1) * k = depth h := Nat.sub_add_cancel hprod
  have hb : 2 * b < depth h := by
    have h := Nat.mul_le_mul_right (b + e) (show 2 ≤ 4 * s by omega)
    omega
  have hkprod : k ≤ (h.val + 1) * k := by nlinarith
  refine ⟨h, k, B, habound, hek, hjk, hk, rfl, ?_, ?_, ?_⟩
  · omega
  · omega
  · have hh := hmax h
    omega

end Erdos3

end

end OAI
