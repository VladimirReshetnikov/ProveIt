import EnumNoFiller254

/-!
Parity-complete refutation candidates, 17 October 2026.

This file proves that the original full-logic enumerator, and the verified
MP-filler omission, both have uniformly halting candidate words in every
cofinal parity class whenever Code254.C254 F holds.  It is a source-level
completeness fact.  It does not prove a binary loader's physical contract.

The uniform reset argument is extracted from Enum254.complete at ProveIt
85633fd2f57b5dca16f87667699134d1b500ebc0.  It also appears, with padding,
as EnumSafeStart254.padded_program_halts in that source tree.
-/

namespace SetTheory.BusyBeaver.ZFC.ParityCandidates254

open Code254

/-- Among the three safe prefix opcodes, either parity is available. -/
theorem prefix_parity (q e : Nat) (he : e < 2) :
    ∃ a : Nat, a ≤ 2 ∧ P a q % 2 = e := by
  have h01 : P 1 q = P 0 q + q + 1 := by
    simp only [P, Cantor.toNat, Nat.zero_add]
    rw [show 1 + q = q + 1 by omega, Cantor.tri]
    omega
  have h12 : P 2 q = P 1 q + q + 2 := by
    simp only [P, Cantor.toNat]
    rw [show 2 + q = (1 + q) + 1 by omega, Cantor.tri]
    omega
  by_cases h0 : P 0 q % 2 = e
  · exact ⟨0, by omega, h0⟩
  by_cases h1 : P 1 q % 2 = e
  · exact ⟨1, by omega, h1⟩
  exact ⟨2, by omega, by omega⟩

/-- A prefix argument at least the requested bound gives a candidate in any
prescribed arithmetic progression of step two, beyond that bound. -/
theorem prefix_progression (r g B : Nat) :
    ∃ a k : Nat, a ≤ 2 ∧ B ≤ P a (P (g + B) r) ∧
      P a (P (g + B) r) = g + 2 * k := by
  obtain ⟨a, ha, hp⟩ := prefix_parity (P (g + B) r) (g % 2) (by omega)
  have hl : g + B ≤ P a (P (g + B) r) :=
    Nat.le_trans (le_P_left _ _) (le_P_right _ _)
  refine ⟨a, P a (P (g + B) r) / 2 - g / 2, ha, by omega, ?_⟩
  omega

namespace Original

open Enum254

/-- The full original calculus produces a word halting from every working
register state, without assuming that its stack or registers are sound. -/
theorem uniform_of_refutation (h : C254 F) :
    ∃ c : Cmd, ∃ cs : List Cmd, ∀ w, cexec (c :: cs) w = none := by
  obtain ⟨p, hp⟩ := build h
  refine ⟨.ax 0 1 1 0, p ++ [.drop 0, .nip 0, .nip 0], ?_⟩
  intro w
  obtain ⟨t, S, d, hh⟩ := w
  rw [cexec_cons_some (cstep_ax 0 1 1 0 t S d hh), cexec_append]
  rcases hp (gate (d + 1) (hh + 1) 0) (axStack (d + 1) hh (hh + 1) 0 0 t S) with hn | hs
  · rw [hn]
  · rw [hs]
    simp only
    rw [cexec_cons_some (cstep_drop 0 F _ 0 0)]
    simp only [Nat.add_zero]
    rw [cexec_cons_some (cstep_nip 0 0 _ 0 0 (by omega))]
    simp only [unP_P', Nat.add_zero]
    exact cexec_cons_none (cstep_nip_one 0 0 _ 0)

def safePrefix (a x : Nat) : Cmd := if a = 0 then .mp x else if a = 1 then .drop x else .nip x

theorem pack_prefix (a x r : Nat) (ha : a ≤ 2) :
    pack (safePrefix a x) r = P a (P x r) := by
  have : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases this with rfl | rfl | rfl <;> simp [safePrefix, pack]

theorem prefix_uniform (c : Cmd) (cs : List Cmd) (h : ∀ w, cexec cs w = none) :
    ∀ w, cexec (c :: cs) w = none := by
  intro w
  simp only [cexec]
  cases cstep c w with
  | none => rfl
  | some v => exact h v

/-- Cofinal candidate completeness for every progression g, g+2, g+4, ... . -/
theorem cofinal_uniform_parity (h : C254 F) (g B : Nat) :
    ∃ c : Cmd, ∃ cs : List Cmd, ∃ k : Nat,
      B ≤ encL c cs ∧ encL c cs = g + 2 * k ∧
        ∀ w, cexec (c :: cs) w = none := by
  obtain ⟨c, cs, hw⟩ := uniform_of_refutation h
  obtain ⟨a, k, ha, hB, hk⟩ := prefix_progression (encL c cs + 1) g B
  refine ⟨safePrefix a (g + B), c :: cs, k, ?_, ?_, prefix_uniform _ _ hw⟩
  · simpa only [encL, pack_prefix a (g + B) (encL c cs + 1) ha] using hB
  · simpa only [encL, pack_prefix a (g + B) (encL c cs + 1) ha] using hk

end Original

namespace NoFiller

open EnumNoFiller254

theorem uniform_of_refutation (h : C254 F) :
    ∃ c : Cmd, ∃ cs : List Cmd, ∀ w, cexec (c :: cs) w = none := by
  obtain ⟨p, hp⟩ := build h
  refine ⟨.ax 0 1 1 0, p ++ [.drop 0, .nip 0, .nip 0], ?_⟩
  intro w
  obtain ⟨t, S, d, hh⟩ := w
  rw [cexec_cons_some (cstep_ax 0 1 1 0 t S d hh), cexec_append]
  rcases hp (gate (d + 1) (hh + 1) 0) (axStack (d + 1) hh (hh + 1) 0 0 t S) with hn | hs
  · rw [hn]
  · rw [hs]
    simp only
    rw [cexec_cons_some (cstep_drop 0 F _ 0 0)]
    simp only [Nat.add_zero]
    rw [cexec_cons_some (cstep_nip 0 0 _ 0 0 (by omega))]
    simp only [unP_P', Nat.add_zero]
    exact cexec_cons_none (cstep_nip_one 0 0 _ 0)

def safePrefix (a x : Nat) : Cmd := if a = 0 then .mp x else if a = 1 then .drop x else .nip x

theorem pack_prefix (a x r : Nat) (ha : a ≤ 2) :
    pack (safePrefix a x) r = P a (P x r) := by
  have : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  rcases this with rfl | rfl | rfl <;> simp [safePrefix, pack]

theorem prefix_uniform (c : Cmd) (cs : List Cmd) (h : ∀ w, cexec cs w = none) :
    ∀ w, cexec (c :: cs) w = none := by
  intro w
  simp only [cexec]
  cases cstep c w with
  | none => rfl
  | some v => exact h v

theorem cofinal_uniform_parity (h : C254 F) (g B : Nat) :
    ∃ c : Cmd, ∃ cs : List Cmd, ∃ k : Nat,
      B ≤ encL c cs ∧ encL c cs = g + 2 * k ∧
        ∀ w, cexec (c :: cs) w = none := by
  obtain ⟨c, cs, hw⟩ := uniform_of_refutation h
  obtain ⟨a, k, ha, hB, hk⟩ := prefix_progression (encL c cs + 1) g B
  refine ⟨safePrefix a (g + B), c :: cs, k, ?_, ?_, prefix_uniform _ _ hw⟩
  · simpa only [encL, pack_prefix a (g + B) (encL c cs + 1) ha] using hB
  · simpa only [encL, pack_prefix a (g + B) (encL c cs + 1) ha] using hk

end NoFiller

#print axioms Original.cofinal_uniform_parity
#print axioms NoFiller.cofinal_uniform_parity

end SetTheory.BusyBeaver.ZFC.ParityCandidates254
