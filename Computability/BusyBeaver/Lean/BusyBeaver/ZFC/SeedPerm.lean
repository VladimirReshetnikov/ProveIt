import BusyBeaver.ZFC.L2RootPerm

/-!
The seed start of the 215's enumerator, and the program layer from its boot registers.

The 215 boots into the root with `nextproof = 4` and every other register zero. As in
`Seed222`, the enumerator is complete from there (Source 159's cofinal argument): a derivation of
the code 1 compiles into `START_Y ++ B_1 ++ [DROP, NIP, NIP]`, which halts from every register
state, and with `Y = 4` its candidate number `P 3 (P 4 (P 1 r))` is at least 4, so it is reached
unless the run halts first. Soundness is the stack invariant.

`dagPerm_seed_iff`: the structured program `dagPerm`, iterated from the boot registers, halts
iff the code 1 is derivable in `C222`.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumPerm

open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222
open SetTheory.BusyBeaver.ZFC.KCodeDom

attribute [local irreducible] P

/-- The 215's seed: candidate 4, every other register zero. -/
def seed : St := ⟨0, 4, 0, 0, 0, 0⟩

def HaltsFrom (s : St) : Prop := ∃ n s', run n s = some s' ∧ enumStep s' = none

theorem reach_from (sd : St) (hpl : sd.pl = 0) : ∀ k : Nat,
    (∃ n s, run n sd = some s ∧ s.pl = 0 ∧ s.np = sd.np + k) ∨ HaltsFrom sd
  | 0 => Or.inl ⟨0, sd, rfl, hpl, rfl⟩
  | k + 1 => by
      rcases reach_from sd hpl k with ⟨n, s, hr, hpl', hnp⟩ | hh
      · match hs : enumStep s with
        | none => exact Or.inr ⟨n, s, hr, hs⟩
        | some s1 =>
          have hnp1 : s1.np = sd.np + (k + 1) := by rw [step_start hpl' hs, hnp]; omega
          have hr1 : run (n + 1) sd = some s1 := by
            rw [run_add n 1 sd s hr]; simp only [run, hs]
          rcases drain s1.pl s1 (Nat.le_refl _) with ⟨j, s', hr', h1, h2⟩ | ⟨j, s', hr', h1⟩
          · left
            exact ⟨n + 1 + j, s', by rw [run_add (n + 1) j sd s1 hr1]; exact hr', h1, h2.trans hnp1⟩
          · right
            exact ⟨n + 1 + j, s', by rw [run_add (n + 1) j sd s1 hr1]; exact hr', h1⟩
      · exact Or.inr hh

theorem seed_sound : HaltsFrom seed → C222 F := by
  rintro ⟨n, s, hrun, hstep⟩
  exact halt_step (run_inv n ⟨C222.truth, C222.truth, good_zero⟩ hrun) hstep

theorem encL_ge (Y : Nat) (cs : List Cmd) : Y ≤ encL (.ax 0 1 Y) cs := by
  have key : ∀ r, Y ≤ pack (.ax 0 1 Y) r := fun r =>
    Nat.le_trans (le_P_left Y (P 1 r)) (le_P_right (0 + 3) (P Y (P 1 r)))
  cases cs with
  | nil => exact key 0
  | cons c' cs => exact key _

theorem seed_complete (h : C222 F) : HaltsFrom seed := by
  obtain ⟨p, hp⟩ := build (cdom_of_c222 h)
  let cs := p ++ [.drop, .nip, .nip]
  have hN := encL_ge 4 cs
  rcases reach_from seed rfl (encL (.ax 0 1 4) cs - 4) with ⟨n, s, hr, hpl, hnp⟩ | hh
  · have hf : (fetch s).1 = encL (.ax 0 1 4) cs := by
      simp only [fetch, hpl, if_true]; rw [hnp]; simp only [seed]; omega
    obtain ⟨k, s', hr', hs'⟩ := exec_list cs (.ax 0 1 4) s hf (program_none 4 p hp _)
    exact ⟨n + k, s', by rw [run_add n k seed s hr]; exact hr', hs'⟩
  · exact hh

theorem seed_iff : HaltsFrom seed ↔ C222 F := ⟨seed_sound, seed_complete⟩

end SetTheory.BusyBeaver.ZFC.EnumPerm

namespace SetTheory.BusyBeaver.ZFC.L2Perm

open RMDag DagPerm Code254
open L2K (enc)

/-- The 215's boot registers: `nextproof = 4`. -/
def bootRegs : Regs := upd (fun _ => 0) 0 4

theorem enc_seed : enc (toAS EnumPerm.seed) = bootRegs := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [enc, toAS, EnumPerm.seed, bootRegs, upd]

/-- **L2 + L1 from the boot registers**: `dagPerm` halts iff the code 1 is derivable. -/
theorem dagPerm_seed_iff : IterHalts dagPerm bootRegs ↔ KCode222.C222 F := by
  rw [← enc_seed, iter_iff]
  exact EnumPerm.seed_iff

#print axioms dagPerm_seed_iff

end SetTheory.BusyBeaver.ZFC.L2Perm
