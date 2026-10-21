/- Forked by Research/ZFC/k225-formal/generate_l2rootdom.py from Seed222.lean for dagDom. -/
import BusyBeaver.ZFC.L2RootDom
import BusyBeaver.ZFC.Seed222

/-!
The seed start of the 217's enumerator, and the program layer from the boot registers.

Forked from `Seed222.lean` by `Research/ZFC/k225-formal/generate_l2rootdom.py`, with EnumDom's
AX command; the boot registers are `L2K.bootRegs`.

The K-family machines boot into Elliot Glazer's seed state (candidate 3, parameter counter 3:
registers `np = 3`, `param1 = 3`), not the zero state. As in `k230-rocq`'s `Seed230.v`, the
enumerator is complete from there: a derivation of the code 1 compiles into a command list
that halts from every register state; its candidate number is at least 3, and every candidate
from the seed on is reached unless the run halts first. Soundness is the stack invariant.

`dagDom_seed_iff`: the structured program `dagDom`, iterated from the boot registers, halts
iff the code 1 is derivable in `C222`.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumDom

open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222
open SetTheory.BusyBeaver.ZFC.KCodeDom

attribute [local irreducible] P

/-- Elliot Glazer's seed: candidate 3, parameter counter 3. -/
def seed : St := ⟨0, 3, 0, 0, 3, 0⟩

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

/-- The compiled program of a derivation of 1 halts from every register state. -/
theorem program_none (p : List Cmd) (hp : Contract p F) :
    ∀ w, cexec (.ax 0 1 1 0 :: (p ++ [.drop 0, .nip 0, .nip 0])) w = none := by
  intro w
  obtain ⟨t, S, d, hh⟩ := w
  rw [cexec_cons_some (cstep_ax 0 1 1 0 t S d hh), cexec_append]
  rcases hp (gate (d + 1 + 0) (hh + 1) 0) (axStack (d + 1 + 0) hh (hh + 1) 0 (d + 1) t S) with hn | hs
  · rw [hn]
  · rw [hs]
    simp only
    rw [cexec_cons_some (cstep_drop 0 F _ 0 0)]
    simp only [Nat.add_zero]
    rw [cexec_cons_some (cstep_nip 0 0 _ 0 0 (by omega))]
    simp only [unP_P', Nat.add_zero]
    exact cexec_cons_none (cstep_nip_one 0 0 _ 0)

theorem encL_ge_three (c x y u : Nat) (cs : List Cmd) : 3 ≤ encL (.ax c x y u) cs := by
  cases cs with
  | nil => simp only [encL, pack]; have := le_P_left (c + 3) (P x (P y (P u 0))); omega
  | cons c' cs =>
      simp only [encL, pack]; have := le_P_left (c + 3) (P x (P y (P u (encL c' cs + 1)))); omega

theorem seed_complete (h : C222 F) : HaltsFrom seed := by
  obtain ⟨p, hp⟩ := build (cdom_of_c222 h)
  let cs := p ++ [.drop 0, .nip 0, .nip 0]
  have hN := encL_ge_three 0 1 1 0 cs
  rcases reach_from seed rfl (encL (.ax 0 1 1 0) cs - 3) with ⟨n, s, hr, hpl, hnp⟩ | hh
  · have hf : (fetch s).1 = encL (.ax 0 1 1 0) cs := by
      simp only [fetch, hpl, if_true]; rw [hnp]; simp only [seed]; omega
    obtain ⟨k, s', hr', hs'⟩ := exec_list cs (.ax 0 1 1 0) s hf (program_none p hp _)
    exact ⟨n + k, s', by rw [run_add n k seed s hr]; exact hr', hs'⟩
  · exact hh

theorem seed_iff : HaltsFrom seed ↔ C222 F := ⟨seed_sound, seed_complete⟩

end SetTheory.BusyBeaver.ZFC.EnumDom

namespace SetTheory.BusyBeaver.ZFC.L2Dom

open RMDag DagDom Code254
open L2K (enc bootRegs)

theorem enc_seed : enc (toAS EnumDom.seed) = bootRegs := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [enc, toAS, EnumDom.seed, bootRegs, upd]

/-- **L2 + L1 from the boot registers**: `dagDom` halts iff the code 1 is derivable. -/
theorem dagDom_seed_iff : IterHalts dagDom bootRegs ↔ KCode222.C222 F := by
  rw [← enc_seed, iter_iff]
  exact EnumDom.seed_iff

#print axioms dagDom_seed_iff

end SetTheory.BusyBeaver.ZFC.L2Dom
