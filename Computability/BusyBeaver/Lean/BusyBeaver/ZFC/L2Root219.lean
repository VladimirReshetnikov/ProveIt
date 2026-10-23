import BusyBeaver.ZFC.RMDagIteration
import BusyBeaver.ZFC.L2Axioms219
import BusyBeaver.ZFC.L2Root222

/-!
Root contracts of `dag219`, transferred from `dag222` through the equivalent
equality test. The programs share Enum222's states, AX effect and step semantics;
`trCore` transfers individual runs and `Dag219.iter_iff` transfers root iteration.
-/

namespace SetTheory.BusyBeaver.ZFC.L2Q

open RMDag Dag219 Code254

attribute [local irreducible] Code254.P

/-! ## The dispatch -/

/-- The AX leaf (node 149) runs `axioms()` and breaks out of the dispatch. -/
theorem ax_leaf (st : AS) (hc : Clean st) :
    Run dag219 (.node 149) (enc st) (.brk 1) (enc (f236 st)) :=
  trCore (n := 149) rfl (L2K.ax_leaf st hc)

theorem dispatch_mp (st : AS) (hc : Clean st) (h0 : st.ac = 0) :
    Rn (.node 141) st (if wim st.tw st.p1 = st.p2
      then { st with tw := st.p1, ws := P 0 st.ws, p2 := 0 } else { st with tw := 0, p2 := 0 }) :=
  trCore (n := 141) rfl (L2K.dispatch_mp st hc h0)

theorem dispatch_drop (st : AS) (hc : Clean st) :
    Rn (.node 141) { st with ac := 1 } { st with ac := 0, tw := st.p2, ws := P st.tw st.ws } :=
  trCore (n := 141) rfl (L2K.dispatch_drop st hc)

theorem dispatch_nip (st : AS) (hc : Clean st) (hh : st.p2 ≠ 1) :
    Rn (.node 141) { st with ac := 2 }
      { st with ac := 0, p2 := (Cantor.ofNat st.ws).1, ws := (Cantor.ofNat st.ws).2 } :=
  trCore (n := 141) rfl (L2K.dispatch_nip st hc hh)

theorem dispatch_nip_halt (st : AS) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ R', Run dag219 (.node 141) (enc { st with ac := 2 }) .halt R' :=
  let ⟨R', h⟩ := L2K.dispatch_nip_halt st hc hh
  ⟨R', trCore (n := 141) rfl h⟩

theorem dispatch_ax (st : AS) (hc : Clean st) (c : Nat) :
    Rn (.node 141) { st with ac := c + 3 } (f236 { st with ac := c }) :=
  trCore (n := 141) rfl (L2K.dispatch_ax st hc c)

/-! ## One root run is one enumerator step -/

/-- Enumerator states as boundary register files. -/
def toAS (s : Enum222.St) : AS := ⟨s.np, s.tw, s.ws, 0, s.d, s.h, 0, 0, s.pl⟩

theorem fetch_run (s : Enum222.St) :
    Rn (.node 133) (toAS s) ⟨(Enum222.fetch s).2, s.tw, s.ws, 0, s.d, s.h, 0, 0, (Enum222.fetch s).1⟩ :=
  trCore (n := 133) rfl (L2K.fetch_run s)

/-- The two reads after the fetch. -/
theorem reads_run (np pl1 tw ws d h : Nat) {X : AS}
    (hd : Rn (.node 141) ⟨np, tw, ws, (Cantor.ofNat pl1).1, d + (Cantor.ofNat (Cantor.ofNat pl1).2).1,
      h, 0, 0, (Cantor.ofNat (Cantor.ofNat pl1).2).2⟩ X) :
    Rn (.node 139) ⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩ X := by
  have h174 := read_ac ⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩ ⟨rfl, rfl⟩
  have h175 := read_p1 { (⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩ : AS) with
    pl := (Cantor.ofNat pl1).2, ac := 0 + (Cantor.ofNat pl1).1 } ⟨rfl, rfl⟩
  simp only [Nat.zero_add] at h174 h175
  exact seqAS (n := 139) rfl h174 (seqAS (n := 140) rfl h175 hd)

theorem root_step (s : Enum222.St) :
    match Enum222.enumStep s with
    | some s' => Rn (.node 0) (toAS s) (toAS s')
    | none => ∃ R', Run dag219 (.node 0) (enc (toAS s)) .halt R' := by
  have h := L2K.root_step s
  cases hs : Enum222.enumStep s <;> simp only [hs] at h ⊢
  · obtain ⟨R', hR'⟩ := h
    exact ⟨R', trCore (n := 0) rfl hR'⟩
  · exact trCore (n := 0) rfl h

/-! ## Iteration -/

/-- L2: iterating the program root halts iff the enumerator halts. -/
theorem iter_iff (s : Enum222.St) :
    IterHalts dag219 (enc (toAS s)) ↔ ∃ n s', Enum222.run n s = some s' ∧ Enum222.enumStep s' = none :=
  (Dag219.iter_iff _).trans (L2K.iter_iff s)

theorem iter_iff_halts : IterHalts dag219 (enc (toAS Enum222.s0)) ↔ Enum222.Halts := iter_iff _

/-- The first two candidates (MP on truth, then DROP) lead to `nextproof = 2`
with every other register zero: the state reached by the machine's boot. -/
def s2 : Enum222.St := ⟨0, 2, 0, 0, 0, 0⟩

theorem run_s0_s2 : Enum222.run 2 Enum222.s0 = some s2 :=
  L2K.run_s0_s2

/-- L2 from the boot register file `nextproof = 2`, all other registers zero. -/
theorem iter_halts_boot : IterHalts dag219 (enc (toAS s2)) ↔ Enum222.Halts :=
  (Dag219.iter_iff _).trans L2K.iter_halts_boot

theorem enc_s2 : enc (toAS s2) = upd (fun _ => 0) 0 2 :=
  L2K.enc_s2

/-- L2 composed with L1: the seed-K 222 program dag219, iterated from the boot registers
(`nextproof = 2`), halts iff the falsity code is derivable in the code calculus. -/
theorem program_halts_iff : IterHalts dag219 (upd (fun _ => 0) 0 2) ↔ KCode222.C222 F :=
  (Dag219.iter_iff _).trans L2K.program_halts_iff

end SetTheory.BusyBeaver.ZFC.L2Q
