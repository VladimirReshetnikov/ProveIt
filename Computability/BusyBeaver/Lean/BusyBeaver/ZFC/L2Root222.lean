/- Forked by hand from L2Root254.lean for dag222: the AX leaf (node 149) enters node 236. -/
import BusyBeaver.ZFC.RMDagIteration
import BusyBeaver.ZFC.L2Axioms222

/-!
L2: one run of the root of the seed-K 222 program dag222 is one enumerator step.

`ax_eval` evaluates the generated `axioms()` composite symbolically: the
stack becomes `Enum222.axStack` and the current formula the gated bundle.
-/

namespace SetTheory.BusyBeaver.ZFC.L2K

open RMDag Dag222 Code254
open L2 (dec_brk dec_halt pass fall)

attribute [local irreducible] Code254.P

/-! ## The dispatch -/

/-- The AX leaf (node 149) runs `axioms()` and breaks out of the dispatch. -/
theorem ax_leaf (st : AS) (hc : Clean st) :
    Run dag222 (.node 149) (enc st) (.brk 1) (enc (f236 st)) :=
  brk_cdr (p := dag222) (n := 149) (k := 0) rfl (l236 st hc) (Run.brkS 0 _)

theorem dispatch_mp (st : AS) (hc : Clean st) (h0 : st.ac = 0) :
    Rn (.node 141) st (if wim st.tw st.p1 = st.p2
      then { st with tw := st.p1, ws := P 0 st.ws, p2 := 0 } else { st with tw := 0, p2 := 0 }) :=
  seqAS (n := 141) rfl (skip (p := dag222) (n := 142) rfl (Run.decZero 3 _ (by simp [enc, h0])))
    (mp_branch st hc)

theorem dispatch_drop (st : AS) (hc : Clean st) :
    Rn (.node 141) { st with ac := 1 } { st with ac := 0, tw := st.p2, ws := P st.tw st.ws } :=
  skip rfl (dec_brk rfl 0 rfl (fall rfl rfl rfl rfl (par2 { st with ac := 0 } hc)))

theorem dispatch_nip (st : AS) (hc : Clean st) (hh : st.p2 ≠ 1) :
    Rn (.node 141) { st with ac := 2 }
      { st with ac := 0, p2 := (Cantor.ofNat st.ws).1, ws := (Cantor.ofNat st.ws).2 } :=
  skip rfl (dec_brk rfl 1 rfl (pass rfl rfl (dec_brk rfl 0 rfl
    (fall rfl rfl rfl rfl (nip_branch { st with ac := 0 } hc hh)))))

theorem dispatch_nip_halt (st : AS) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ R', Run dag222 (.node 141) (enc { st with ac := 2 }) .halt R' := by
  obtain ⟨R', hR'⟩ := nip_halt { st with ac := 0 } hc hh
  exact ⟨R', halt_car rfl (dec_halt rfl 1 rfl (halt_car rfl (halt_car rfl (dec_halt rfl 0 rfl
    (halt_car rfl (halt_cdr rfl (skip rfl (Run.decZero 3 _ (by simp [enc]))) hR'))))))⟩

theorem dispatch_ax (st : AS) (hc : Clean st) (c : Nat) :
    Rn (.node 141) { st with ac := c + 3 } (f236 { st with ac := c }) :=
  skip rfl (dec_brk rfl (c + 2) rfl (pass rfl rfl (dec_brk rfl (c + 1) rfl
    (pass rfl rfl (dec_brk rfl c rfl (ax_leaf _ hc))))))

/-! ## One root run is one enumerator step -/

/-- Enumerator states as boundary register files. -/
def toAS (s : Enum222.St) : AS := ⟨s.np, s.tw, s.ws, 0, s.d, s.h, 0, 0, s.pl⟩

theorem fetch_run (s : Enum222.St) :
    Rn (.node 133) (toAS s) ⟨(Enum222.fetch s).2, s.tw, s.ws, 0, s.d, s.h, 0, 0, (Enum222.fetch s).1⟩ := by
  by_cases h : s.pl = 0
  · have := fetch_zero (toAS s) (by simp [toAS, h]) rfl
    apply rn_eq this
    simp [toAS, Enum222.fetch, h]
  · obtain ⟨v, hv⟩ : ∃ v, s.pl = v + 1 := ⟨s.pl - 1, by omega⟩
    have := fetch_pos (toAS s) v (by simp [toAS, hv])
    apply rn_eq this
    simp [toAS, Enum222.fetch, hv]

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
    | none => ∃ R', Run dag222 (.node 0) (enc (toAS s)) .halt R' := by
  have hf := fetch_run s
  unfold Enum222.enumStep Enum222.execAt
  generalize (Enum222.fetch s).1 = pl1 at hf ⊢
  generalize (Enum222.fetch s).2 = np1 at hf ⊢
  have hc : ∀ np tw ws ac p1 p2 pl, Clean (⟨np, tw, ws, ac, p1, p2, 0, 0, pl⟩ : AS) := fun _ _ _ _ _ _ _ =>
    ⟨rfl, rfl⟩
  have hreads := fun {X : AS} (hd : Rn (.node 141) ⟨np1, s.tw, s.ws, (Cantor.ofNat pl1).1,
      s.d + (Cantor.ofNat (Cantor.ofNat pl1).2).1, s.h, 0, 0, (Cantor.ofNat (Cantor.ofNat pl1).2).2⟩ X) =>
    seqAS (n := 0) rfl hf (reads_run np1 pl1 s.tw s.ws s.d s.h hd)
  generalize hx : (Cantor.ofNat (Cantor.ofNat pl1).2).1 = x at hreads ⊢
  generalize hp3 : (Cantor.ofNat (Cantor.ofNat pl1).2).2 = pl3 at hreads ⊢
  generalize hy : (Cantor.ofNat pl3).1 = y at ⊢
  generalize hp4 : (Cantor.ofNat pl3).2 = pl4 at ⊢
  generalize hac : (Cantor.ofNat pl1).1 = ac at hreads ⊢
  rcases ac with _ | _ | _ | c
  · -- MP
    have := hreads (dispatch_mp ⟨np1, s.tw, s.ws, 0, s.d + x, s.h, 0, 0, pl3⟩ (hc _ _ _ _ _ _ _) rfl)
    simp only
    split
    · rename_i hw
      simp only [hw, if_true] at this
      exact rn_eq this (by simp [toAS])
    · rename_i hw
      simp only [hw, if_false] at this
      exact rn_eq this (by simp [toAS])
  · -- DROP
    have := hreads (dispatch_drop ⟨np1, s.tw, s.ws, 0, s.d + x, s.h, 0, 0, pl3⟩ (hc _ _ _ _ _ _ _))
    exact rn_eq this (by simp [toAS])
  · -- NIP
    by_cases hh : s.h = 1
    · simp only [hh, if_true]
      obtain ⟨R', hR'⟩ := dispatch_nip_halt ⟨np1, s.tw, s.ws, 0, s.d + x, s.h, 0, 0, pl3⟩
        (hc _ _ _ _ _ _ _) hh
      have h174 := read_ac ⟨np1, s.tw, s.ws, 0, s.d, s.h, 0, 0, pl1⟩ ⟨rfl, rfl⟩
      have h175 := read_p1 { (⟨np1, s.tw, s.ws, 0, s.d, s.h, 0, 0, pl1⟩ : AS) with
        pl := (Cantor.ofNat pl1).2, ac := 0 + (Cantor.ofNat pl1).1 } ⟨rfl, rfl⟩
      simp only [Nat.zero_add, hac, hx, hp3] at h174 h175
      have h140 := halt_cdr (p := dag222) (n := 140) rfl h175 hR'
      have h139 := halt_cdr (p := dag222) (n := 139) rfl h174 h140
      exact ⟨R', halt_cdr (p := dag222) (n := 0) rfl hf h139⟩
    · simp only [hh, if_false]
      have := hreads (dispatch_nip ⟨np1, s.tw, s.ws, 0, s.d + x, s.h, 0, 0, pl3⟩ (hc _ _ _ _ _ _ _) hh)
      exact rn_eq this (by simp [toAS])
  · -- AX
    have := hreads (dispatch_ax ⟨np1, s.tw, s.ws, 0, s.d + x, s.h, 0, 0, pl3⟩ (hc _ _ _ _ _ _ _) c)
    apply rn_eq this
    simp only [ax_eval, toAS, hy, hp4]

/-! ## Iteration -/

/-- L2: iterating the program root halts iff the enumerator halts. -/
theorem iter_iff (s : Enum222.St) :
    IterHalts dag222 (enc (toAS s)) ↔ ∃ n s', Enum222.run n s = some s' ∧ Enum222.enumStep s' = none :=
  RMDag.iter_halts_iff Enum222.enumStep Enum222.run (fun s => enc (toAS s))
    (fun _ => rfl) (fun n s => by cases h : Enum222.enumStep s <;> simp only [Enum222.run, h])
    (fun {s s'} h => by have := root_step s; rwa [h] at this)
    (fun {s} h => by have := root_step s; rwa [h] at this) s

theorem iter_iff_halts : IterHalts dag222 (enc (toAS Enum222.s0)) ↔ Enum222.Halts := iter_iff _

/-- The first two candidates (MP on truth, then DROP) lead to `nextproof = 2`
with every other register zero: the state reached by the machine's boot. -/
def s2 : Enum222.St := ⟨0, 2, 0, 0, 0, 0⟩

theorem run_s0_s2 : Enum222.run 2 Enum222.s0 = some s2 := by
  have h0 : wim 0 0 = 0 := by simp [wim, P_zero_zero]
  have hP : P 0 0 = 0 := P_zero_zero
  have e1 : Enum222.enumStep Enum222.s0 = some ⟨0, 1, 0, 0, 0, 0⟩ := by
    simp [Enum222.enumStep, Enum222.execAt, Enum222.fetch, Enum222.s0, h0, hP, Cantor.ofNat]
  have e2 : Enum222.enumStep ⟨0, 1, 0, 0, 0, 0⟩ = some s2 := by
    simp [Enum222.enumStep, Enum222.execAt, Enum222.fetch, s2, hP, Cantor.ofNat]
  simp [Enum222.run, e1, e2]

/-- L2 from the boot register file `nextproof = 2`, all other registers zero. -/
theorem iter_halts_boot : IterHalts dag222 (enc (toAS s2)) ↔ Enum222.Halts := by
  rw [iter_iff]
  constructor
  · rintro ⟨n, s', h1, h2⟩
    exact ⟨2 + n, s', by rw [Enum222.run_add 2 n _ _ run_s0_s2]; exact h1, h2⟩
  · rintro ⟨n, s', h1, h2⟩
    have hs0 : Enum222.enumStep Enum222.s0 = some ⟨0, 1, 0, 0, 0, 0⟩ := by
      simp [Enum222.enumStep, Enum222.execAt, Enum222.fetch, Enum222.s0, wim, P_zero_zero, Cantor.ofNat]
    have hs1 : Enum222.enumStep ⟨0, 1, 0, 0, 0, 0⟩ = some s2 := by
      simp [Enum222.enumStep, Enum222.execAt, Enum222.fetch, s2, P_zero_zero, Cantor.ofNat]
    match n, h1 with
    | 0, h1 => simp [Enum222.run] at h1; subst h1; rw [hs0] at h2; cases h2
    | 1, h1 => simp [Enum222.run, hs0] at h1; subst h1; rw [hs1] at h2; cases h2
    | n + 2, h1 =>
        refine ⟨n, s', ?_, h2⟩
        simpa [Enum222.run, hs0, hs1] using h1

theorem enc_s2 : enc (toAS s2) = upd (fun _ => 0) 0 2 := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [enc, toAS, s2, upd]

/-- L2 composed with L1: the seed-K 222 program dag222, iterated from the boot registers
(`nextproof = 2`), halts iff the falsity code is derivable in the code calculus. -/
theorem program_halts_iff : IterHalts dag222 (upd (fun _ => 0) 0 2) ↔ KCode222.C222 F := by
  rw [← enc_s2, iter_halts_boot, Enum222.enum_halts_iff]

end SetTheory.BusyBeaver.ZFC.L2K
