import BusyBeaver.ZFC.RMDagIteration
import BusyBeaver.ZFC.L2AxiomsDom

/-!
L2: one run of the root of the 217's program dagDom is one step of EnumDom.

The root fetches the next command and reads its selector and first field (nodes 139, 140).
The dispatch (node 141) runs MP at selector 0, DROP at 1, NIP at 2 and AX at `3 + c`; the AX
leaf runs the dominated AX word, which `ax_eval` (`L2AxiomsDom`) evaluates to EnumDom's AX step.
Adapted from `L2Root222.lean`.
-/

namespace SetTheory.BusyBeaver.ZFC.L2Dom

open RMDag DagDom
open Code254 (P wim F)
open L2K (AS enc Clean upd_ac P_zero_zero)

attribute [local irreducible] Code254.P

/-! ## The dispatch -/

/-- The AX leaf (node 149) runs `axioms()` and breaks out of the dispatch. -/
theorem ax_leaf (st : AS) (hc : Clean st) :
    Run dagDom (.node 149) (enc st) (.brk 1) (enc (f236 st)) :=
  brk_cdr (p := dagDom) (n := 149) (k := 0) rfl (l236 st hc) (Run.brkS 0 _)

theorem dispatch_mp (st : AS) (hc : Clean st) (h0 : st.ac = 0) :
    Rn (.node 141) st (if wim st.tw st.p1 = st.p2
      then { st with tw := st.p1, ws := P 0 st.ws, p2 := 0 } else { st with tw := 0, p2 := 0 }) :=
  seqAS (n := 141) rfl (skip (p := dagDom) (n := 142) rfl (Run.decZero 3 _ (by simp [enc, h0])))
    (mp_branch st hc)

/-! The selector levels 142, 145, 148: a level `a = (DEC ac, b)` decrements; with `b = (c, BREAK)`
and `c = (a', body)`, the next level `a'` either dispatches and breaks out (`pass`) or falls
through at `ac = 0` to the body (`fall`); either way `b` then breaks out of the level. -/

theorem dec_brk {a b : Nat} (ha : dagDom.nodes a = (.decnz 3, .node b)) {st : AS} (k : Nat)
    (hk : st.ac = k + 1) {R : Regs} (hb : Run dagDom (.node b) (enc { st with ac := k }) (.brk 1) R) :
    Run dagDom (.node a) (enc st) (.brk 1) R :=
  L2.dec_brk ha k hk hb

/-- `dec_brk` for a halting run. -/
theorem dec_halt {a b : Nat} (ha : dagDom.nodes a = (.decnz 3, .node b)) {st : AS} (k : Nat)
    (hk : st.ac = k + 1) {R : Regs} (hb : Run dagDom (.node b) (enc { st with ac := k }) .halt R) :
    Run dagDom (.node a) (enc st) .halt R :=
  L2.dec_halt ha k hk hb

theorem pass {b c a' : Nat} {e : Edge} (hb : dagDom.nodes b = (.node c, .brk 1))
    (hc : dagDom.nodes c = (.node a', e)) {R R' : Regs} (h : Run dagDom (.node a') R (.brk 1) R') :
    Run dagDom (.node b) R (.brk 1) R' :=
  L2.pass hb hc h

theorem fall {b c a' x : Nat} {e : Edge} (hb : dagDom.nodes b = (.node c, .brk 1))
    (hc : dagDom.nodes c = (.node a', e)) (ha' : dagDom.nodes a' = (.decnz 3, .node x))
    {st st' : AS} (h0 : st.ac = 0) (he : Run dagDom e (enc st) .normal (enc st')) :
    Run dagDom (.node b) (enc st) (.brk 1) (enc st') :=
  L2.fall hb hc ha' h0 he

theorem dispatch_drop (st : AS) (hc : Clean st) :
    Rn (.node 141) { st with ac := 1 } { st with ac := 0, tw := st.p2, ws := P st.tw st.ws } :=
  skip rfl (dec_brk rfl 0 rfl (fall rfl rfl rfl rfl (par2 { st with ac := 0 } hc)))

theorem dispatch_nip (st : AS) (hc : Clean st) (hh : st.p2 ≠ 1) :
    Rn (.node 141) { st with ac := 2 }
      { st with ac := 0, p2 := (Cantor.ofNat st.ws).1, ws := (Cantor.ofNat st.ws).2 } :=
  skip rfl (dec_brk rfl 1 rfl (pass rfl rfl (dec_brk rfl 0 rfl
    (fall rfl rfl rfl rfl (nip_branch { st with ac := 0 } hc hh)))))

theorem dispatch_nip_halt (st : AS) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ R', Run dagDom (.node 141) (enc { st with ac := 2 }) .halt R' := by
  obtain ⟨R', hR'⟩ := nip_halt { st with ac := 0 } hc hh
  exact ⟨R', halt_car rfl (dec_halt rfl 1 rfl (halt_car rfl (halt_car rfl (dec_halt rfl 0 rfl
    (halt_car rfl (halt_cdr rfl (skip rfl (Run.decZero 3 _ (by simp [enc]))) hR'))))))⟩

theorem dispatch_ax (st : AS) (hc : Clean st) (c : Nat) :
    Rn (.node 141) { st with ac := c + 3 } (f236 { st with ac := c }) :=
  skip rfl (dec_brk rfl (c + 2) rfl (pass rfl rfl (dec_brk rfl (c + 1) rfl
    (pass rfl rfl (dec_brk rfl c rfl (ax_leaf _ hc))))))

/-! ## One root run is one enumerator step -/

/-- Enumerator states as boundary register files. -/
def toAS (s : EnumDom.St) : AS := ⟨s.np, s.tw, s.ws, 0, s.d, s.h, 0, 0, s.pl⟩

theorem fetch_run (s : EnumDom.St) :
    Rn (.node 133) (toAS s) ⟨(EnumDom.fetch s).2, s.tw, s.ws, 0, s.d, s.h, 0, 0, (EnumDom.fetch s).1⟩ := by
  by_cases h : s.pl = 0
  · have := fetch_zero (toAS s) (by simp [toAS, h]) rfl
    apply rn_eq this
    simp [toAS, EnumDom.fetch, h]
  · obtain ⟨v, hv⟩ : ∃ v, s.pl = v + 1 := ⟨s.pl - 1, by omega⟩
    have := fetch_pos (toAS s) v (by simp [toAS, hv])
    apply rn_eq this
    simp [toAS, EnumDom.fetch, hv]

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

theorem root_step (s : EnumDom.St) :
    match EnumDom.enumStep s with
    | some s' => Rn (.node 0) (toAS s) (toAS s')
    | none => ∃ R', Run dagDom (.node 0) (enc (toAS s)) .halt R' := by
  have hf := fetch_run s
  unfold EnumDom.enumStep EnumDom.execAt
  generalize (EnumDom.fetch s).1 = pl1 at hf ⊢
  generalize (EnumDom.fetch s).2 = np1 at hf ⊢
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
      have h140 := halt_cdr (p := dagDom) (n := 140) rfl h175 hR'
      have h139 := halt_cdr (p := dagDom) (n := 139) rfl h174 h140
      exact ⟨R', halt_cdr (p := dagDom) (n := 0) rfl hf h139⟩
    · simp only [hh, if_false]
      have := hreads (dispatch_nip ⟨np1, s.tw, s.ws, 0, s.d + x, s.h, 0, 0, pl3⟩ (hc _ _ _ _ _ _ _) hh)
      exact rn_eq this (by simp [toAS])
  · -- AX
    have := hreads (dispatch_ax ⟨np1, s.tw, s.ws, 0, s.d + x, s.h, 0, 0, pl3⟩ (hc _ _ _ _ _ _ _) c)
    apply rn_eq this
    simp only [ax_eval, toAS, hy, hp4]

/-! ## Iteration -/

/-- L2: iterating the program root halts iff the enumerator halts. -/
theorem iter_iff (s : EnumDom.St) :
    IterHalts dagDom (enc (toAS s)) ↔ ∃ n s', EnumDom.run n s = some s' ∧ EnumDom.enumStep s' = none :=
  RMDag.iter_halts_iff EnumDom.enumStep EnumDom.run (fun s => enc (toAS s))
    (fun _ => rfl) (fun n s => by cases h : EnumDom.enumStep s <;> simp only [EnumDom.run, h])
    (fun {s s'} h => by have := root_step s; rwa [h] at this)
    (fun {s} h => by have := root_step s; rwa [h] at this) s

end SetTheory.BusyBeaver.ZFC.L2Dom
