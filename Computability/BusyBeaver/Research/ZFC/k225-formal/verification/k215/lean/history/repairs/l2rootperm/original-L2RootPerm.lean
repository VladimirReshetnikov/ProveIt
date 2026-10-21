import BusyBeaver.ZFC.L2AxiomsPerm

/-!
L2: one run of the root of the 215's program `dagPerm` is one step of `EnumPerm`.

The root fetches the next command and reads only its selector (node 139 = (read_ac, dispatch)).
The dispatch (node 141) runs NIP at selector 0, DROP at 1, MP at 2 and AX at `3 + c`; MP reads
its own field before its body (node 484 = (read_p1, MP body)), and the AX word reads its two
fields itself (`L2AxiomsPerm.ax_eval`). Adapted from `L2Root222.lean`.
-/

namespace SetTheory.BusyBeaver.ZFC.L2Perm

open RMDag DagPerm Code254
open L2K (AS enc Clean upd_ac)

attribute [local irreducible] Code254.P

/-! ## The dispatch -/

/-- The AX leaf (node 149) runs `axioms()` and breaks out of the dispatch. -/
theorem ax_leaf (st : AS) (hc : Clean st) :
    Run dagPerm (.node 149) (enc st) (.brk 1) (enc (f236 st)) :=
  brk_cdr (p := dagPerm) (n := 149) (k := 0) rfl (l236 st hc) (Run.brkS 0 _)

/-- MP's result on a register file whose parameter already holds `d + x`. -/
def mpOut (st : AS) : AS :=
  if wim st.tw st.p1 = st.p2 then { st with tw := st.p1, ws := P 0 st.ws, p2 := 0 }
  else { st with tw := 0, p2 := 0 }

/-- MP (node 484): read the field into the parameter, then the old MP body. -/
theorem mp484 (st : AS) (hc : Clean st) :
    Rn (.node 484) st
      (mpOut { st with pl := (Cantor.ofNat st.pl).2, p1 := st.p1 + (Cantor.ofNat st.pl).1 }) :=
  seqAS (n := 484) rfl (read_p1 st hc) (mp_branch _ hc)

theorem dispatch_nip (st : AS) (hc : Clean st) (h0 : st.ac = 0) (hh : st.p2 ≠ 1) :
    Rn (.node 141) st { st with p2 := (Cantor.ofNat st.ws).1, ws := (Cantor.ofNat st.ws).2 } :=
  seqAS (n := 141) rfl (skip (p := dagPerm) (n := 142) rfl (Run.decZero 3 _ (by simp [enc, h0])))
    (nip_branch st hc hh)

theorem dispatch_nip_halt (st : AS) (hc : Clean st) (h0 : st.ac = 0) (hh : st.p2 = 1) :
    ∃ R', Run dagPerm (.node 141) (enc st) .halt R' := by
  obtain ⟨R', hR'⟩ := nip_halt st hc hh
  exact ⟨R', halt_cdr (p := dagPerm) (n := 141) rfl
    (skip (p := dagPerm) (n := 142) rfl (Run.decZero 3 _ (by simp [enc, h0]))) hR'⟩

theorem dispatch_drop (st : AS) (hc : Clean st) :
    Rn (.node 141) { st with ac := 1 } { st with ac := 0, tw := st.p2, ws := P st.tw st.ws } := by
  have hdec := Run.decPos (p := dagPerm) 3 (enc { st with ac := 1 }) 0 (by simp [enc])
  rw [upd_ac] at hdec
  let st0 : AS := { { st with ac := 1 } with ac := 0 }
  have h145 : Rn (.node 145) st0 st0 :=
    skip (p := dagPerm) (n := 145) rfl (Run.decZero 3 (enc st0) (by simp [st0, enc]))
  have h144 := seqAS (n := 144) rfl h145 (par2 st0 hc)
  have h143 := brk_cdr (p := dagPerm) (n := 143) (k := 0) rfl h144 (Run.brkS 0 _)
  have h142 := brk_cdr (p := dagPerm) (n := 142) (k := 0) rfl hdec h143
  have := skip (p := dagPerm) (n := 141) rfl h142
  apply rn_eq this
  cases st; rfl

theorem dispatch_mp (st : AS) (hc : Clean st) :
    Rn (.node 141) { st with ac := 2 }
      (mpOut { st with ac := 0, pl := (Cantor.ofNat st.pl).2, p1 := st.p1 + (Cantor.ofNat st.pl).1 }) := by
  have hdec1 := Run.decPos (p := dagPerm) 3 (enc { st with ac := 2 }) 1 (by simp [enc])
  rw [upd_ac] at hdec1
  have hdec2 := Run.decPos (p := dagPerm) 3 (enc { { st with ac := 2 } with ac := 1 }) 0 (by simp [enc])
  rw [upd_ac] at hdec2
  let st0 : AS := { { { st with ac := 2 } with ac := 1 } with ac := 0 }
  have h148 : Rn (.node 148) st0 st0 :=
    skip (p := dagPerm) (n := 148) rfl (Run.decZero 3 (enc st0) (by simp [st0, enc]))
  have h147 := seqAS (n := 147) rfl h148 (mp484 st0 hc)
  have h146 := brk_cdr (p := dagPerm) (n := 146) (k := 0) rfl h147 (Run.brkS 0 _)
  have h145 := brk_cdr (p := dagPerm) (n := 145) (k := 0) rfl hdec2 h146
  have h144 := skip (p := dagPerm) (n := 144) rfl h145
  have h143 := brk_cdr (p := dagPerm) (n := 143) (k := 0) rfl h144 (Run.brkS 0 _)
  have h142 := brk_cdr (p := dagPerm) (n := 142) (k := 0) rfl hdec1 h143
  have := skip (p := dagPerm) (n := 141) rfl h142
  apply rn_eq this
  cases st; rfl

theorem dispatch_ax (st : AS) (hc : Clean st) (c : Nat) :
    Rn (.node 141) { st with ac := c + 3 } (f236 { st with ac := c }) := by
  have hdec1 := Run.decPos (p := dagPerm) 3 (enc { st with ac := c + 3 }) (c + 2) (by simp [enc])
  rw [upd_ac] at hdec1
  have hdec2 := Run.decPos (p := dagPerm) 3 (enc { { st with ac := c + 3 } with ac := c + 2 }) (c + 1)
    (by simp [enc])
  rw [upd_ac] at hdec2
  have hdec3 := Run.decPos (p := dagPerm) 3
    (enc { { { st with ac := c + 3 } with ac := c + 2 } with ac := c + 1 }) c (by simp [enc])
  rw [upd_ac] at hdec3
  have e : ({ { { { st with ac := c + 3 } with ac := c + 2 } with ac := c + 1 } with ac := c } : AS) =
      { st with ac := c } := by cases st; rfl
  rw [e] at hdec3
  have h148 := brk_cdr (p := dagPerm) (n := 148) (k := 0) rfl hdec3 (ax_leaf _ hc)
  have h147 := skip (p := dagPerm) (n := 147) rfl h148
  have h146 := brk_cdr (p := dagPerm) (n := 146) (k := 0) rfl h147 (Run.brkS 0 _)
  have h145 := brk_cdr (p := dagPerm) (n := 145) (k := 0) rfl hdec2 h146
  have h144 := skip (p := dagPerm) (n := 144) rfl h145
  have h143 := brk_cdr (p := dagPerm) (n := 143) (k := 0) rfl h144 (Run.brkS 0 _)
  have h142 := brk_cdr (p := dagPerm) (n := 142) (k := 0) rfl hdec1 h143
  exact skip (p := dagPerm) (n := 141) rfl h142

/-! ## One root run is one enumerator step -/

/-- Enumerator states as boundary register files. -/
def toAS (s : EnumPerm.St) : AS := ⟨s.np, s.tw, s.ws, 0, s.d, s.h, 0, 0, s.pl⟩

theorem fetch_run (s : EnumPerm.St) :
    Rn (.node 133) (toAS s) ⟨(EnumPerm.fetch s).2, s.tw, s.ws, 0, s.d, s.h, 0, 0, (EnumPerm.fetch s).1⟩ := by
  by_cases h : s.pl = 0
  · have := fetch_zero (toAS s) (by simp [toAS, h]) rfl
    apply rn_eq this
    simp [toAS, EnumPerm.fetch, h]
  · obtain ⟨v, hv⟩ : ∃ v, s.pl = v + 1 := ⟨s.pl - 1, by omega⟩
    have := fetch_pos (toAS s) v (by simp [toAS, hv])
    apply rn_eq this
    simp [toAS, EnumPerm.fetch, h, hv]

/-- The selector read after the fetch. -/
theorem read_run (np pl1 tw ws d h : Nat) {X : AS}
    (hd : Rn (.node 141) ⟨np, tw, ws, (Cantor.ofNat pl1).1, d, h, 0, 0, (Cantor.ofNat pl1).2⟩ X) :
    Rn (.node 139) ⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩ X := by
  have h174 := read_ac ⟨np, tw, ws, 0, d, h, 0, 0, pl1⟩ ⟨rfl, rfl⟩
  simp only [Nat.zero_add] at h174
  exact seqAS (n := 139) rfl h174 hd

theorem root_step (s : EnumPerm.St) :
    match EnumPerm.enumStep s with
    | some s' => Rn (.node 0) (toAS s) (toAS s')
    | none => ∃ R', Run dagPerm (.node 0) (enc (toAS s)) .halt R' := by
  have hf := fetch_run s
  unfold EnumPerm.enumStep EnumPerm.execAt
  generalize (EnumPerm.fetch s).1 = pl1 at hf ⊢
  generalize (EnumPerm.fetch s).2 = np1 at hf ⊢
  have hc : ∀ np tw ws ac p1 p2 pl, Clean (⟨np, tw, ws, ac, p1, p2, 0, 0, pl⟩ : AS) := fun _ _ _ _ _ _ _ =>
    ⟨rfl, rfl⟩
  have hread := fun {X : AS} (hd : Rn (.node 141) ⟨np1, s.tw, s.ws, (Cantor.ofNat pl1).1, s.d, s.h, 0, 0,
      (Cantor.ofNat pl1).2⟩ X) =>
    seqAS (n := 0) rfl hf (read_run np1 pl1 s.tw s.ws s.d s.h hd)
  generalize hp2 : (Cantor.ofNat pl1).2 = pl2 at hread ⊢
  generalize hx : (Cantor.ofNat pl2).1 = x at ⊢
  generalize hp3 : (Cantor.ofNat pl2).2 = pl3 at ⊢
  generalize hac : (Cantor.ofNat pl1).1 = ac at hread ⊢
  rcases ac with _ | _ | _ | c
  · -- NIP
    by_cases hh : s.h = 1
    · simp only [hh, if_true]
      obtain ⟨R', hR'⟩ := dispatch_nip_halt ⟨np1, s.tw, s.ws, 0, s.d, s.h, 0, 0, pl2⟩
        (hc _ _ _ _ _ _ _) rfl hh
      have h174 := read_ac ⟨np1, s.tw, s.ws, 0, s.d, s.h, 0, 0, pl1⟩ ⟨rfl, rfl⟩
      simp only [Nat.zero_add, hac, hp2] at h174
      have h139 := halt_cdr (p := dagPerm) (n := 139) rfl h174 hR'
      exact ⟨R', halt_cdr (p := dagPerm) (n := 0) rfl hf h139⟩
    · simp only [hh, if_false]
      have := hread (dispatch_nip ⟨np1, s.tw, s.ws, 0, s.d, s.h, 0, 0, pl2⟩ (hc _ _ _ _ _ _ _) rfl hh)
      exact rn_eq this (by simp [toAS])
  · -- DROP
    have := hread (dispatch_drop ⟨np1, s.tw, s.ws, 0, s.d, s.h, 0, 0, pl2⟩ (hc _ _ _ _ _ _ _))
    exact rn_eq this (by simp [toAS])
  · -- MP
    have := hread (dispatch_mp ⟨np1, s.tw, s.ws, 0, s.d, s.h, 0, 0, pl2⟩ (hc _ _ _ _ _ _ _))
    simp only [hx, hp3] at this
    simp only
    split
    · rename_i hw
      simp only [mpOut, hw, if_true] at this
      exact rn_eq this (by simp [toAS])
    · rename_i hw
      simp only [mpOut, hw, if_false] at this
      exact rn_eq this (by simp [toAS])
  · -- AX
    have := hread (dispatch_ax ⟨np1, s.tw, s.ws, 0, s.d, s.h, 0, 0, pl2⟩ (hc _ _ _ _ _ _ _) c)
    apply rn_eq this
    simp only [ax_eval, toAS, hx, hp3]

/-! ## Iteration -/

theorem root_some {s s' : EnumPerm.St} (h : EnumPerm.enumStep s = some s') :
    Run dagPerm (.node dagPerm.root) (enc (toAS s)) .normal (enc (toAS s')) := by
  have := root_step s
  rw [h] at this
  exact this

theorem root_none {s : EnumPerm.St} (h : EnumPerm.enumStep s = none) :
    ∃ R', Run dagPerm (.node dagPerm.root) (enc (toAS s)) .halt R' := by
  have := root_step s
  rw [h] at this
  exact this

/-- L2: iterating the program root halts iff the enumerator halts. -/
theorem iter_iff (s : EnumPerm.St) :
    IterHalts dagPerm (enc (toAS s)) ↔
      ∃ n s', EnumPerm.run n s = some s' ∧ EnumPerm.enumStep s' = none := by
  constructor
  · intro h
    suffices H : ∀ R, IterHalts dagPerm R → ∀ s, R = enc (toAS s) →
        ∃ n s', EnumPerm.run n s = some s' ∧ EnumPerm.enumStep s' = none from H _ h s rfl
    intro R hR
    induction hR with
    | halt R R' hrun =>
        intro s hs
        subst hs
        match he : EnumPerm.enumStep s with
        | none => exact ⟨0, s, rfl, he⟩
        | some s1 => exact absurd (run_det hrun (root_some he)).1 (by simp)
    | next R R' hrun _ ih =>
        intro s hs
        subst hs
        match he : EnumPerm.enumStep s with
        | none =>
            obtain ⟨R'', h''⟩ := root_none he
            exact absurd (run_det hrun h'').1 (by simp)
        | some s1 =>
            have e := (run_det hrun (root_some he)).2
            obtain ⟨n, s', h1, h2⟩ := ih s1 e
            exact ⟨n + 1, s', by simp only [EnumPerm.run, he]; exact h1, h2⟩
  · rintro ⟨n, s', hrun, hstep⟩
    induction n generalizing s with
    | zero =>
        simp only [EnumPerm.run] at hrun
        cases hrun
        obtain ⟨R', h'⟩ := root_none hstep
        exact IterHalts.halt _ _ h'
    | succ n ih =>
        simp only [EnumPerm.run] at hrun
        split at hrun
        · rename_i s1 he
          exact IterHalts.next _ _ (root_some he) (ih s1 hrun)
        · cases hrun

end SetTheory.BusyBeaver.ZFC.L2Perm
