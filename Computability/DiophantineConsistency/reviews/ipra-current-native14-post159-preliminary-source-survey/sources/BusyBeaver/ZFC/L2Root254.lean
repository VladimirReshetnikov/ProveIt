import BusyBeaver.ZFC.L2AxiomsEval254

/-!
L2: one run of the root of the 219-node program is one enumerator step.

`ax_eval` evaluates the generated `axioms()` composite symbolically: the
stack becomes `Enum254.axStack` and the current formula the gated bundle.
-/

namespace SetTheory.BusyBeaver.ZFC.L2

open RMDag Dag254 Code254

attribute [local irreducible] Code254.P

theorem ax_eval (np t S c a h pl : Nat) :
    f1 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, Enum254.gate a (h + (Cantor.ofNat pl).1) c,
        Enum254.axStack a h (h + (Cantor.ofNat pl).1) c (Cantor.ofNat (Cantor.ofNat pl).2).1 t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := by
  rw [e1]
  simp only [Enum254.gate, Enum254.axStack, bundle, bundleC, bundleG, rho1, rho2, rho3, rho4, rho5,
    rho6, rho7, rho8]

/-! ## The dispatch -/

/-- The AX leaf (node 149) runs `axioms()` and breaks out of the dispatch. -/
theorem ax_leaf (st : AS) (hc : Clean st) :
    Run dag254 (.node 149) (enc st) (.brk 1) (enc (f1 st)) :=
  brk_cdr (p := dag254) (n := 149) (k := 0) rfl (l1 st hc) (Run.brkS 0 _)

theorem dispatch_mp (st : AS) (hc : Clean st) (h0 : st.ac = 0) :
    Rn (.node 141) st (if wim st.tw st.p1 = st.p2
      then { st with tw := st.p1, ws := P 0 st.ws, p2 := 0 } else { st with tw := 0, p2 := 0 }) :=
  seqAS (n := 141) rfl (skip (p := dag254) (n := 142) rfl (Run.decZero 3 _ (by simp [enc, h0])))
    (mp_branch st hc)

theorem dispatch_drop (st : AS) (hc : Clean st) :
    Rn (.node 141) { st with ac := 1 } { st with ac := 0, tw := st.p2, ws := P st.tw st.ws } := by
  have hdec := Run.decPos (p := dag254) 3 (enc { st with ac := 1 }) 0 (by simp [enc])
  rw [upd_ac] at hdec
  let st0 : AS := { { st with ac := 1 } with ac := 0 }
  have h145 : Rn (.node 145) st0 st0 :=
    skip (p := dag254) (n := 145) rfl (Run.decZero 3 (enc st0) (by simp [st0, enc]))
  have h144 := seqAS (n := 144) rfl h145 (par2 st0 hc)
  have h143 := brk_cdr (p := dag254) (n := 143) (k := 0) rfl h144 (Run.brkS 0 _)
  have h142 := brk_cdr (p := dag254) (n := 142) (k := 0) rfl hdec h143
  have := skip (p := dag254) (n := 141) rfl h142
  apply rn_eq this
  cases st; rfl

theorem dispatch_nip (st : AS) (hc : Clean st) (hh : st.p2 ≠ 1) :
    Rn (.node 141) { st with ac := 2 }
      { st with ac := 0, p2 := (Cantor.ofNat st.ws).1, ws := (Cantor.ofNat st.ws).2 } := by
  have hdec1 := Run.decPos (p := dag254) 3 (enc { st with ac := 2 }) 1 (by simp [enc])
  rw [upd_ac] at hdec1
  have hdec2 := Run.decPos (p := dag254) 3 (enc { { st with ac := 2 } with ac := 1 }) 0 (by simp [enc])
  rw [upd_ac] at hdec2
  let st0 : AS := { { { st with ac := 2 } with ac := 1 } with ac := 0 }
  have h148 : Rn (.node 148) st0 st0 :=
    skip (p := dag254) (n := 148) rfl (Run.decZero 3 (enc st0) (by simp [st0, enc]))
  have h147 := seqAS (n := 147) rfl h148 (nip_branch st0 hc hh)
  have h146 := brk_cdr (p := dag254) (n := 146) (k := 0) rfl h147 (Run.brkS 0 _)
  have h145 := brk_cdr (p := dag254) (n := 145) (k := 0) rfl hdec2 h146
  have h144 := skip (p := dag254) (n := 144) rfl h145
  have h143 := brk_cdr (p := dag254) (n := 143) (k := 0) rfl h144 (Run.brkS 0 _)
  have h142 := brk_cdr (p := dag254) (n := 142) (k := 0) rfl hdec1 h143
  have := skip (p := dag254) (n := 141) rfl h142
  apply rn_eq this
  cases st; rfl

theorem dispatch_nip_halt (st : AS) (hc : Clean st) (hh : st.p2 = 1) :
    ∃ R', Run dag254 (.node 141) (enc { st with ac := 2 }) .halt R' := by
  have hdec1 := Run.decPos (p := dag254) 3 (enc { st with ac := 2 }) 1 (by simp [enc])
  rw [upd_ac] at hdec1
  have hdec2 := Run.decPos (p := dag254) 3 (enc { { st with ac := 2 } with ac := 1 }) 0 (by simp [enc])
  rw [upd_ac] at hdec2
  let st0 : AS := { { { st with ac := 2 } with ac := 1 } with ac := 0 }
  obtain ⟨R', hR'⟩ := nip_halt st0 hc hh
  have h148 : Rn (.node 148) st0 st0 :=
    skip (p := dag254) (n := 148) rfl (Run.decZero 3 (enc st0) (by simp [st0, enc]))
  have h147 := halt_cdr (p := dag254) (n := 147) rfl h148 hR'
  have h146 := halt_car (p := dag254) (n := 146) rfl h147
  have h145 := halt_cdr (p := dag254) (n := 145) rfl hdec2 h146
  have h144 := halt_car (p := dag254) (n := 144) rfl h145
  have h143 := halt_car (p := dag254) (n := 143) rfl h144
  have h142 := halt_cdr (p := dag254) (n := 142) rfl hdec1 h143
  exact ⟨R', halt_car (p := dag254) (n := 141) rfl h142⟩

theorem dispatch_ax (st : AS) (hc : Clean st) (c : Nat) :
    Rn (.node 141) { st with ac := c + 3 } (f1 { st with ac := c }) := by
  have hdec1 := Run.decPos (p := dag254) 3 (enc { st with ac := c + 3 }) (c + 2) (by simp [enc])
  rw [upd_ac] at hdec1
  have hdec2 := Run.decPos (p := dag254) 3 (enc { { st with ac := c + 3 } with ac := c + 2 }) (c + 1)
    (by simp [enc])
  rw [upd_ac] at hdec2
  have hdec3 := Run.decPos (p := dag254) 3
    (enc { { { st with ac := c + 3 } with ac := c + 2 } with ac := c + 1 }) c (by simp [enc])
  rw [upd_ac] at hdec3
  have e : ({ { { { st with ac := c + 3 } with ac := c + 2 } with ac := c + 1 } with ac := c } : AS) =
      { st with ac := c } := by cases st; rfl
  rw [e] at hdec3
  have h148 := brk_cdr (p := dag254) (n := 148) (k := 0) rfl hdec3 (ax_leaf _ hc)
  have h147 := skip (p := dag254) (n := 147) rfl h148
  have h146 := brk_cdr (p := dag254) (n := 146) (k := 0) rfl h147 (Run.brkS 0 _)
  have h145 := brk_cdr (p := dag254) (n := 145) (k := 0) rfl hdec2 h146
  have h144 := skip (p := dag254) (n := 144) rfl h145
  have h143 := brk_cdr (p := dag254) (n := 143) (k := 0) rfl h144 (Run.brkS 0 _)
  have h142 := brk_cdr (p := dag254) (n := 142) (k := 0) rfl hdec1 h143
  exact skip (p := dag254) (n := 141) rfl h142

/-! ## One root run is one enumerator step -/

/-- Enumerator states as boundary register files. -/
def toAS (s : Enum254.St) : AS := ⟨s.np, s.tw, s.ws, 0, s.d, s.h, 0, 0, s.pl⟩

theorem fetch_run (s : Enum254.St) :
    Rn (.node 133) (toAS s) ⟨(Enum254.fetch s).2, s.tw, s.ws, 0, s.d, s.h, 0, 0, (Enum254.fetch s).1⟩ := by
  by_cases h : s.pl = 0
  · have := fetch_zero (toAS s) (by simp [toAS, h]) rfl
    apply rn_eq this
    simp [toAS, Enum254.fetch, h]
  · obtain ⟨v, hv⟩ : ∃ v, s.pl = v + 1 := ⟨s.pl - 1, by omega⟩
    have := fetch_pos (toAS s) v (by simp [toAS, hv])
    apply rn_eq this
    simp [toAS, Enum254.fetch, h, hv]

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

theorem root_step (s : Enum254.St) :
    match Enum254.enumStep s with
    | some s' => Rn (.node 0) (toAS s) (toAS s')
    | none => ∃ R', Run dag254 (.node 0) (enc (toAS s)) .halt R' := by
  have hf := fetch_run s
  unfold Enum254.enumStep Enum254.execAt
  generalize (Enum254.fetch s).1 = pl1 at hf ⊢
  generalize (Enum254.fetch s).2 = np1 at hf ⊢
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
      have h140 := halt_cdr (p := dag254) (n := 140) rfl h175 hR'
      have h139 := halt_cdr (p := dag254) (n := 139) rfl h174 h140
      exact ⟨R', halt_cdr (p := dag254) (n := 0) rfl hf h139⟩
    · simp only [hh, if_false]
      have := hreads (dispatch_nip ⟨np1, s.tw, s.ws, 0, s.d + x, s.h, 0, 0, pl3⟩ (hc _ _ _ _ _ _ _) hh)
      exact rn_eq this (by simp [toAS])
  · -- AX
    have := hreads (dispatch_ax ⟨np1, s.tw, s.ws, 0, s.d + x, s.h, 0, 0, pl3⟩ (hc _ _ _ _ _ _ _) c)
    apply rn_eq this
    simp only [ax_eval, toAS, hy, hp4]

/-! ## Iteration -/

theorem root_some {s s' : Enum254.St} (h : Enum254.enumStep s = some s') :
    Run dag254 (.node dag254.root) (enc (toAS s)) .normal (enc (toAS s')) := by
  have := root_step s
  rw [h] at this
  exact this

theorem root_none {s : Enum254.St} (h : Enum254.enumStep s = none) :
    ∃ R', Run dag254 (.node dag254.root) (enc (toAS s)) .halt R' := by
  have := root_step s
  rw [h] at this
  exact this

/-- L2: iterating the program root halts iff the enumerator halts. -/
theorem iter_iff (s : Enum254.St) :
    IterHalts dag254 (enc (toAS s)) ↔ ∃ n s', Enum254.run n s = some s' ∧ Enum254.enumStep s' = none := by
  constructor
  · intro h
    suffices H : ∀ R, IterHalts dag254 R → ∀ s, R = enc (toAS s) →
        ∃ n s', Enum254.run n s = some s' ∧ Enum254.enumStep s' = none from H _ h s rfl
    intro R hR
    induction hR with
    | halt R R' hrun =>
        intro s hs
        subst hs
        match he : Enum254.enumStep s with
        | none => exact ⟨0, s, rfl, he⟩
        | some s1 => exact absurd (run_det hrun (root_some he)).1 (by simp)
    | next R R' hrun _ ih =>
        intro s hs
        subst hs
        match he : Enum254.enumStep s with
        | none =>
            obtain ⟨R'', h''⟩ := root_none he
            exact absurd (run_det hrun h'').1 (by simp)
        | some s1 =>
            have e := (run_det hrun (root_some he)).2
            obtain ⟨n, s', h1, h2⟩ := ih s1 e
            exact ⟨n + 1, s', by simp only [Enum254.run, he]; exact h1, h2⟩
  · rintro ⟨n, s', hrun, hstep⟩
    induction n generalizing s with
    | zero =>
        simp only [Enum254.run] at hrun
        cases hrun
        obtain ⟨R', h'⟩ := root_none hstep
        exact IterHalts.halt _ _ h'
    | succ n ih =>
        simp only [Enum254.run] at hrun
        split at hrun
        · rename_i s1 he
          exact IterHalts.next _ _ (root_some he) (ih s1 hrun)
        · cases hrun

/-- The enumerator's own halting predicate, from the zero state. -/
theorem iter_iff_halts : IterHalts dag254 (enc (toAS Enum254.s0)) ↔ Enum254.Halts := iter_iff _

/-- The first two candidates (MP on truth, then DROP) lead to `nextproof = 2`
with every other register zero: the state reached by the machine's boot. -/
def s2 : Enum254.St := ⟨0, 2, 0, 0, 0, 0⟩

theorem run_s0_s2 : Enum254.run 2 Enum254.s0 = some s2 := by
  have h0 : wim 0 0 = 0 := by simp [wim, P_zero_zero]
  have hP : P 0 0 = 0 := P_zero_zero
  have e1 : Enum254.enumStep Enum254.s0 = some ⟨0, 1, 0, 0, 0, 0⟩ := by
    simp [Enum254.enumStep, Enum254.execAt, Enum254.fetch, Enum254.s0, h0, hP, Cantor.ofNat]
  have e2 : Enum254.enumStep ⟨0, 1, 0, 0, 0, 0⟩ = some s2 := by
    simp [Enum254.enumStep, Enum254.execAt, Enum254.fetch, s2, hP, Cantor.ofNat]
  simp [Enum254.run, e1, e2]

/-- L2 from the boot register file `nextproof = 2`, all other registers zero. -/
theorem iter_halts_boot : IterHalts dag254 (enc (toAS s2)) ↔ Enum254.Halts := by
  rw [iter_iff]
  constructor
  · rintro ⟨n, s', h1, h2⟩
    exact ⟨2 + n, s', by rw [Enum254.run_add 2 n _ _ run_s0_s2]; exact h1, h2⟩
  · rintro ⟨n, s', h1, h2⟩
    have hs0 : Enum254.enumStep Enum254.s0 = some ⟨0, 1, 0, 0, 0, 0⟩ := by
      simp [Enum254.enumStep, Enum254.execAt, Enum254.fetch, Enum254.s0, wim, P_zero_zero, Cantor.ofNat]
    have hs1 : Enum254.enumStep ⟨0, 1, 0, 0, 0, 0⟩ = some s2 := by
      simp [Enum254.enumStep, Enum254.execAt, Enum254.fetch, s2, P_zero_zero, Cantor.ofNat]
    match n, h1 with
    | 0, h1 => simp [Enum254.run] at h1; subst h1; rw [hs0] at h2; cases h2
    | 1, h1 => simp [Enum254.run, hs0] at h1; subst h1; rw [hs1] at h2; cases h2
    | n + 2, h1 =>
        refine ⟨n, s', ?_, h2⟩
        simpa [Enum254.run, hs0, hs1] using h1

theorem enc_s2 : enc (toAS s2) = upd (fun _ => 0) 0 2 := by
  funext i
  rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;> simp [enc, toAS, s2, upd]

/-- L2 composed with L1: the 219-node program, iterated from the boot registers
(`nextproof = 2`), halts iff the falsity code is derivable in the code calculus. -/
theorem program_halts_iff : IterHalts dag254 (upd (fun _ => 0) 0 2) ↔ C254 F := by
  rw [← enc_s2, iter_halts_boot, Enum254.enum_halts_iff]

end SetTheory.BusyBeaver.ZFC.L2
