import BusyBeaver.ZFC.EnumPerm
import Mathlib.Computability.RE

/-!
# A primitive recursive semidecider for syntactic inconsistency of ZFC

The six-register proof enumerator is the arithmetic source of the verified
215-state machine. Here its *actual* arithmetic operations are shown primitive
recursive. No consistency assumption, machine simulation assumption, or new
axiom enters the bridge to `BProv ZFCax_s [] Form.fBot`.
-/

namespace DiophantineConsistency

open SetTheory SetTheory.BusyBeaver.ZFC
open EnumPerm Code254 KCode222

private def stateEquiv : St ≃ ℕ × ℕ × ℕ × ℕ × ℕ × ℕ where
  toFun s := (s.pl, s.np, s.tw, s.ws, s.d, s.h)
  invFun s := ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1, s.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : Primcodable St := Primcodable.ofEquiv _ stateEquiv
private instance : DecidableEq St := Encodable.decidableEqOfEncodable _

private theorem pr_stateEquiv : Primrec stateEquiv := Primrec.of_equiv (e := stateEquiv)

private theorem pr_pl : Primrec St.pl :=
  (Primrec.fst.comp pr_stateEquiv).of_eq (fun _ => rfl)
private theorem pr_np : Primrec St.np :=
  (Primrec.fst.comp (Primrec.snd.comp pr_stateEquiv)).of_eq (fun _ => rfl)
private theorem pr_tw : Primrec St.tw :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp pr_stateEquiv))).of_eq (fun _ => rfl)
private theorem pr_ws : Primrec St.ws :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp pr_stateEquiv)))).of_eq (fun _ => rfl)
private theorem pr_d : Primrec St.d :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp pr_stateEquiv))))).of_eq (fun _ => rfl)
private theorem pr_h : Primrec St.h :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (Primrec.snd.comp pr_stateEquiv))))).of_eq (fun _ => rfl)

private theorem pr_mk {α : Type} [Primcodable α]
    {a b c d e f : α → ℕ} (ha : Primrec a) (hb : Primrec b)
    (hc : Primrec c) (hd : Primrec d) (he : Primrec e) (hf : Primrec f) :
    Primrec fun x => (⟨a x, b x, c x, d x, e x, f x⟩ : St) :=
  ((Primrec.of_equiv_symm (e := stateEquiv)).comp
    (ha.pair (hb.pair (hc.pair (hd.pair (he.pair hf)))))).of_eq (fun _ => rfl)

private theorem pr_tri : Primrec Cantor.tri := by
  have h := Primrec.nat_rec₁ 0
    ((Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.snd Primrec.fst)
      (Primrec.const 1)).to₂)
  exact h.of_eq (by intro n; induction n <;> simp_all [Cantor.tri])

private theorem pr_P : Primrec₂ P :=
  Primrec.nat_add.comp Primrec.snd
    (pr_tri.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd))

private theorem pr_unP : Primrec unP := by
  have hs : Primrec fun p : ℕ × ℕ =>
      if p.1 = 0 then (p.2 + 1, 0) else (p.1 - 1, p.2 + 1) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
      ((Primrec.nat_add.comp Primrec.snd (Primrec.const 1)).pair (Primrec.const 0))
      ((Primrec.nat_sub.comp Primrec.fst (Primrec.const 1)).pair
        (Primrec.nat_add.comp Primrec.snd (Primrec.const 1)))
  have h := Primrec.nat_rec₁ (0, 0) ((hs.comp Primrec.snd).to₂)
  exact h.of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [ih, unP, Cantor.ofNat]
      cases Cantor.ofNat n with
      | mk a b => cases a <;> simp)

private theorem pr_wim : Primrec₂ wim :=
  Primrec.nat_mul.comp (Primrec.const 4) pr_P
private theorem pr_wel : Primrec₂ wel :=
  Primrec.nat_add.comp pr_wim (Primrec.const 1)
private theorem pr_wal : Primrec₂ wal :=
  Primrec.nat_add.comp pr_wim (Primrec.const 2)
private theorem pr_weq : Primrec₂ weq :=
  Primrec.nat_add.comp pr_wim (Primrec.const 3)

private theorem pr_wn : Primrec wn := pr_wim.comp Primrec.id (Primrec.const F)
private theorem pr_wex : Primrec₂ wex :=
  pr_wn.comp (pr_wal.comp Primrec.fst (pr_wn.comp Primrec.snd))

private theorem pr_rho1 : Primrec fun v : ℕ × ℕ => rho1 v.1 v.2 :=
  pr_wex.comp Primrec.fst (pr_weq.comp Primrec.fst Primrec.snd)
private theorem pr_rho2 : Primrec fun v : ℕ × ℕ × ℕ => rho2 v.1 v.2.1 v.2.2 :=
  pr_wim.comp
    (pr_wal.comp Primrec.fst (pr_wim.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)))
    (pr_wim.comp (pr_wal.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (pr_wal.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))
private theorem pr_rho3 : Primrec fun v : ℕ × ℕ × ℕ => rho3 v.1 v.2.1 v.2.2 :=
  pr_wim.comp (pr_weq.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (pr_wim.comp (pr_wel.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
      (pr_wel.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)))
private theorem pr_rho4 : Primrec fun v : ℕ × ℕ × ℕ => rho4 v.1 v.2.1 v.2.2 :=
  pr_wim.comp
    (pr_wal.comp Primrec.fst (pr_wal.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)))
    (pr_wal.comp (Primrec.fst.comp Primrec.snd)
      (pr_wal.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))
private theorem pr_rho5 : Primrec fun v : ℕ × ℕ × ℕ => rho5 v.1 v.2.1 v.2.2 :=
  pr_wim.comp (pr_weq.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
    (pr_wim.comp (pr_wel.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd))
      (pr_wel.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
private theorem pr_rho6 : Primrec₂ rho6 :=
  pr_wim.comp (pr_wex.comp Primrec.fst (pr_wal.comp Primrec.fst Primrec.snd)) Primrec.snd
private theorem pr_growG : Primrec fun v : ℕ × ℕ × ℕ => growG v.1 v.2.1 v.2.2 :=
  pr_wim.comp (pr_weq.comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
    (pr_wim.comp (pr_weq.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.fst.comp Primrec.snd))
      (pr_wal.comp (pr_wel.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
        (pr_weq.comp Primrec.fst (Primrec.fst.comp Primrec.snd))))

private theorem pr_req {α : Type} [Primcodable α] {b k m : α → ℕ}
    (hb : Primrec b) (hk : Primrec k) (hm : Primrec m) :
    Primrec fun v => req (b v) (k v) (m v) :=
  pr_wal.comp hb (pr_wim.comp hm (pr_wn.comp
    (pr_wal.comp hb (pr_wim.comp hm (pr_wn.comp (pr_wel.comp hb hk))))))

private theorem pr_clos {α : Type} [Primcodable α] {a b k m : α → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hk : Primrec k) (hm : Primrec m) :
    Primrec fun v => clos (a v) (b v) (k v) (m v) :=
  pr_wal.comp hb (pr_wim.comp (pr_wel.comp hb hk) (pr_wn.comp
    (pr_wal.comp ha (pr_wim.comp hm (pr_wn.comp
      (pr_wal.comp ha (pr_wim.comp
        (pr_wal.comp hk (pr_wim.comp (pr_wel.comp hk ha) (pr_wel.comp hk hb)))
        (pr_req hb hk hm))))))))

private theorem pr_gate {α : Type} [Primcodable α] {a b c : α → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec fun v => gate (a v) (b v) (c v) :=
  Primrec.ite ((Primrec.eq.comp hc ha).or (Primrec.eq.comp hc hb)) (Primrec.const 0)
    (pr_wn.comp (pr_wim.comp
      (pr_wim.comp (pr_wel.comp ha hb) (pr_wal.comp hc (pr_wel.comp ha hb)))
      (pr_wal.comp hc (pr_wim.comp (pr_clos ha hb hc hc)
        (pr_wn.comp (pr_req hb hc hc))))))

private theorem pr_rho8 {α : Type} [Primcodable α] {a b c u : α → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) (hu : Primrec u) :
    Primrec fun v => rho8 (a v) (b v) (c v) (u v) :=
  pr_wim.comp (pr_wim.comp (pr_wim.comp hc hu) ha)
    (pr_wim.comp (pr_wim.comp ha hc) (pr_wim.comp hb hc))

private theorem pr_axStack {α : Type} [Primcodable α] {a h b c u t w : α → ℕ}
    (ha : Primrec a) (hh : Primrec h) (hb : Primrec b) (hc : Primrec c)
    (hu : Primrec u) (ht : Primrec t) (hw : Primrec w) :
    Primrec fun v => axStack (a v) (h v) (b v) (c v) (u v) (t v) (w v) :=
  (pr_P.comp (pr_rho1.comp (ha.pair hb))
    (pr_P.comp (pr_rho2.comp (ha.pair (hb.pair hc)))
    (pr_P.comp (pr_rho3.comp (ha.pair (hb.pair hc)))
    (pr_P.comp (pr_rho4.comp (ha.pair (hb.pair hc)))
    (pr_P.comp (pr_rho5.comp (ha.pair (hb.pair hc)))
    (pr_P.comp (pr_rho6.comp ha hc)
    (pr_P.comp (pr_growG.comp (ha.pair (hb.pair hc)))
    (pr_P.comp (pr_rho8 ha hb hc hu)
    (pr_P.comp (pr_wal.comp hu hh) (pr_P.comp ht hw)))))))))).of_eq (fun _ => rfl)

/-- The existing enumerator step, written without an intermediate command datatype. -/
private def rawStep (pl np : ℕ) (s : St) : Option St :=
  let tag := (unP pl).1
  let rest := (unP pl).2
  if tag = 0 then
    if s.h = 1 then none else
      some ⟨rest, np, s.tw, (unP s.ws).2, s.d, (unP s.ws).1⟩
  else if tag = 1 then some ⟨rest, np, s.h, P s.tw s.ws, s.d, s.h⟩
  else if tag = 2 then
    let d := s.d + (unP rest).1
    if wim s.tw d = s.h then some ⟨(unP rest).2, np, d, P 0 s.ws, d, 0⟩
    else some ⟨(unP rest).2, np, 0, s.ws, d, 0⟩
  else
    let c := tag - 3
    let a := s.d + (unP (unP rest).2).1
    let b := s.h + (unP rest).1
    some ⟨(unP (unP rest).2).2, np, gate a b c,
      axStack a s.h b c s.d s.tw s.ws, 0, 0⟩

private theorem rawStep_eq (pl np : ℕ) (s : St) : rawStep pl np s = execAt pl np s := by
  unfold rawStep execAt EnumPerm.decode
  generalize unP pl = p
  rcases p with ⟨tag, rest⟩
  rcases s with ⟨pl0, np0, t, w, d, h⟩
  cases tag with
  | zero => simp [cstep, toW]; split <;> rfl
  | succ tag =>
      cases tag with
      | zero => rfl
      | succ tag =>
          cases tag with
          | zero => simp [cstep, toW]; split <;> rfl
          | succ tag => simp [cstep, toW]

private theorem pr_rawStep {α : Type} [Primcodable α]
    {pl np : α → ℕ} {s : α → St} (hpl : Primrec pl) (hnp : Primrec np)
    (hs : Primrec s) : Primrec fun v => rawStep (pl v) (np v) (s v) := by
  have tag := Primrec.fst.comp (pr_unP.comp hpl)
  have rest := Primrec.snd.comp (pr_unP.comp hpl)
  have t := pr_tw.comp hs
  have w := pr_ws.comp hs
  have d := pr_d.comp hs
  have h := pr_h.comp hs
  have x := Primrec.fst.comp (pr_unP.comp rest)
  have y := Primrec.snd.comp (pr_unP.comp rest)
  have a := Primrec.nat_add.comp d (Primrec.fst.comp (pr_unP.comp y))
  have b := Primrec.nat_add.comp h x
  have c := Primrec.nat_sub.comp tag (Primrec.const 3)
  have d' := Primrec.nat_add.comp d x
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp h (Primrec.const 1)) (Primrec.const none)
      (Primrec.option_some.comp (pr_mk rest hnp t
        (Primrec.snd.comp (pr_unP.comp w)) d (Primrec.fst.comp (pr_unP.comp w)))))
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1))
      (Primrec.option_some.comp (pr_mk rest hnp h (pr_P.comp t w) d h))
      (Primrec.ite (Primrec.eq.comp tag (Primrec.const 2))
        (Primrec.ite (Primrec.eq.comp (pr_wim.comp t d') h)
          (Primrec.option_some.comp (pr_mk y hnp d' (pr_P.comp (Primrec.const 0) w)
            d' (Primrec.const 0)))
          (Primrec.option_some.comp (pr_mk y hnp (Primrec.const 0) w d' (Primrec.const 0))))
        (Primrec.option_some.comp (pr_mk (Primrec.snd.comp (pr_unP.comp y)) hnp
          (pr_gate a b c) (pr_axStack a h b c d t w) (Primrec.const 0) (Primrec.const 0)))))

/-- One step of the literal six-register enumerator is primitive recursive. -/
private theorem pr_enumStep : Primrec enumStep := by
  have cond := Primrec.eq.comp pr_pl (Primrec.const 0)
  have pl := Primrec.ite cond pr_np
    (Primrec.nat_sub.comp pr_pl (Primrec.const 1))
  have np := Primrec.ite cond (Primrec.nat_add.comp pr_np (Primrec.const 1)) pr_np
  exact (pr_rawStep pl np Primrec.id).of_eq (by
    intro s
    simp only [enumStep, fetch]
    split <;> simp_all only [rawStep_eq, id_eq])

/-- Run the proof enumerator for a bounded number of steps; `none` stays `none`. -/
def boundedRun (n : ℕ) (s : St) : Option St :=
  (fun o : Option St => o.bind enumStep)^[n] (some s)

private theorem pr_boundedRun : Primrec₂ boundedRun := by
  exact Primrec.nat_iterate Primrec.fst
    (Primrec.option_some.comp Primrec.snd)
    ((Primrec.option_bind₁ pr_enumStep).comp₂ Primrec₂.right)

private theorem boundedRun_eq (n : ℕ) (s : St) : boundedRun n s = run n s := by
  have hnone : ∀ n, (fun o : Option St => o.bind enumStep)^[n] none = none := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simpa only [Function.iterate_succ_apply, Option.bind_none] using ih
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      simp only [boundedRun, Function.iterate_succ_apply, Option.bind_some]
      cases he : enumStep s with
      | none =>
          simpa only [run, he] using hnone n
      | some s' => simpa only [boundedRun, run, he] using ih s'

private theorem run_succ_right (n : ℕ) (s : St) :
    run (n + 1) s = (run n s).bind enumStep := by
  rw [← boundedRun_eq, boundedRun, Function.iterate_succ_apply']
  change (boundedRun n s).bind enumStep = _
  rw [boundedRun_eq]

/-- The literal initial state shared with the 215-state proof enumerator. -/
def initialState : St := ⟨0, 4, 0, 0, 0, 0⟩

private theorem exists_none_iff (s : St) : (∃ n, boundedRun n s = none) ↔ HaltsFrom s := by
  simp only [boundedRun_eq]
  constructor
  · rintro ⟨n, hn⟩
    induction n generalizing s with
    | zero => cases hn
    | succ n ih =>
        cases he : enumStep s with
        | none => exact ⟨0, s, rfl, he⟩
        | some s' =>
            obtain ⟨k, u, hk, hu⟩ := ih s' (by simpa only [run, he] using hn)
            exact ⟨k + 1, u, by simp only [run, he, hk], hu⟩
  · rintro ⟨n, s', hn, hs'⟩
    exact ⟨n + 1, by rw [run_succ_right, hn, Option.bind_some, hs']⟩

/-- The input is unused: every input is accepted exactly when the falsity code is derivable. -/
def refutationInputs : Set ℕ := fun _ => C222 F

/-- Syntactic inconsistency of ZFC is semidecidable, by the actual verified enumerator. -/
theorem refutationInputs_re : REPred refutationInputs := by
  have ht : Primrec fun v : ℕ × ℕ => decide (boundedRun v.2 initialState = none) :=
    (Primrec.eq.comp
      (pr_boundedRun.comp Primrec.snd (Primrec.const initialState))
      (Primrec.const none)).decide
  have hsearch : Partrec fun _ : ℕ => Nat.rfind
      (fun t => Part.some (decide (boundedRun t initialState = none))) :=
    Partrec.rfind ht.to_comp.partrec
  apply hsearch.dom_re.of_eq
  intro _
  simp only [Nat.rfind_dom, Part.mem_some_iff, true_eq_decide_iff,
    Part.some_dom, implies_true, and_true]
  exact (exists_none_iff initialState).trans
    (EnumPerm.halts_iff rfl ⟨C222.truth, C222.truth, good_zero⟩)

/-- A scalar, executable bounded test for the actual proof enumerator.
Its result is `1` exactly when a refutation has already been found. -/
def haltingTest (t : ℕ) : ℕ :=
  Encodable.encode (decide (boundedRun t initialState = none))

theorem haltingTest_natPrimrec : Nat.Primrec haltingTest := by
  have h : Primrec fun t : ℕ => decide (boundedRun t initialState = none) :=
    (Primrec.eq.comp
      (pr_boundedRun.comp Primrec.id (Primrec.const initialState))
      (Primrec.const none)).decide
  exact Primrec.nat_iff.mp (Primrec.encode_iff.mpr h)

theorem haltingTest_vectorPrimrec :
    Nat.Primrec' (fun v : List.Vector ℕ 1 => haltingTest v.head) :=
  Nat.Primrec'.prim_iff₁.mpr (Primrec.nat_iff.mpr haltingTest_natPrimrec)

theorem haltingTest_eq_one_iff (t : ℕ) :
    haltingTest t = 1 ↔ boundedRun t initialState = none := by
  by_cases h : boundedRun t initialState = none <;> simp [haltingTest, h]

theorem exists_haltingTest_eq_one_iff : (∃ t, haltingTest t = 1) ↔ C222 F := by
  simp only [haltingTest_eq_one_iff]
  exact (exists_none_iff initialState).trans
    (EnumPerm.halts_iff rfl ⟨C222.truth, C222.truth, good_zero⟩)

end DiophantineConsistency
