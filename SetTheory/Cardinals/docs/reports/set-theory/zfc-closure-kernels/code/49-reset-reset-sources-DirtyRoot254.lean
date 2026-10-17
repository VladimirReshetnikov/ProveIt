import BusyBeaver.ZFC.L2Control254
import BusyBeaver.ZFC.EnumSafeStart254

/-!
Attributed port from intake 153, source 35, “Small Turing Machines for the
Consistency of ZFC: Source audit, formal scratch absorption, and certified
transition synthesis” (2026-10-16), supplied under MIT No Attribution.

Arrival: 4e720ccbbfaa836b95be3b2f3f268a737b48c6d1.
Preserved-source placement: 6135ffef4b.
Original ProveIt input: 426592ce97e52d309bfb8f0132411556650b7ac1.
Upstream literal program: jeff87654/busy-beaver,
297ab8df7e5de329605c3875b4934643b371a5e3, ZF/m254/coq/prog/Dag254.v.
Preserved source: SetTheory/Cardinals/docs/reports/set-theory/
zfc-closure-kernels/code/35-dirty-formal-src-BusyBeaver-ZFC-DirtyRoot254.lean.
The published program is attributed to Mira-Cult, Jeff Ketchersid and
Andrew James Wade. The port retains the delivered theorem statements and
proofs; DirtyProgram254 supplies the separate current-tree composition.
-/

/-!
Absorbing arbitrary initial control and scratch registers at the actual root
of the published 219-node register DAG.

Only the two prefix routines are used. The theorem preserves all structured
root outcomes and root halting, without assuming a complete AX simulation.
It is about this literal register program; it is not a blank-tape theorem.
-/

namespace SetTheory.BusyBeaver.ZFC.DirtyRoot254

open RMDag Dag254 Code254 L2

attribute [local irreducible] Code254.P

/-- Exact fetch effect, now without assuming `scratch1 = 0`. -/
def fetched (st : AS) : AS :=
  if st.pl = 0 then
    { st with pl := st.np, np := st.np + st.s1 + 1, s1 := 0 }
  else
    { st with pl := st.pl - 1 }

theorem fetch_any (st : AS) : Rn (.node 133) st (fetched st) := by
  by_cases hpl : st.pl = 0
  · have h134 : Rn (.node 134) st st :=
      skip (p := dag254) (n := 134) rfl
        (Run.decZero 8 (L2.enc st) (by simp [L2.enc, hpl]))
    have h135 := seqAS (n := 135) rfl (loop194 st)
      (seqAS (n := 136) rfl (loop203 _) (inc_AS 0 (by omega) _))
    have h := seqAS (n := 133) rfl h134 h135
    apply rn_eq h
    cases st
    simp_all [fetched, updAS, L2.enc, Nat.add_comm, Nat.add_assoc]
  · have hv : st.pl = (st.pl - 1) + 1 := by omega
    simpa only [fetched, hpl, if_false] using fetch_pos st (st.pl - 1) hv

/-- Nonzero scratch fields advance the unpair walk from their own Cantor code. -/
def readAny (st : AS) : AS :=
  let z := P st.s1 st.s2 + st.pl
  { st with ac := st.ac + (Cantor.ofNat z).1, pl := (Cantor.ofNat z).2, s1 := 0, s2 := 0 }

theorem read_ac_any (st : AS) : Rn (.node 174) st (readAny st) := by
  have h158 := seqAS (n := 158) rfl (loop115 st) (loop209 _)
  have h174 := seqAS (n := 174) rfl h158 (loop201 _)
  apply rn_eq h174
  cases st
  simp [readAny]

def stage (st : AS) : AS := readAny (fetched st)

/-- A clean root configuration with exactly the same continuation after
fetch and the first read. Its proof list is deliberately nonzero. -/
def virtual (st : AS) : AS :=
  let f := fetched st
  let uv := Cantor.ofNat (P f.s1 f.s2 + f.pl)
  { f with ac := 0, s1 := 0, s2 := 0, pl := P (f.ac + uv.1) uv.2 + 1 }

theorem canonical_prefix (st : AS) :
    readAny (fetched
      { st with ac := 0, s1 := 0, s2 := 0, pl := P (st.ac + (Cantor.ofNat (P st.s1 st.s2 + st.pl)).1) (Cantor.ofNat (P st.s1 st.s2 + st.pl)).2 + 1 }) = readAny st := by
  cases st
  simp [fetched, readAny, P_zero_zero, unP_P]

theorem stage_virtual (st : AS) : stage (virtual st) = stage st := by
  exact canonical_prefix (fetched st)

theorem virtual_clean (st : AS) :
    (virtual st).ac = 0 ∧ (virtual st).s1 = 0 ∧ (virtual st).s2 = 0 := by
  exact ⟨rfl, rfl, rfl⟩

theorem virtual_formulas (st : AS) :
    (virtual st).tw = st.tw ∧ (virtual st).ws = st.ws ∧ (virtual st).p2 = st.p2 := by
  unfold virtual fetched
  split <;> exact ⟨rfl, rfl, rfl⟩

def enumOf (st : AS) : Enum254.St :=
  ⟨st.pl, st.np, st.tw, st.ws, st.p1, st.p2⟩

theorem virtual_inv (st : AS) (hs : Enum254.Inv (enumOf st)) :
    Enum254.Inv (enumOf (virtual st)) := by
  obtain ⟨ht, hw, hh⟩ := virtual_formulas st
  simpa only [Enum254.Inv, enumOf, ht, hw, hh] using hs

/-- A generic congruence rule for a node whose first edge terminates normally.
Even continue exits are covered: their restart begins at a common resulting
register file, so it does not retain the original prefix input. -/
theorem node_transfer {p : Prog} {n : Nat} {R S R1 S1 : Regs}
    (ha : Run p (p.nodes n).1 R .normal R1)
    (ha' : Run p (p.nodes n).1 S .normal S1)
    (hb : ∀ x Q, Run p (p.nodes n).2 R1 x Q → Run p (p.nodes n).2 S1 x Q) :
    ∀ {x Q}, Run p (.node n) R x Q → Run p (.node n) S x Q := by
  intro x Q h
  cases h with
  | carBrk1 _ _ _ hc => cases (run_det ha hc).1
  | carBrkS _ _ _ _ hc => cases (run_det ha hc).1
  | carCont _ _ _ _ hc => cases (run_det ha hc).1
  | carHalt _ _ _ hc => cases (run_det ha hc).1
  | cdrNormal _ _ M _ hc hd =>
      have heq := (run_det ha hc).2
      subst M
      exact Run.cdrNormal n S S1 Q ha' (hb _ _ hd)
  | cdrBrk _ k _ M _ hc hd =>
      have heq := (run_det ha hc).2
      subst M
      exact Run.cdrBrk n k S S1 Q ha' (hb _ _ hd)
  | cdrCont1 _ _ M M2 _ y hc hd hr =>
      have heq := (run_det ha hc).2
      subst M
      exact Run.cdrCont1 n S S1 M2 Q _ ha' (hb _ _ hd) hr
  | cdrContS _ k _ M _ hc hd =>
      have heq := (run_det ha hc).2
      subst M
      exact Run.cdrContS n k S S1 Q ha' (hb _ _ hd)
  | cdrHalt _ _ M _ hc hd =>
      have heq := (run_det ha hc).2
      subst M
      exact Run.cdrHalt n S S1 Q ha' (hb _ _ hd)

theorem node_equiv {p : Prog} {n : Nat} {R S R1 S1 : Regs}
    (ha : Run p (p.nodes n).1 R .normal R1)
    (ha' : Run p (p.nodes n).1 S .normal S1)
    (hb : ∀ x Q, Run p (p.nodes n).2 R1 x Q ↔ Run p (p.nodes n).2 S1 x Q) :
    ∀ x Q, Run p (.node n) R x Q ↔ Run p (.node n) S x Q := by
  intro x Q
  exact ⟨node_transfer ha ha' (fun x Q => (hb x Q).mp),
    node_transfer ha' ha (fun x Q => (hb x Q).mpr)⟩

/-- Every structured root outcome is unchanged by the explicit absorption
map, for all nine initial register values. No formula invariant is needed. -/
theorem root_equiv (st : AS) : ∀ x Q,
    Run dag254 (.node 0) (L2.enc st) x Q ↔
      Run dag254 (.node 0) (L2.enc (virtual st)) x Q := by
  have hread := read_ac_any (fetched st)
  have hread' := read_ac_any (fetched (virtual st))
  change Rn (.node 174) (fetched st) (stage st) at hread
  change Rn (.node 174) (fetched (virtual st)) (stage (virtual st)) at hread'
  rw [stage_virtual] at hread'
  have h139 := node_equiv (p := dag254) (n := 139) hread hread'
    (fun _ _ => Iff.rfl)
  exact node_equiv (p := dag254) (n := 0) (fetch_any st) (fetch_any (virtual st)) h139

/-- Absorption preserves repeated-root halting of the literal 219-node DAG. -/
theorem iter_equiv (st : AS) :
    IterHalts dag254 (L2.enc st) ↔ IterHalts dag254 (L2.enc (virtual st)) := by
  constructor
  · intro h
    cases h with
    | halt _ Q hr => exact IterHalts.halt _ Q ((root_equiv st _ Q).mp hr)
    | next _ Q hr hh => exact IterHalts.next _ Q ((root_equiv st _ Q).mp hr) hh
  · intro h
    cases h with
    | halt _ Q hr => exact IterHalts.halt _ Q ((root_equiv st _ Q).mpr hr)
    | next _ Q hr hh => exact IterHalts.next _ Q ((root_equiv st _ Q).mpr hr) hh

/-- The absorbed enumerator state satisfies exact safe-start calibration.
The separate DAG/enumerator bridge is deliberately not a premise hidden
inside this theorem: this conclusion names the abstract enumerator only. -/
theorem virtual_enum_iff (st : AS) (hs : Enum254.Inv (enumOf st)) :
    EnumSafeStart254.HaltsFrom (enumOf (virtual st)) ↔ C254 F :=
  EnumSafeStart254.safe_start_iff _ (virtual_inv st hs)

#print axioms root_equiv
#print axioms iter_equiv
#print axioms virtual_enum_iff

end SetTheory.BusyBeaver.ZFC.DirtyRoot254

