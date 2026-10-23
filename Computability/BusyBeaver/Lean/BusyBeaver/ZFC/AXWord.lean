import BusyBeaver.ZFC.L2Control222

/-!
AX routines as checked words of register macros. The program fixes the successors; the
word names only semantic operations. A literal read is the clean-to-clean pair 158/208.
One induction composes the macro contracts for every program sharing those primitives.
-/

namespace SetTheory.BusyBeaver.ZFC.AXWord

open RMDag Code254 L2

attribute [local irreducible] Code254.P

/-- Push `x`, saving the current formula. -/
def pushA (x : Nat) (st : AS) : AS := { st with tw := x, ws := P st.tw st.ws }

/-- Pop a formula and combine it with the current one. -/
def popA (op : Nat → Nat → Nat) (st : AS) : AS :=
  { st with tw := op (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }

/-- Clear the parameters and discard the bundle if two of them coincide. -/
def gateF (st : AS) : AS :=
  { st with ac := 0, p1 := 0, p2 := 0, tw := if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else st.tw }

/-- The shared physical gate of the 222-family AX routines. -/
theorem gate222 (st : AS) (hc : Clean st) : L2K.Rn (.node 457) st (gateF st) := by
  have := L2K.seqAS (n := 457) rfl (L2K.loop192 st) (L2K.seqAS (n := 458) rfl (L2K.ifeq_clear _)
    (L2K.seqAS (n := 459) rfl (L2K.loop211 _) (L2K.seqAS (n := 460) rfl (L2K.loop197 _) (L2K.ifeq_clear _))))
  apply L2K.rn_eq this
  obtain ⟨h1, h2⟩ := hc
  cases st
  simp only at h1 h2
  subst h1; subst h2
  simp only [gateF, Nat.zero_add]
  split <;> split <;> simp_all <;> omega

inductive AXAtom where
  | par1 | par2 | par3 | push | cons | wel | wal | weq | wn | wa | wex | readp2 | readp1 | readwff

/-- The first primitive of an atom; `readwff` also runs primitive 208. -/
def AXAtom.node : AXAtom → Nat
  | .par1 => 166 | .par2 => 121 | .par3 => 168 | .push => 171 | .cons => 119 | .wel => 181
  | .wal => 180 | .weq => 182 | .wn => 218 | .wa => 178 | .wex => 183 | .readp2 => 176
  | .readp1 => 175 | .readwff => 158

def AXAtom.effect : AXAtom → AS → AS
  | .par1, st => pushA st.p1 st
  | .par2, st => pushA st.p2 st
  | .par3, st => pushA st.ac st
  | .push, st => pushA 0 st
  | .cons, st => popA Code254.wim st
  | .wel, st => popA Code254.wel st
  | .wal, st => popA Code254.wal st
  | .weq, st => popA Code254.weq st
  | .wa, st => popA Code254.wa st
  | .wex, st => popA Code254.wex st
  | .wn, st => { st with tw := Code254.wn st.tw }
  | .readp2, st => { st with pl := (Cantor.ofNat st.pl).2, p2 := st.p2 + (Cantor.ofNat st.pl).1 }
  | .readp1, st => { st with pl := (Cantor.ofNat st.pl).2, p1 := st.p1 + (Cantor.ofNat st.pl).1 }
  | .readwff, st => { st with pl := (Cantor.ofNat st.pl).2, tw := st.tw + (Cantor.ofNat st.pl).1, s1 := 0 }

/-- The ordinary macros have their native contracts; `readwff` is composed below. -/
theorem AXAtom.run (st : AS) (hc : Clean st) :
    ∀ a : AXAtom, a ≠ .readwff → L2.Rn (.node a.node) st (a.effect st)
  | .par1, _ => L2.par1 st hc
  | .par2, _ => L2.par2 st hc
  | .par3, _ => L2.par3 st hc
  | .push, _ => L2.pushwff st hc
  | .cons, _ => L2.cons st hc
  | .wel, _ => L2.wel_m st hc
  | .wal, _ => L2.wal_m st hc
  | .weq, _ => L2.weq_m st hc
  | .wn, _ => L2.wn_m st hc
  | .wa, _ => L2.wa_m st hc
  | .wex, _ => L2.wex_m st hc
  | .readp2, _ => L2.read_p2 st hc
  | .readp1, _ => L2.read_p1 st hc
  | .readwff, h => False.elim (h rfl)

/-- The 148-atom tail common to the three parameter-reading variants. -/
def axBody : List AXAtom := [
  .par1, .cons, .par1, .par3, .cons, .par2, .par3, .cons, .cons, .cons, .par3, .par1,
  .weq, .par3, .par2, .weq, .par1, .par2, .wel, .par1, .par2, .weq, .wal, .cons,
  .cons, .par1, .par1, .par3, .wal, .wex, .par3, .cons, .par3, .par1, .weq, .par3,
  .par2, .wel, .par1, .par2, .wel, .cons, .cons, .par1, .par2, .par3, .wal, .wal,
  .par2, .par1, .par3, .wal, .wal, .cons, .par1, .par2, .weq, .par3, .par1, .wel,
  .par3, .par2, .wel, .cons, .cons, .par1, .par2, .par3, .cons, .wal, .par1, .par2,
  .wal, .par1, .par3, .wal, .cons, .cons, .par1, .par1, .par2, .weq, .wex, .par1,
  .par2, .wel, .par3, .par1, .par2, .wel, .wal, .cons, .par3, .par2, .par2, .par3,
  .wel, .par1, .par3, .par1, .par3, .par3, .par1, .wel, .par3, .par2, .wel, .cons,
  .wal, .par2, .par3, .par2, .par3, .par2, .par3, .wel, .wn, .cons, .wal, .wn,
  .cons, .wal, .cons, .wal, .wn, .cons, .wal, .wn, .cons, .wal, .par2, .par3,
  .par2, .par3, .par2, .par3, .wel, .wn, .cons, .wal, .wn, .cons, .wal, .wn,
  .cons, .wal, .cons, .wn]

/-- Every complete macro returns clean scratch registers. -/
theorem AXAtom.clean (a : AXAtom) (st : AS) (hc : Clean st) : Clean (a.effect st) := by
  cases a <;> first | exact hc | exact ⟨rfl, hc.2⟩

/-- Follow a single car macro, rejecting every other program shape. -/
def chainNext (p : Prog) (n m : Nat) : Option Nat :=
  match p.nodes n with
  | (.node m', .node next) => if m' = m then some next else none
  | _ => none

/-- A literal read consumes two program nodes; every other macro consumes one. -/
def AXAtom.next (p : Prog) : AXAtom → Nat → Option Nat
  | .readwff, n => (chainNext p n 158).bind (fun middle => chainNext p middle 208)
  | a, n => chainNext p n a.node

private theorem chainNext_run {p : Prog} {n m next : Nat} {R R1 R2 : Regs}
    (hn : chainNext p n m = some next) (hm : Run p (.node m) R .normal R1)
    (hr : Run p (.node next) R1 .normal R2) : Run p (.node n) R .normal R2 := by
  unfold chainNext at hn
  split at hn
  · rename_i m' next' he
    split at hn
    · rename_i h
      have hn' : next' = next := Option.some.inj hn
      subst m'; subst next'
      exact seq he hm hr
    · contradiction
  · contradiction

section

variable {p : Prog}
  (transfer : ∀ (a : AXAtom) {R R' : Regs},
    Run Dag254.dag254 (.node a.node) R .normal R' → Run p (.node a.node) R .normal R')
  (move : ∀ st : AS, Run p (.node 208) (enc st) .normal
    (enc { st with tw := st.tw + st.s1, s1 := 0 }))

include transfer move in
private theorem AXAtom.prefix (a : AXAtom) {n next : Nat}
    (hn : a.next p n = some next) (st : AS) (hc : Clean st) {R' : Regs}
    (hr : Run p (.node next) (enc (a.effect st)) .normal R') :
    Run p (.node n) (enc st) .normal R' := by
  by_cases ha : a = .readwff
  · subst a
    simp only [AXAtom.next] at hn
    cases hs : chainNext p n 158 with
    | none => simp only [hs, Option.bind_none, reduceCtorEq] at hn
    | some middle =>
      have hm : chainNext p middle 208 = some next := by
        simpa only [hs, Option.bind_some] using hn
      exact chainNext_run hs (transfer .readwff (L2.read108 st hc))
        (chainNext_run hm (move _) hr)
  · have hn' : chainNext p n a.node = some next := by
      cases a <;> first | contradiction | exact hn
    exact chainNext_run hn' (transfer a (AXAtom.run st hc a ha)) hr

/-- The literal program supplies successors; the certificate names only semantic macros. -/
def axWordCheck (p : Prog) (gate : Nat) : Nat → List AXAtom → Bool
  | n, [] => decide (n = gate)
  | n, a :: rest =>
    match a.next p n with
    | none => false
    | some next => axWordCheck p gate next rest

def axWordEval : List AXAtom → AS → AS
  | [], st => gateF st
  | a :: rest, st => axWordEval rest (a.effect st)

theorem axWordClean (word : List AXAtom) (st : AS) (hc : Clean st) :
    Clean (axWordEval word st) := by
  induction word generalizing st with
  | nil => exact hc
  | cons a rest ih => exact ih _ (a.clean st hc)

include transfer move in
theorem axWordRun {gate : Nat}
    (gateRun : ∀ st : AS, Clean st → Run p (.node gate) (enc st) .normal (enc (gateF st)))
    (word : List AXAtom) {n : Nat} (h : axWordCheck p gate n word = true)
    (st : AS) (hc : Clean st) : Run p (.node n) (enc st) .normal (enc (axWordEval word st)) := by
  induction word generalizing n st with
  | nil =>
    simp only [axWordCheck, decide_eq_true_eq] at h
    subst n
    exact gateRun st hc
  | cons a rest ih =>
    cases hn : a.next p n with
    | none => simp only [axWordCheck, hn, Bool.false_eq_true] at h
    | some next =>
      exact a.prefix transfer move hn st hc
        (ih (by simpa only [axWordCheck, hn] using h) _ (a.clean st hc))

end
end SetTheory.BusyBeaver.ZFC.AXWord
