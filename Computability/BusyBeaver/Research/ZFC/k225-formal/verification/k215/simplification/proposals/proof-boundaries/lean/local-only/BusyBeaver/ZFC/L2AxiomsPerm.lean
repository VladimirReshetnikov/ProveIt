import BusyBeaver.ZFC.L2Perm
import BusyBeaver.ZFC.EnumPerm

/-!
The AX routine of `dagPerm` (node 236) as a checked word of register macros.

Each atom is a macro node whose run contract `L2Perm` transfers from `dag222`. One induction
composes the contracts along the word, a kernel check binds the word to the literal program,
and symbolic evaluation identifies its complete effect with EnumPerm's AX step (`ax_eval`).
-/

namespace SetTheory.BusyBeaver.ZFC.L2Perm

open RMDag DagPerm Code254 KCode222
open L2K (AS enc Clean ofNat_P)

attribute [local irreducible] Code254.P

set_option maxRecDepth 4096

/-- Push `x`, saving the current formula. -/
def pushA (x : Nat) (st : AS) : AS := { st with tw := x, ws := P st.tw st.ws }

/-- Pop a formula and combine it with the current one. -/
def popA (op : Nat → Nat → Nat) (st : AS) : AS :=
  { st with tw := op (Cantor.ofNat st.ws).1 st.tw, ws := (Cantor.ofNat st.ws).2 }

/-- The gate: clear the bundle when `c = b` or `c = a`, and clear `axiomcode`, `param1`,
`param2`. -/
def gateF (st : AS) : AS :=
  { st with ac := 0, p1 := 0, p2 := 0, tw := if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else st.tw }

theorem l457 (st : AS) (hc : Clean st) : Rn (.node 457) st (gateF st) := by
  have := seqAS (n := 457) rfl (loop192 st) (seqAS (n := 458) rfl (ifeq_clear _)
    (seqAS (n := 459) rfl (loop211 _) (seqAS (n := 460) rfl (loop197 _) (ifeq_clear _))))
  apply rn_eq this
  obtain ⟨h1, h2⟩ := hc
  cases st
  simp only at h1 h2
  subst h1; subst h2
  simp only [gateF, Nat.zero_add]
  split <;> split <;> simp_all <;> omega

/-- The register macros of the AX word. -/
inductive AXAtom where
  | par1 | par2 | par3 | push | cons | wel | wal | weq | wn | wa | wex | readp2 | readp1

def AXAtom.node : AXAtom → Nat
  | .par1 => 166 | .par2 => 121 | .par3 => 168 | .push => 171 | .cons => 119 | .wel => 181
  | .wal => 180 | .weq => 182 | .wn => 218 | .wa => 178 | .wex => 183 | .readp2 => 176
  | .readp1 => 175

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

theorem AXAtom.run (st : AS) (hc : Clean st) : ∀ a : AXAtom, Rn (.node a.node) st (a.effect st)
  | .par1 => L2Perm.par1 st hc
  | .par2 => L2Perm.par2 st hc
  | .par3 => L2Perm.par3 st hc
  | .push => L2Perm.pushwff st hc
  | .cons => L2Perm.cons st hc
  | .wel => L2Perm.wel_m st hc
  | .wal => L2Perm.wal_m st hc
  | .weq => L2Perm.weq_m st hc
  | .wn => L2Perm.wn_m st hc
  | .wa => L2Perm.wa_m st hc
  | .wex => L2Perm.wex_m st hc
  | .readp2 => L2Perm.read_p2 st hc
  | .readp1 => L2Perm.read_p1 st hc

/-- The literal program supplies successors; the certificate names only semantic macros. -/
def axWordCheck : Nat → List AXAtom → Bool
  | n, [] => decide (n = 457)
  | n, a :: rest =>
    match dagPerm.nodes n with
    | (.node m, .node next) => decide (m = a.node) && axWordCheck next rest
    | _ => false

def axWordEval : List AXAtom → AS → AS
  | [], st => gateF st
  | a :: rest, st => axWordEval rest (a.effect st)

/-- No macro touches the scratch registers. -/
theorem axWordClean (word : List AXAtom) (st : AS) (hc : Clean st) :
    Clean (axWordEval word st) := by
  induction word generalizing st with
  | nil => exact hc
  | cons a rest ih => exact ih _ (by cases a <;> exact hc)

theorem axWordRun (word : List AXAtom) {n : Nat}
    (h : axWordCheck n word = true) (st : AS) (hc : Clean st) :
    Rn (.node n) st (axWordEval word st) := by
  induction word generalizing n st with
  | nil =>
    simp only [axWordCheck, decide_eq_true_eq] at h
    subst n
    exact l457 st hc
  | cons a rest ih =>
    simp only [axWordCheck] at h
    split at h
    · rename_i m next hn
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hm, hr⟩
      subst m
      exact seq hn (AXAtom.run st hc a) (ih hr _ (by cases a <;> exact hc))
    · contradiction

def axWord : List AXAtom := [
  .par1, .par2, .wal, .par3, .par1, .readp2, .cons, .readp1, .par1, .cons, .par1, .par3,
  .cons, .par2, .par3, .cons, .cons, .cons, .par3, .par1, .weq, .par3, .par2, .weq,
  .par1, .par2, .wel, .par1, .par2, .weq, .wal, .cons, .cons, .par1, .par1, .par3,
  .wal, .wex, .par3, .cons, .par3, .par1, .weq, .par3, .par2, .wel, .par1, .par2,
  .wel, .cons, .cons, .par1, .par2, .par3, .wal, .wal, .par2, .par1, .par3, .wal,
  .wal, .cons, .par1, .par2, .weq, .par3, .par1, .wel, .par3, .par2, .wel, .cons,
  .cons, .par1, .par2, .par3, .cons, .wal, .par1, .par2, .wal, .par1, .par3, .wal,
  .cons, .cons, .par1, .par1, .par2, .weq, .wex, .par1, .par2, .wel, .par3, .par1,
  .par2, .wel, .wal, .cons, .par3, .par2, .par2, .par3, .wel, .par1, .par3, .par1,
  .par3, .par3, .par1, .wel, .par3, .par2, .wel, .cons, .wal, .par2, .par3, .par2,
  .par3, .par2, .par3, .wel, .wn, .cons, .wal, .wn, .cons, .wal, .cons, .wal,
  .wn, .cons, .wal, .wn, .cons, .wal, .par2, .par3, .par2, .par3, .par2, .par3,
  .wel, .wn, .cons, .wal, .wn, .cons, .wal, .wn, .cons, .wal, .cons, .wn]

theorem axWord_checked : axWordCheck 236 axWord = true := by decide +kernel

def f236 (st : AS) : AS := axWordEval axWord st
theorem l236 (st : AS) (hc : Clean st) : Rn (.node 236) st (f236 st) :=
  axWordRun axWord axWord_checked st hc
theorem c236 (st : AS) (hc : Clean st) : Clean (f236 st) := axWordClean axWord st hc

/-- **The AX routine is EnumPerm's AX step.** -/
theorem ax_eval (np t S c a h pl : Nat) :
    f236 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, EnumPerm.gate (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) (h + (Cantor.ofNat pl).1) c,
        EnumPerm.axStack (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) h (h + (Cantor.ofNat pl).1) c a
          t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := by
  simp only [f236, axWord, axWordEval, AXAtom.effect, pushA, popA, gateF, ofNat_P,
    EnumPerm.gate, EnumPerm.axStack, bundle222, nks, clos, req, vrel, growG,
    rho1, rho2, rho3, rho4, rho5, rho6, rho8, wex]

#print axioms l236
#print axioms ax_eval
end SetTheory.BusyBeaver.ZFC.L2Perm
