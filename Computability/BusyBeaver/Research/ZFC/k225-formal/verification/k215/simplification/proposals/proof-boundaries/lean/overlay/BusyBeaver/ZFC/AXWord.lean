import BusyBeaver.ZFC.L2Control222
import BusyBeaver.ZFC.KCode222

/-! Shared checked AX words for the dominated and permuted programs.
The two words differ by a commuting readp1/cons pair and literal program addresses.
All macro contracts are proved once for dag222 and supplied to axWordRun by transfer. -/

namespace SetTheory.BusyBeaver.ZFC.AXWord
open RMDag Code254 KCode222 L2K
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
  | .par1 => L2K.par1 st hc
  | .par2 => L2K.par2 st hc
  | .par3 => L2K.par3 st hc
  | .push => L2K.pushwff st hc
  | .cons => L2K.cons st hc
  | .wel => L2K.wel_m st hc
  | .wal => L2K.wal_m st hc
  | .weq => L2K.weq_m st hc
  | .wn => L2K.wn_m st hc
  | .wa => L2K.wa_m st hc
  | .wex => L2K.wex_m st hc
  | .readp2 => L2K.read_p2 st hc
  | .readp1 => L2K.read_p1 st hc

/-- The literal program supplies successors; the certificate names only semantic macros. -/
def axWordCheck (p : Prog) : Nat → List AXAtom → Bool
  | n, [] => decide (n = 457)
  | n, a :: rest =>
    match p.nodes n with
    | (.node m, .node next) => decide (m = a.node) && axWordCheck p next rest
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

theorem axWordRun {p : Prog}
    (atomRun : ∀ st, Clean st → ∀ a : AXAtom,
      Run p (.node a.node) (enc st) .normal (enc (a.effect st)))
    (gateRun : ∀ st, Clean st → Run p (.node 457) (enc st) .normal (enc (gateF st)))
    (word : List AXAtom) {n : Nat}
    (h : axWordCheck p n word = true) (st : AS) (hc : Clean st) :
    Run p (.node n) (enc st) .normal (enc (axWordEval word st)) := by
  induction word generalizing n st with
  | nil =>
    simp only [axWordCheck, decide_eq_true_eq] at h
    subst n
    exact gateRun st hc
  | cons a rest ih =>
    simp only [axWordCheck] at h
    split at h
    · rename_i m next hn
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hm, hr⟩
      subst m
      exact seq hn (atomRun st hc a) (ih hr _ (by cases a <;> exact hc))
    · contradiction

def axWord (permuted : Bool) : List AXAtom := [
  .par1, .par2, .wal, .par3, .par1, .readp2,
  (if permuted then .cons else .readp1), (if permuted then .readp1 else .cons),
  .par1, .cons, .par1, .par3,
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

/-- Shared pure AX output. This is definitionally the enumerators' AX output. -/
def stack (a h b c u t w : Nat) : Nat :=
  P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c) (P (rho5 a b c)
    (P (rho6 a c) (P (growG a b c) (P (rho8 a b c u) (P (wal u h) (P t w)))))))))

def gate (a b c : Nat) : Nat := if c = a ∨ c = b then 0 else bundle222 a b c

/-- Reading p1 and constructing an implication touch disjoint fields. -/
theorem cons_readp1 (st : AS) :
    AXAtom.cons.effect (AXAtom.readp1.effect st) =
      AXAtom.readp1.effect (AXAtom.cons.effect st) := rfl

/-- Program addresses do not affect evaluation; the only reordered macros commute. -/
theorem eval_permuted (permuted : Bool) (st : AS) :
    axWordEval (axWord permuted) st = axWordEval (axWord false) st := by
  cases permuted <;> rfl

/-- Both literal AX words have one shared symbolic evaluation. -/
theorem ax_eval (permuted : Bool) (np t S c a h pl : Nat) :
    axWordEval (axWord permuted) ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, gate (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) (h + (Cantor.ofNat pl).1) c,
        stack (a + (Cantor.ofNat (Cantor.ofNat pl).2).1) h (h + (Cantor.ofNat pl).1) c a t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := by
  rw [eval_permuted]
  simp only [axWord, Bool.false_eq_true, ↓reduceIte, axWordEval, AXAtom.effect, pushA, popA,
    gateF, ofNat_P, gate, stack, bundle222, nks, clos, req, vrel, growG,
    rho1, rho2, rho3, rho4, rho5, rho6, rho8, wex]

#print axioms axWordRun
#print axioms eval_permuted
#print axioms ax_eval
end SetTheory.BusyBeaver.ZFC.AXWord
