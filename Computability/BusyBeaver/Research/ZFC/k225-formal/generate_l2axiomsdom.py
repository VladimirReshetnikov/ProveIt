#!/usr/bin/env python3
"""Generate L2AxiomsDom.lean (the 217) or L2AxiomsPerm.lean (the 215): the AX routine (node 236).

Node 236 of dagDom (make_dagdom.py) and of dagPerm (make_dagperm.py) is a linear chain of macro
atoms, node n = (atom, next), ending in the gate (192, 131, 211, 197, 131). The atoms are the
register macros (par1/2/3, pushwff, cons, wel, wal, weq, wn, wa, wex, readp1, readp2), whose run
contracts L2Dom / L2Perm transfer from dag222. The output is a checked macro word: one run
induction composes the contracts along the word, a kernel check binds the word to the literal
program, and one symbolic evaluation identifies its effect with the enumerator's AX step
(`ax_eval`). Both programs share the template; the Dom output renames its Perm identifiers.

Usage: generate_l2axiomsdom.py NODES_JSON OUT_LEAN [perm]
  dom  (default): lean217/dagdom_nodes.json -> L2AxiomsDom.lean
  perm:           lean215/dagperm_nodes.json -> L2AxiomsPerm.lean
"""
import json
import sys


def to_dom(text):
    """the 217's program dagDom (make_dagdom.py) instead of dagPerm"""
    for a, b in [("dagPerm", "dagDom"), ("DagPerm", "DagDom"), ("L2Perm", "L2Dom"),
                 ("EnumPerm", "EnumDom")]:
        text = text.replace(a, b)
    return text


src, out = sys.argv[1], sys.argv[2]
VARIANT = sys.argv[3] if len(sys.argv) > 3 else "dom"
d = json.load(open(src))
nodes = {int(k): v for k, v in d["nodes"].items()}
FIELDS = ["np", "tw", "ws", "ac", "p1", "p2", "s1", "s2", "pl"]

# the chain from 236
chain, n = [], 236
while True:
    a, b = nodes[n]
    assert a[0] == "N"
    chain.append(n)
    if b[0] == "N" and b[1] >= 301 and b[1] not in chain:
        n = b[1]
        continue
    break
last = chain[-1]
atoms = [nodes[m][0][1] for m in chain] + [nodes[last][1][1]]
assert atoms == d["word236"], "chain atoms differ from the recorded word"

LEAF = {166: ("par1L", "par1F", "par1C"), 121: ("par2L", "par2F", "par2C"),
        168: ("par3L", "par3F", "par3C"), 171: ("pushL", "pushF", "pushC"),
        119: ("consL", "consF", "consC"), 181: ("welL", "welF", "welC"),
        180: ("walL", "walF", "walC"), 182: ("weqL", "weqF", "weqC"),
        218: ("wnL", "wnF", "wnC"), 178: ("waL", "waF", "waC"),
        183: ("wexL", "wexF", "wexC"), 176: ("readp2L", "readp2F", "readp2C"),
        175: ("readp1L", "readp1F", "readp1C")}

# locate the literal read (158, 208) and the gate (192, 131, 211, 197, 131)
pos = {m: i for i, m in enumerate(chain)}
assert 158 not in atoms
assert atoms[-5:] == [192, 131, 211, 197, 131]
G = len(chain) - 4                 # chain[G] = (192, chain[G+1]), ..., chain[G+3] = (197, 131)
assert [nodes[chain[G + k]][0][1] for k in range(4)] == [192, 131, 211, 197]
other = set(atoms[:G])
assert other <= set(LEAF), sorted(other - set(LEAF))

PERM_TEMPLATE = r"""import BusyBeaver.ZFC.L2Perm
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

theorem l@G0@ (st : AS) (hc : Clean st) : Rn (.node @G0@) st (gateF st) := by
  have := seqAS (n := @G0@) rfl (loop192 st) (seqAS (n := @G1@) rfl (ifeq_clear _)
    (seqAS (n := @G2@) rfl (loop211 _) (seqAS (n := @G3@) rfl (loop197 _) (ifeq_clear _))))
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
  | n, [] => decide (n = @G0@)
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
    exact l@G0@ st hc
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
@WORD@

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
"""


word = [(LEAF[atoms[i]][1][:-1], chain[i + 1]) for i in range(G)]
rows = [", ".join(f".{a}" for a, _ in word[i:i + 12]) for i in range(0, len(word), 12)]
text = PERM_TEMPLATE.replace("@WORD@", ",\n".join("  " + r for r in rows) + "]")
for k in range(4):
    text = text.replace(f"@G{k}@", str(chain[G + k]))
if VARIANT == "perm":
    assert chain[G] == 457, "the Perm word must end at the checked gate"
else:
    text = to_dom(text)
with open(out, "w", encoding="utf-8", newline="\n") as stream:
    stream.write(text)
print("wrote", out, "checked macro word", len(word), "gate", chain[G])
