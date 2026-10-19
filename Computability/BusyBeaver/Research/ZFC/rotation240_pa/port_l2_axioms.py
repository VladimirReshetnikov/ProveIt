"""Port L2Axioms254.lean (external, Nat records) to ArithmeticL2Axioms254.lean
(internal, records over an IΣ₁ model).

The external module is itself generated (one f/l/c triple per node of the
`axioms()` subtree); the port rewrites it textually: records `AS` become
`AS V`, `seqAS` becomes the internal `R.seq`, the Cantor pairing `P` and its
inverse `Cantor.ofNat` become `cantor` and `first`/`second`. The hand-written
gate (node 71) gets an internal proof. Usage: port_l2_axioms.py SRC DST
"""
import re
import sys

HEADER = '''import BusyBeaver.ZFC.ArithmeticL2Control254

set_option autoImplicit false

/-!
# Internal L2, part 4: the `axioms()` routine of the 219-node program

The internal counterpart of `L2Axioms254`, in every model of `IΣ₁`: one
lemma per node of the `axioms()` subtree, each composing the effects of its
two children, ported mechanically from the external module by
`Research/ZFC/rotation240_pa/port_l2_axioms.py` (records over the model,
the internal Cantor pairing and constructors, the internal structured-run
rules). The final gate (node 71) is proved by hand.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticL2

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticDagRun RMDag
open ArithmeticCode254 (wim wel wal weq)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

'''

GATE = '''/-- The gate (node 71): clear the bundle when `c = b` or `c = a`, and clear
`axiomcode`, `param1`, `param2`. -/
noncomputable def gateF (st : AS V) : AS V :=
  { st with ac := 0, p1 := 0, p2 := 0, tw := if st.ac = st.p1 ∨ st.ac = st.p2 then 0 else st.tw }

theorem gateC (st : AS V) (hc : Clean st) : Clean (gateF st) := hc

theorem l71 (st : AS V) (hc : Clean st) : Rn (.node 71) st (gateF st) := by
  have := R.seq (n := 71) rfl (loop192 st) (R.seq (n := 72) rfl (ifeq_clear _)
    (R.seq (n := 73) rfl (loop211 _) (R.seq (n := 74) rfl (loop197 _) (ifeq_clear _))))
  apply rn_eq this
  obtain ⟨h1, h2⟩ := hc
  rcases st with ⟨np, tw, ws, ac, p1, p2, s1, s2, pl⟩
  simp only at h1 h2
  subst h1; subst h2
  simp only [gateF, zero_add]
  split_ifs <;> simp_all

'''


def port(src):
    s = src
    # drop the header up to the namespace line
    i = s.index("namespace SetTheory.BusyBeaver.ZFC.L2")
    j = s.index("\n", s.index("attribute [local irreducible] Code254.P"))
    body = s[j + 1:]
    body = body.replace("end SetTheory.BusyBeaver.ZFC.L2", "end SetTheory.BusyBeaver.ZFC.ArithmeticL2")
    # gate block: replace by the internal version
    g0 = body.index("/-- The gate (node 71)")
    g1 = body.index("/-- node_111.0 -/")
    body = body[:g0] + GATE + body[g1:]
    body = body.replace("(st : AS) : AS :=", "(st : AS V) : AS V :=")
    body = body.replace("(st : AS)", "(st : AS V)")
    body = re.sub(r"^def ", "noncomputable def ", body, flags=re.M)
    body = body.replace("seqAS (n := ", "R.seq (n := ")
    body = re.sub(r"\(Cantor\.ofNat ([a-z0-9.]+)\)\.1", r"(first \1)", body)
    body = re.sub(r"\(Cantor\.ofNat ([a-z0-9.]+)\)\.2", r"(second \1)", body)
    body = re.sub(r"\bP (st\.[a-z0-9]+) (st\.[a-z0-9]+)", r"cantor \1 \2", body)
    assert "Cantor.ofNat" not in body and "seqAS" not in body, "unported construct"
    return HEADER + body


if __name__ == "__main__":
    with open(sys.argv[1], encoding="utf-8") as f:
        out = port(f.read())
    with open(sys.argv[2], "w", encoding="utf-8", newline="\n") as f:
        f.write(out)
    print("ok", out.count("\ntheorem "), "theorems")
