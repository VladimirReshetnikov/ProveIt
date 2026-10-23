"""Port L2AxiomsEval254.lean (external closed forms) to ArithmeticL2AxiomsEval254.lean.

Textual: records `AS` over the model, `P` -> `cantor`, nested `(Cantor.ofNat X).1/.2`
-> `(first X)`/`(second X)`, `ofNat_P` -> the internal projection lemmas.
Usage: port_l2_eval.py SRC DST
"""
import re
import sys

HEADER = '''import BusyBeaver.ZFC.ArithmeticL2Axioms254

set_option autoImplicit false

/-!
# Internal L2, part 5: closed forms of the `axioms()` nodes

The internal counterpart of `L2AxiomsEval254`, in every model of `IΣ₁`:
each closed form is checked against the definitions of `ArithmeticL2Axioms254`
bottom-up, so that `unP (P x y) = (x, y)` collapses at every step. Ported
mechanically from the external module (itself generated) by
`Research/ZFC/rotation240_pa/port_l2_eval.py`.
-/

namespace SetTheory.BusyBeaver.ZFC.ArithmeticL2

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor RMDag
open ArithmeticCode254 (wim wel wal weq)

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

'''


def replace_ofnat(s):
    key = "(Cantor.ofNat "
    while True:
        i = s.find(key)
        if i < 0:
            return s
        # find the matching close paren of "(Cantor.ofNat ...)"
        depth = 0
        j = i
        while True:
            ch = s[j]
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        arg = s[i + len(key):j]
        proj = s[j + 1:j + 3]
        assert proj in (".1", ".2"), (proj, s[i:j + 4])
        fn = "first" if proj == ".1" else "second"
        s = s[:i] + "(" + fn + " " + arg + ")" + s[j + 3:]


def port(src):
    j = src.index("\n", src.index("set_option linter.unusedSimpArgs false"))
    body = src[j + 1:]
    body = body.replace("end SetTheory.BusyBeaver.ZFC.L2", "end SetTheory.BusyBeaver.ZFC.ArithmeticL2")
    body = body.replace("(st : AS)", "(st : AS V)")
    body = replace_ofnat(body)
    body = re.sub(r"\bP\b", "cantor", body)
    body = body.replace("ofNat_P", "first_cantor, second_cantor")
    body = body.replace("Nat.zero_add", "zero_add")
    assert "Cantor." not in body
    return HEADER + body


if __name__ == "__main__":
    with open(sys.argv[1], encoding="utf-8") as f:
        out = port(f.read())
    with open(sys.argv[2], "w", encoding="utf-8", newline="\n") as f:
        f.write(out)
    print("ok", out.count("\ntheorem "), "theorems")
