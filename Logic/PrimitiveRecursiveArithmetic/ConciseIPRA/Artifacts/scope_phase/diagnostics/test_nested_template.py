#!/usr/bin/env python3
"""Reproduce a nested formula-hole attack on a precisely pinned raw checker.

The copied checker is ProveIt MIT-0 code.  The variants here are deliberately
unsound negative controls, not proposed iPRA checkers.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent


def witness():
    # Shifted codec: formula depth 2, term depth 5; an iterator adds 2.
    e = [[7, 0, 0], [7, 0, [0]]]
    h = [0, 0]
    s = [0, e, h]
    f = [6]
    a = [e]
    m = [s, e]
    dummy = [0, 0, 0, 0]
    # Packets are [source, target, template, major], popped from the end.
    consumed = [[s, e, f, m], [0, e, h, 0], dummy, dummy, dummy]
    return {"E": e, "H": h, "S": s, "F": f, "A": a, "M": m,
            "certificate": list(reversed(consumed)) + [[a, 0]]}


MISSING = object()


def opener(a, t=MISSING, d=2, k=0, parity=True):
    if isinstance(a, list):
        return [opener(b, t, d + 5 - len(a), k, parity) for b in a]
    if type(a) is not int:
        raise ValueError("missing or nonnumeric image")
    if k <= a < d:
        return a
    image = opener(t, MISSING, 5, k, parity)
    return (d % 2) * image if parity else image


def formula_arrays(a):
    """All semantically active formula nodes are arrays, ignoring term trees.

    Ternary formula arrays read Q of their last child. Other formula arities
    except 1, 2, 3 read truth, just as in the audited raw sorted decoder.
    """
    if not isinstance(a, list):
        return False
    if len(a) == 1:
        return formula_arrays(a[0])
    if len(a) == 3:
        return formula_arrays(a[-1])
    return True


GUARD_CODE = '''
def formula_arrays(a):
    if not isinstance(a, list):
        return False
    if len(a) == 1:
        return formula_arrays(a[0])
    if len(a) == 3:
        return formula_arrays(a[-1])
    return True
'''


def run(source, cert, name):
    with tempfile.TemporaryDirectory(prefix="nested-ipra-") as td:
        p = Path(td) / (name + ".py")
        p.write_text(source)
        result = subprocess.run([sys.executable, str(p)], input=json.dumps(cert),
                                text=True, capture_output=True, timeout=10)
    return {"accepted": result.returncode == 0 and result.stdout == "ACCEPT\n",
            "returncode": result.returncode,
            "stdout": result.stdout,
            "error_last_line": result.stderr.strip().splitlines()[-1: ]}


def main():
    w = witness()
    original = (ROOT / "pinned_checker461.py").read_text()
    expected = "e587d311a76e7b1ac9a292883ff57a139ad7ddf8dceff8d39d489a033f29525e"
    if hashlib.sha256(original.encode()).hexdigest() != expected:
        raise RuntimeError("pinned checker changed")
    old = "d % 2 * i(t, d=5)"
    if original.count(old) != 1:
        raise RuntimeError("unexpected opener source")
    weakened = original.replace(old, "i(t, d=5)")
    condition = "(m, a) == (s and r[:2] or [t] * 3, i(t, u))"
    if weakened.count(condition) != 1:
        raise RuntimeError("unexpected replacement test")
    root_guard = weakened.replace(condition,
        "(" + condition + " and isinstance(t, list))")
    entry = "    s, u, t, m = r = q()\n"
    all_goals_guard = GUARD_CODE + root_guard.replace(entry, entry +
        "    if a != 0 and not formula_arrays(a):\n"
        "        raise ValueError('scalar formula node in checked goal')\n"
        "    if any(x != 0 and not formula_arrays(x) for x in g):\n"
        "        raise ValueError('scalar formula node in context')\n")
    results = {name: run(src, w["certificate"], name) for name, src in [
        ("original", original),
        ("no_parity", weakened),
        ("no_parity_and_template_root_array", root_guard),
        ("no_parity_root_array_and_all_goal_formula_nodes_arrays", all_goals_guard)]}
    if results["original"]["accepted"]:
        raise RuntimeError("sound control unexpectedly accepted")
    if not all(v["accepted"] for k, v in results.items() if k != "original"):
        raise RuntimeError("nested counterexample did not replay")
    observations = {
        "F_root_is_array": isinstance(w["F"], list),
        "F_has_only_array_formula_nodes": formula_arrays(w["F"]),
        "target_has_only_array_formula_nodes": formula_arrays(w["A"]),
        "source_has_only_array_formula_nodes": formula_arrays([w["S"]]),
        "major_has_only_array_formula_nodes": formula_arrays(w["M"]),
        "weak_target": opener(w["F"], w["E"], parity=False),
        "weak_source": opener(w["F"], w["S"], parity=False),
        "original_target": opener(w["F"], w["E"], parity=True),
        "E_term_scan": opener(w["E"], d=5, parity=False),
        "S_term_scan": opener(w["S"], d=5, parity=False),
        "false_matrix_at_zero": [0, 0],
        "false_matrix_at_one": [0, 1],
    }
    if observations["weak_target"] != w["A"]:
        raise RuntimeError("target opening mismatch")
    if observations["weak_source"] != [w["S"]]:
        raise RuntimeError("source opening mismatch")
    if observations["E_term_scan"] != w["E"] or observations["S_term_scan"] != w["S"]:
        raise RuntimeError("image closedness mismatch")
    receipt = {"python": sys.version, "snapshot": "7a7633980dbca7f599322a5e7f1e65fb1cddb7c8",
               "original_sha256": expected, "objects": w,
               "observations": observations, "results": results}
    (ROOT / "nested_template_witness.json").write_text(json.dumps(w["certificate"], indent=2) + "\n")
    (ROOT / "nested_template_receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
