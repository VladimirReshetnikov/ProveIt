#!/usr/bin/env python3
"""Build the two q-cube product-square ten-positive circuits from package 133's compact circuits.

Parents (tracked, pinned by SHA-256): con-zfc-diophantine-forms/133-staged-certificates/compact/
equation_84.json (weight L = V^2, 84 operations) and equation_85.json (L = bV, 85 operations).

Transformation (PROOF.md section 1), as literal row edits:
  * the unknown Y is replaced by Y = q^3 * s with a new unknown s (one added row);
  * the common factor q^3 of Z and M is cancelled: P = q^3 (q-1) becomes q - 1, so the row
    P1 = q3*bJ is deleted, P1mu2 = P1*mu2 becomes hmu2 = bJ*mu2, and the eight low-bracket rows
    qm1Y, q3Bt, inner, mu2inner, P1e, brk, Zpart2, Znum are replaced by the five rows
        mu2Bt = mu2*Bt, bJe = bJ*e, lowsum = mu2Bt + bJe, Zpart2 = Hp*lowsum,
        Znum = Zpart1 - Zpart2;
  * the term Y/q^3 = s of the centre is absorbed into n (the new n is the old n + s).

usage: py -I build.py [--check]
"""
import hashlib, json, os, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
PARENT_DIR = os.path.join(ROOT, "con-zfc-diophantine-forms", "133-staged-certificates", "compact")
PARENTS = {
    "equation_84": ("c7db162322ec4605f2bf68e73fad288ad0399d6cc9cce5fc80b95556e9f13630", "qcube_product_square_81", 750, "V^2"),
    "equation_85": ("75b34f2a6e1986656529da58da99b72b01265aeeb5691a69549aeac21ecea803", "qcube_product_square_82", 560, "bV"),
}
DROP = {"qm1Y", "q3Bt", "inner", "mu2inner", "P1e", "brk", "Zpart2", "Znum", "P1"}


def transform(d):
    rows = []
    for r in d["source"]:
        n = r[0]
        if n in DROP:
            continue
        if n == "P1mu2":
            rows.append(["hmu2", "*", "bJ", "mu2"])
        elif n == "q3":
            rows.append(list(r))
            rows.append(["Y", "*", "q3", "s"])
        else:
            rows.append([n, r[1]] + ["hmu2" if a == "P1mu2" else a for a in r[2:]])
        if n == "Zpart1":
            rows += [["mu2Bt", "*", "mu2", "Bt"], ["bJe", "*", "bJ", "e"], ["lowsum", "+", "mu2Bt", "bJe"],
                     ["Zpart2", "*", "Hp", "lowsum"], ["Znum", "-", "Zpart1", "Zpart2"]]
    wit = ["s" if v == "Y" else v for v in d["witnesses"]]
    defined = set(wit) | set(d["fixed_numerals"])
    pending, ordered = rows[:], []
    while pending:
        for r in pending:
            if all((not isinstance(a, str)) or a in defined for a in r[2:]):
                ordered.append(r)
                defined.add(r[0])
                pending.remove(r)
                break
        else:
            raise SystemExit("dependency cycle")
    return wit, ordered


def build():
    out = {}
    for pname, (sha, name, deg, weight) in PARENTS.items():
        raw = open(os.path.join(PARENT_DIR, pname + ".json"), "rb").read()
        if hashlib.sha256(raw).hexdigest() != sha:
            raise SystemExit("parent hash mismatch: " + pname)
        d = json.loads(raw.decode("utf-8"))
        wit, rows = transform(d)
        out[name] = {
            "name": name,
            "domain": "strictly positive integers",
            "witnesses": wit,
            "fixed_numerals": d["fixed_numerals"],
            "coefficient_binding": {"path": "coefficients/", "tuple": "whole indexed compact44 tuple of package 133"},
            "transport_weight": weight,
            "parent": "con-zfc-diophantine-forms/133-staged-certificates/compact/" + pname + ".json",
            "parent_sha256": sha,
            "operations": len(rows),
            "operation_breakdown": dict(sorted(Counter(r[1] for r in rows).items())),
            "exact_degree": deg,
            "output": "N",
            "proof": "PROOF.md",
            "source": rows,
        }
    return out


def main():
    eqs = build()
    if "--check" in sys.argv:
        bad = 0
        for name, e in eqs.items():
            ok = json.load(open(os.path.join(HERE, "equations", name + ".json"), encoding="utf-8")) == e
            print(("ok " if ok else "MISMATCH ") + name, e["operations"], e["exact_degree"])
            bad += not ok
        raise SystemExit(1 if bad else 0)
    os.makedirs(os.path.join(HERE, "equations"), exist_ok=True)
    for name, e in eqs.items():
        with open(os.path.join(HERE, "equations", name + ".json"), "w", encoding="utf-8", newline="\n") as f:
            json.dump(e, f, indent=1)
            f.write("\n")
        print("wrote", name, e["operations"], "operations, exact degree", e["exact_degree"])


if __name__ == "__main__":
    main()
