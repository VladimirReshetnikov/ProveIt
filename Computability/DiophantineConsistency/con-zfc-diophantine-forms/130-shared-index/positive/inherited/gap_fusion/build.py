#!/usr/bin/env python3
"""Build the six gap-fusion ten-positive circuits from package 116's tracked schedule.

The parent is the 96-operation coprime-fusion equation delivered as source 116
(con-zfc-diophantine-forms/116-coprime-projection/positive/equation.json), pinned
by SHA-256 below. Three independent changes are applied, each a literal row edit:

  1. transport majorant L := b  (package 118's auxiliary-index gap): delete the
     rows HI = H*(D*E) and L = HI + b; the transport product reads b = cTR;
  2. base: keep 116's direct coordinate X = q + x, or move to the scaled
     zero-offset coordinate X = w*q with g = q - 1 (five rows fewer);
  3. centre: none, the lower centre (A-1)*D*E, or the sharp centre A*D*E,
     added to the centred bracket n + V (two or three rows more).

usage: py -I build.py            write equations/*.json
       py -I build.py --check    rebuild in memory and compare with the files
"""
import hashlib, json, os, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
PARENT = os.path.join(ROOT, "con-zfc-diophantine-forms", "116-coprime-projection", "positive", "equation.json")
PARENT_SHA256 = "7a3429bdd44d27c960d14a39a9534879e695eaf92cf815cbe64b1c5b3bf9602d"
OUTDIR = os.path.join(HERE, "equations")

NAMES = {
    ("scaled", "none"): "gap_fusion_scaled",
    ("scaled", "lower"): "gap_fusion_scaled_lower_centre",
    ("scaled", "sharp"): "gap_fusion_scaled_sharp_centre",
    ("direct", "none"): "gap_fusion_direct",
    ("direct", "lower"): "gap_fusion_direct_lower_centre",
    ("direct", "sharp"): "gap_fusion_direct_sharp_centre",
}


def parent():
    raw = open(PARENT, "rb").read()
    h = hashlib.sha256(raw).hexdigest()
    if h != PARENT_SHA256:
        raise SystemExit(f"parent hash mismatch: {h}")
    return json.loads(raw.decode("utf-8"))


def gap_majorant(rows):
    """Change 1: delete HI and L; every use of L reads the existing b register cTR."""
    out = [list(r) for r in rows if r[0] not in ("HI", "L")]
    for r in out:
        r[2] = "cTR" if r[2] == "L" else r[2]
        r[3] = "cTR" if r[3] == "L" else r[3]
    return out


def scaled_base(rows):
    """Change 2: X = w*q, Bt = (K0+w)C - F, P = q^3 (q-1), no direct correction (q-1)X."""
    out = []
    for r in rows:
        n = r[0]
        if n == "X":
            out.append(["X", "*", "w", "q"])
        elif n == "qK0":
            out += [["K0w", "+", "K0", "w"], ["K0wC", "*", "K0w", "C"], ["B", "-", "K0wC", "F"]]
        elif n in ("qK0X", "qK0XC", "qF", "B", "qbJ", "lowX", "inner"):
            continue
        elif n == "P1":
            out.append(["P1", "*", "q3", "bJ"])
        elif n == "lowY":
            out.append(["lowY", "*", "bJ", "Y"])
        elif n == "inner0":
            out.append(["inner", "-", "lowY", "q3WBt"])
        else:
            out.append(list(r))
    return out


def centre(rows, kind):
    """Change 3: centre n + V + C with C = (A-1)*D*E or A*D*E (D*E is the register DtauI)."""
    if kind == "none":
        return rows
    out = []
    for r in rows:
        if r[0] == "nVL":
            if kind == "lower":
                out.append(["Cg", "*", "Am1", "DtauI"])
            else:
                out.append(["Afull", "+", "Am1", 1])
                out.append(["Cg", "*", "Afull", "DtauI"])
            out.append(["nVCg", "+", "nV", "Cg"])
            out.append(["nVL", "-", "nVCg", "LB"])
        else:
            out.append(r)
    return out


def syntactic_degrees(rows, witnesses):
    deg = {w: 1 for w in witnesses}
    for n, o, x, y in rows:
        dx = deg.get(x, 0) if isinstance(x, str) else 0
        dy = deg.get(y, 0) if isinstance(y, str) else 0
        deg[n] = dx + dy if o == "*" else max(dx, dy)
    return deg


EXACT = {("scaled", "none"): 288, ("scaled", "lower"): 283, ("scaled", "sharp"): 278,
         ("direct", "none"): 262, ("direct", "lower"): 258, ("direct", "sharp"): 254}


def build():
    p = parent()
    rows0 = [list(r) for r in p["source"]]
    out = {}
    for base in ("scaled", "direct"):
        for kind in ("none", "lower", "sharp"):
            rows = gap_majorant(rows0)
            if base == "scaled":
                rows = scaled_base(rows)
            rows = centre(rows, kind)
            wit = ["w" if v == "x" else v for v in p["witnesses"]] if base == "scaled" else list(p["witnesses"])
            deg = syntactic_degrees(rows, wit)
            name = NAMES[(base, kind)]
            out[name] = {
                "name": name,
                "domain": "strictly positive integers",
                "witnesses": wit,
                "fixed_numerals": p["fixed_numerals"],
                "coefficient_binding": {"path": "coefficients/", "tuple": "whole original compact44 tuple (as package 116)"},
                "base": "scaled X=w*q" if base == "scaled" else "direct X=q+x",
                "centre": {"none": "none", "lower": "(A-1)*D*E", "sharp": "A*D*E"}[kind],
                "transport_majorant": "L = b (register cTR)",
                "parent": "con-zfc-diophantine-forms/116-coprime-projection/positive/equation.json",
                "parent_sha256": PARENT_SHA256,
                "operations": len(rows),
                "operation_breakdown": dict(sorted(Counter(r[1] for r in rows).items())),
                "exact_degree": EXACT[(base, kind)],
                "syntactic_degree": deg["N"],
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
            f = os.path.join(OUTDIR, name + ".json")
            if json.load(open(f, encoding="utf-8")) != e:
                print("MISMATCH", name); bad += 1
            else:
                print("ok", name, e["operations"], e["exact_degree"])
        raise SystemExit(1 if bad else 0)
    os.makedirs(OUTDIR, exist_ok=True)
    for name, e in eqs.items():
        with open(os.path.join(OUTDIR, name + ".json"), "w", encoding="utf-8", newline="\n") as f:
            json.dump(e, f, indent=1)
            f.write("\n")
        print("wrote", name, e["operations"], "ops, claimed exact degree", e["exact_degree"],
              "syntactic", e["syntactic_degree"])


if __name__ == "__main__":
    main()
