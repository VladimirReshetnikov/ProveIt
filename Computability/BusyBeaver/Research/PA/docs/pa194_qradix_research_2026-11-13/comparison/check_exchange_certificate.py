#!/usr/bin/env python3
"""Independent flat replay of the archived symbolic exchange certificate.

This checks the K/S/MP certificate, not the derivation of K and S from rho8.
That additional generic proof dependency is explicitly recorded below.
The archive and repository are read-only.
"""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path


def freeze(x):
    return tuple(freeze(y) for y in x) if isinstance(x, list) else x


def arrow(a, b):
    return ("I", a, b)


def need(condition, description):
    if not condition:
        raise ValueError(description)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text())
    need(data["assumptions"] == [], "the certificate has assumptions")
    checked = []
    counts = Counter()
    for index, line in enumerate(data["lines"]):
        claim = freeze(line["formula"])
        rule = line["rule"]
        if rule == "K":
            a, b = (freeze(x) for x in line["parameters"])
            expected = arrow(a, arrow(b, a))
        elif rule == "S":
            a, b, c = (freeze(x) for x in line["parameters"])
            expected = arrow(arrow(a, arrow(b, c)),
                             arrow(arrow(a, b), arrow(a, c)))
        elif rule == "MP":
            major, minor = line["major"], line["minor"]
            need(isinstance(major, int) and isinstance(minor, int), "noninteger citation")
            need(0 <= major < index and 0 <= minor < index, "forward proof citation")
            implication = checked[major]
            need(isinstance(implication, tuple) and len(implication) == 3
                 and implication[0] == "I", "major premise is not an implication")
            need(implication[1] == checked[minor], "modus ponens antecedent mismatch")
            expected = implication[2]
        else:
            raise ValueError(f"Unrecognized proof rule {rule}")
        need(claim == expected, f"incorrect formula at line {index}")
        checked.append(claim)
        counts[rule] += 1
    expected = arrow(arrow("P", arrow("Q", "R")), arrow("Q", arrow("P", "R")))
    need(checked[data["conclusion_line"]] == expected, "incorrect final formula")
    receipt = {
        "status": "PASS",
        "certificate_sha256": hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
        "lines": len(checked), "rules": dict(sorted(counts.items())),
        "conclusion": "(P -> (Q -> R)) -> (Q -> (P -> R))",
        "assumptions": [],
        "scope": "Universal free-implication-algebra replay, hence every numerical radix instance.",
        "separate_dependency": "K and S from the restricted rho8 basis, via the existing generic Rules proof in M6/Logic/RestrictedImplication.lean; this script does not kernel-check Lean.",
        "radix_instantiation": "I_k(a,b)=k*Cantor(a,b); a,b<=I_k(a,b) for every k>=1 supplies Rules.boundLeft and Rules.boundRight. The complete formula calibration uses k>=4.",
    }
    if args.output:
        args.output.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
