#!/usr/bin/env python3
"""Build two quotient-normalized Pell product-square circuits.

The immutable inherited product84/product85 circuits supply the parent.
No network access or optional packages are used.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json

HERE = Path(__file__).resolve().parent


def construct(parent, parent_file, cost, degree, normalize=True, free_t=True):
    result = copy.deepcopy(parent)
    rows = []
    cuts = []
    removed = {"q3", "P1", "qm1Y", "q3Bt", "inner"} if normalize else set()
    if free_t:
        removed.add("Tp")
    replacements = {
        "P1mu2": ["P1mu2", "*", "bJ", "mu2"],
        "mu2inner": ["mu2inner", "*", "mu2", "Bt"],
        "P1e": ["P1e", "*", "bJ", "e"],
        "brk": ["brk", "+", "mu2inner", "P1e"],
        "Znum": ["Znum", "-", "Zpart1", "Zpart2"],
    } if normalize else {}
    if free_t:
        replacements["cT"] = ["cT", "*", "c", "T"]
    # Moving q2 and q3 before Y preserves all preexisting consumers.
    for old_index, row in enumerate(parent["source"]):
        name = row[0]
        if name in removed or (normalize and name == "q2"):
            cuts.append({"old_index": old_index, "row": row, "action": "remove_or_move"})
            continue
        if normalize and name == "k":
            rows += [["q2", "*", "q", "q"], ["q3", "*", "q2", "q"],
                     ["Y", "*", "q3", "s"]]
        replacement = replacements.get(name, row)
        cuts.append({"old_index": old_index, "row": row,
                     "action": "replace" if name in replacements else "keep",
                     "new_index": len(rows), "new_row": replacement})
        rows.append(replacement)
    result["name"] = f"doubled_product_{cost}_{degree}"
    result["transport_weight"] = "V^2" if parent["transport_weight"] in ("V2", "V^2") else "bV"
    result["witnesses"] = ["s" if normalize and x == "Y" else x for x in parent["witnesses"]]
    result["source"] = rows
    result["operations"] = len(rows)
    result["operation_breakdown"] = {op: sum(r[1] == op for r in rows) for op in ("*", "+", "-")}
    if len(rows) != cost:
        raise ValueError((cost, len(rows)))
    result["exact_degree"] = degree
    result["proof"] = "PROOF.md"
    result["proof_status"] = (
        "Ordinary proof of the quotient-normalized doubled-product reduction, "
        "composed with the named inherited native/refutation theorem for the whole "
        "indexed BFS943 tuple. No fresh end-to-end Lean/Rocq or object-ZFC proof term."
    )
    result["parent_commit"] = "1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61"
    result["parent_path"] = str(Path("inherited") / parent_file)
    result["parent_sha256"] = hashlib.sha256((HERE / result["parent_path"]).read_bytes()).hexdigest()
    result["normalization"] = {
        "qcube": normalize, "free_T": free_t,
        "Y_old": "q^3*s" if normalize else "Y",
        "n_old": "n-s" if normalize else "n",
        "T_old": "T-alpha" if free_t else "T",
        "Z_old": "q^3*Z" if normalize else "Z",
        "M_old": "q^3*M" if normalize else "M",
        "N_old": "q^6*N" if normalize else "N",
        "domain_warning": "Shifted old coordinates need not be positive; soundness is proved directly."
    }
    tl = "T" if free_t else "(T+alpha)"
    if not normalize:
        result["leading_form"] = "2^14*(beta*J)^200*w^46*Y^104*i^20*(eta+zeta)^60*(beta*J-F)^4*(beta*J-F-alpha)^2"
    elif result["transport_weight"] == "V^2":
        result["leading_form"] = f"2^14*(beta*J)^506*w^46*s^108*i^20*(eta+zeta)^64*{tl}^4*(beta*J-F-alpha)^2"
    else:
        result["leading_form"] = f"-2^10*(beta*J)^384*w^34*s^80*i^14*(eta+zeta)^46*{tl}^2"
    return result, cuts


def outputs():
    result = {}
    cuts = {}
    for parent_cost, cost, degree, normalize, free_t in [
        (84, 83, 436, False, True),
        (84, 80, 750, True, True),
        (85, 81, 560, True, True),
    ]:
        filename = f"product{parent_cost}.json"
        parent = json.loads((HERE / "inherited" / filename).read_text())
        equation, trace = construct(parent, filename, cost, degree, normalize, free_t)
        result[f"equation_{cost}_{degree}.json"] = equation
        cuts[f"equation_{cost}_{degree}.json"] = trace
    result["CUTS.json"] = cuts
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for name, data in outputs().items():
        content = json.dumps(data, indent=2) + "\n"
        path = HERE / name
        if args.check:
            if path.read_text() != content:
                raise ValueError(f"rebuild mismatch: {name}")
        else:
            path.write_text(content)
    print(json.dumps({"rebuild": "matched" if args.check else "written", "outputs": list(outputs())}))


if __name__ == "__main__":
    main()
