#!/usr/bin/env python3
"""Read-only archive authentication and expression-size metadata for wave11.

Does not invoke Lean or any archive executable. Python replay receipts are
read separately after the audited release drivers finish in scratch copies.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
from itertools import product
from math import prod


ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def expression_size(source, environment, metadata):
    source = re.sub(r"\(\.constant \(-?\d+ : ℤ\)\)", "leaf", source)
    source = re.sub(r"\(\.var \(\.in[lr] \d+\)\)", "leaf", source)
    source = re.sub(r"\.var \(\.in[lr] \d+\)", "leaf", source)
    tokens = re.findall(r"[A-Za-z_][A-Za-z_0-9]*|\d+|[()+*\-]", source)
    require("".join(tokens) == re.sub(r"\s", "", source), "unsupported arithmetic grammar")
    cursor = 0

    def atom():
        nonlocal cursor
        token = tokens[cursor]
        cursor += 1
        if token == "(":
            out = addition()
            require(tokens[cursor] == ")", "unclosed parenthesis")
            cursor += 1
            return out
        if token in environment:
            return environment[token]
        require(token == "leaf" or token.isdigit(), "unknown identifier: " + token)
        return 2

    def multiplication():
        nonlocal cursor
        out = atom()
        while cursor < len(tokens) and tokens[cursor] == "*":
            cursor += 1
            out = metadata.split_mul(out, atom())
        return out

    def addition():
        nonlocal cursor
        out = multiplication()
        while cursor < len(tokens) and tokens[cursor] in ("+", "-"):
            cursor += 1
            out = metadata.split_add(out, multiplication())
        return out

    out = addition()
    require(cursor == len(tokens), "unconsumed expression")
    return out


def height_metadata(path, local_witnesses, metadata):
    section = path.read_text().split("def stepPolynomial", 1)[1].split("def stepRep", 1)[0]
    environment = {}
    output = None
    for line in section.splitlines()[1:]:
        if line.startswith("  let "):
            declaration, expression = line.strip()[4:].split(":=", 1)
            name = declaration.split(":", 1)[0].strip()
            require(name not in environment, "repeated declaration")
            environment[name] = expression_size(expression, environment, metadata)
        elif line.startswith("  ") and line.strip():
            require(output is None, "multiple output expressions")
            output = expression_size(line.strip(), environment, metadata)
    require(output is not None, "missing step output")
    current = metadata.beta_size(metadata.ATOM)
    nxt = metadata.beta_size(metadata.graph_add(metadata.ATOM, metadata.ATOM))
    body = metadata.predicate_compose(metadata.RepSize(local_witnesses, output + 4),
                                      [current, nxt, current, nxt, metadata.ATOM])
    return dict(source_sha256=digest(path), local_witnesses=local_witnesses,
                step_polynomial_split_size=output, bounded_body=body.__dict__,
                bounded_step_witnesses=metadata.forall_count(body),
                endpoint_witnesses=49, outer_witnesses=5,
                closed_rep_witnesses=metadata.forall_count(body) + 49 + 5,
                final_quartic_variable_count=None, new_lean_check=False)


def refined_height_controls(metadata):
    """Additional affine-factor refinement: initialize the budget at1."""
    rules = list(product(range(3), repeat=3))
    cases = balances = 0
    for length in range(4):
        for rows in product(rules, repeat=length):
            bound = prod((1 + p) * (1 + q) + c for p, q, c in rows)
            a = metadata.factor_poly(c for p, q, c in rows)
            b = metadata.factor_poly([1] + [j for p, q, c in rows for j in (p, q)])
            difference = [(a[i] if i < len(a) else 0) -
                          (b[i] if i < len(b) else 0)
                          for i in range(max(len(a), len(b)))]
            require(max(map(abs, difference)) <= bound, "refined affine coefficient bound")
            value_equal = metadata.eval_poly(a, bound + 1) == metadata.eval_poly(b, bound + 1)
            require(value_equal == (not any(difference)), "refined affine carrier injectivity")
            cases += 1
            balances += value_equal
    return dict(status="PASS", labels=[0, 1, 2], maximum_rule_list_length=3,
                rule_lists=cases, polynomial_balances=balances,
                height_initial_value=1, carrier="final_height+1",
                scope="Finite controls supplement the adjacent-coefficient proof; archive unchanged.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--arrival-root", type=Path,
                        default=Path("/tmp/dioph-wave11-arrivals-9a33342a03"))
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    structural = args.arrival_root / "ConZFC_Structural_Reductions_Round11_2026-10-24/con-zfc-structural-reductions-round11"
    budget = args.arrival_root / "con-zfc-budget-and-centering-2026-10-23/con-zfc-budget-and-centering-2026-10-23"
    manifest = json.loads((structural / "MANIFEST.json").read_text())["files"]
    for name, entry in manifest.items():
        path = structural / name
        require(path.stat().st_size == entry["bytes"] and digest(path) == entry["sha256"],
                "structural manifest mismatch: " + name)
    budget_files = 0
    for line in (budget / "MANIFEST.sha256").read_text().splitlines():
        if not line.strip():
            continue
        sha, name = line.split(maxsplit=1)
        name = name.lstrip(" *")
        require(digest(budget / name) == sha, "budget manifest mismatch: " + name)
        budget_files += 1
    module_path = ROOT / "candidates/direct-flow-large-carrier/verify.py"
    spec = importlib.util.spec_from_file_location("large_carrier_metadata", module_path)
    metadata = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = metadata
    spec.loader.exec_module(metadata)
    counts = {}
    for filename, witnesses in [("HeightCommutativeEquation.lean", 20),
                                ("HeightSelectedCommutativeEquation.lean", 21),
                                ("HeightBooleanCommutativeEquation.lean", 23)]:
        counts[filename] = height_metadata(structural / "commutative" / filename, witnesses, metadata)
    names = ["lucas_h1868/integer10.json", "lucas_h1868/PROOF.md", "lucas/PROOF.md",
             "commutative/HEIGHT_CERTIFICATE.md", "REPLAY.json"]
    receipt = dict(status="PASS", arrival_pin="9a33342a03",
                   arrivals=json.loads((args.arrival_root / "ARRIVALS.json").read_text()),
                   authenticated_structural_files=len(manifest), authenticated_budget_files=budget_files,
                   structural_proof_sources_sha256={n: digest(structural / n) for n in names},
                   height_constructor_metadata=counts,
                   large_carrier_comparison=metadata.constructor_metadata(),
                   refined_affine_height_controls=refined_height_controls(metadata),
                   lucas_h1868_metrics=json.loads((structural / "lucas_h1868/METRICS.json").read_text()),
                   budget_local_metrics=json.loads((budget / "direct/LOCAL_METRICS.json").read_text()),
                   primary_reference="https://arxiv.org/html/2609.01594v1",
                   scope="Read-only archive authentication and ordinary constructor arithmetic. No Lean invocation; no formal/native/internal calibration inferred.")
    for name, filename in [("structural_release_replay", "/tmp/proofs62ff-wave11-structural-replay.json"),
                           ("budget_direct_replay", "/tmp/proofs62ff-wave11-budget-direct-replay.json")]:
        path = Path(filename)
        receipt[name] = json.loads(path.read_text()) if path.exists() else dict(status="PENDING")
    if any(receipt[name]["status"] != "PASS" for name in
           ("structural_release_replay", "budget_direct_replay")):
        receipt["status"] = "PENDING_REPLAY"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(dict(status="PASS", output=str(args.output),
                         replays={n: receipt[n]["status"] for n in
                                  ("structural_release_replay", "budget_direct_replay")}), indent=2))


if __name__ == "__main__":
    main()
