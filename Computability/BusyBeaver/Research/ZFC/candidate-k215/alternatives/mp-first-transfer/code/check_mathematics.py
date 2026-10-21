#!/usr/bin/env python3
"""Portable mathematical checks for the T215 transfer packet.

Uses only the Python standard library.  The commutation certificate is read
as data by the independently written schema checker below; its generator
and Hilbert helper are never imported or executed.  The dominated-rho8
certificate uses the reviewed, included independent fixed-certificate
reader, also without invoking its generator.  Finite scheduling checks
corroborate the separate universal induction in proofs/permuted_credit.md.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import sys
from collections import Counter
from functools import lru_cache
from math import isqrt
from pathlib import Path

sys.dont_write_bytecode = True


class AuditFailure(ValueError):
    pass


def require(value, message):
    if not value:
        raise AuditFailure(message)


def no_duplicate_keys(pairs):
    obj = {}
    for key, value in pairs:
        require(key not in obj, f"duplicate JSON key: {key}")
        obj[key] = value
    return obj


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=no_duplicate_keys)


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, list) else value


def check_commutation_data(doc):
    """Check every stored node, plus the exact closed theorem dependencies."""
    def I(u, v):
        return ("I", u, v)

    def Q(i, u):
        return ("Q", i, u)

    truth = ("zero",)
    false = ("R", truth, truth)

    def neg(u):
        return I(u, false)

    def diamond(i, u):
        return neg(Q(i, neg(u)))

    a, b, x = (("parameter", name) for name in ("a", "b", "x"))
    allowed = {"K", "S", "DNE", "rho2", "rho6", "oriented_rho4", "hyp", "mp", "gen"}

    def wellformed(term):
        require(isinstance(term, tuple) and bool(term), "malformed AST")
        tag = term[0]
        if tag == "zero":
            require(term == truth, "malformed truth AST")
        elif tag == "parameter":
            require(len(term) == 2 and term[1] in {"a", "b", "x"}, "unknown parameter")
        else:
            require(len(term) == 3 and tag in {"I", "Q", "R"}, "unknown constructor")
            wellformed(term[1])
            wellformed(term[2])

    def schema(rule, args):
        if rule == "K":
            u, v = args
            return I(u, I(v, u))
        if rule == "S":
            u, v, w = args
            return I(I(u, I(v, w)), I(I(u, v), I(u, w)))
        if rule == "DNE":
            u, = args
            return I(neg(neg(u)), u)
        if rule == "rho2":
            i, u, v = args
            return I(Q(i, I(u, v)), I(Q(i, u), Q(i, v)))
        if rule == "rho6":
            i, u = args
            return I(diamond(i, Q(i, u)), u)
        if rule == "oriented_rho4":
            aa, bb, u = args
            require((aa, bb) == (a, b), "opposite orientation or changed labels used as an axiom")
            return I(Q(a, Q(b, u)), Q(b, Q(a, u)))
        raise AuditFailure(f"unsupported axiom: {rule}")

    forms, opens, parents = [], [], []
    require(set(doc) == {"nodes", "outputs"}, "unexpected certificate fields")
    for k, node in enumerate(doc["nodes"]):
        require(set(node) == {"rule", "formula", "parents", "args", "open"}, f"node {k}: unexpected fields")
        rule = node["rule"]
        require(rule in allowed, f"node {k}: unknown rule")
        formula = freeze(node["formula"])
        wellformed(formula)
        ps, args, oo = node["parents"], freeze(node["args"]), node["open"]
        require(all(type(p) is int and 0 <= p < k for p in ps), f"node {k}: invalid parent")
        require(all(type(h) is int and 0 <= h <= k for h in oo), f"node {k}: invalid hypothesis id")
        require(oo == sorted(set(oo)), f"node {k}: malformed hypothesis set")
        opened = set(oo)
        if rule == "hyp":
            require(not ps and args == (k,) and opened == {k}, f"node {k}: malformed hypothesis")
        elif rule == "mp":
            require(len(ps) == 2 and not args, f"node {k}: malformed MP")
            major, minor = ps
            require(forms[major] == I(forms[minor], formula), f"node {k}: MP mismatch")
            require(opened == opens[major] | opens[minor], f"node {k}: wrong MP assumptions")
        elif rule == "gen":
            require(len(ps) == 1 and len(args) == 1, f"node {k}: malformed GEN")
            require(not opens[ps[0]], f"node {k}: GEN under an open hypothesis")
            require(not opened and formula == Q(args[0], forms[ps[0]]), f"node {k}: GEN mismatch")
        else:
            require(not ps and not opened, f"node {k}: axiom has parents or assumptions")
            require(formula == schema(rule, args), f"node {k}: invalid axiom instance")
        forms.append(formula)
        opens.append(opened)
        parents.append(ps)

    expected = {
        "reversed_commutation": I(Q(b, Q(a, x)), Q(a, Q(b, x))),
        "symmetry_unit": I(x, Q(a, diamond(a, x))),
    }
    require(set(doc["outputs"]) == set(expected), "wrong output collection")
    for name, index in doc["outputs"].items():
        require(type(index) is int and 0 <= index < len(forms), "invalid output index")
        require(not opens[index] and forms[index] == expected[name], f"wrong or open output: {name}")
    reachable = set(doc["outputs"].values())
    todo = list(reachable)
    while todo:
        for parent in parents[todo.pop()]:
            if parent not in reachable:
                reachable.add(parent)
                todo.append(parent)
    require(all(not opens[k] for k in reachable), "theorem dependencies retain an assumption")
    oriented = [k for k, node in enumerate(doc["nodes"]) if node["rule"] == "oriented_rho4"]
    require(len(oriented) == 1, "wrong oriented-axiom count")
    require(freeze(doc["nodes"][oriented[0]]["args"]) == (a, b, neg(Q(b, Q(a, x)))), "wrong oriented matrix")
    counts = Counter(node["rule"] for node in doc["nodes"])
    require(len(forms) == 600 and len(reachable) == 488, "unexpected certificate census")
    require(counts["gen"] == 5, "unexpected GEN count")
    return {
        "status": "PASS",
        "reader": "Independent inline schema reader; no generator or Hilbert-helper import",
        "stored_nodes": len(forms),
        "output_dependency_nodes": len(reachable),
        "output_dependencies_have_no_hypotheses": True,
        "rule_counts": dict(sorted(counts.items())),
        "reachable_rule_counts": dict(sorted(Counter(doc["nodes"][k]["rule"] for k in reachable).items())),
        "oriented_axiom_nodes": oriented,
        "only_oriented_axiom_labels": ["a", "b"],
        "oriented_axiom_matrix": "not(Box_b(Box_a(x)))",
        "all_five_GEN_premises_closed": True,
        "exact_closed_outputs": sorted(expected),
    }


def check_commutation(root):
    doc = read_json(root / "formalism/ordered_commutation_dag.json")
    result = check_commutation_data(doc)
    negative = []
    # These directly exercise the two proof-boundary risks under review.
    tampered = copy.deepcopy(doc)
    node = next(n for n in tampered["nodes"] if n["rule"] == "oriented_rho4")
    node["args"][0], node["args"][1] = node["args"][1], node["args"][0]
    try:
        check_commutation_data(tampered)
    except AuditFailure as exc:
        negative.append({"case": "opposite orientation inserted as axiom", "rejected": True, "reason": str(exc)})
    else:
        raise AuditFailure("opposite-orientation negative control was accepted")
    tampered = copy.deepcopy(doc)
    gi = next(k for k, n in enumerate(tampered["nodes"]) if n["rule"] == "gen")
    hi = next(k for k, n in enumerate(tampered["nodes"][:gi]) if n["rule"] == "hyp")
    node = tampered["nodes"][gi]
    node["parents"] = [hi]
    node["formula"] = ["Q", node["args"][0], tampered["nodes"][hi]["formula"]]
    try:
        check_commutation_data(tampered)
    except AuditFailure as exc:
        negative.append({"case": "GEN on an open hypothesis", "rejected": True, "reason": str(exc)})
    else:
        raise AuditFailure("open-GEN negative control was accepted")
    result["negative_controls"] = negative
    return result


def check_credit():
    def unpair(n):
        s = (isqrt(8 * n + 1) - 1) // 2
        y = n - s * (s + 1) // 2
        return s - y, y

    def right(n):
        return unpair(n)[1]

    def shape(n):
        a, y = unpair(n)
        if a == 0:
            return "MP", 0, right(y)
        if a == 1:
            return "S", -1, y
        return "AX", 10, right(right(y))

    count = 500_000
    balances, minima, lengths, sums = [], [], [], [0]
    for n in range(count):
        tag, delta, residual = shape(n)
        j = residual - 1
        require(j < n, "nondecreasing schedule recursion")
        bal = delta + (balances[j] if residual else 0)
        low = min(0, delta + (minima[j] if residual else 0))
        length = 1 + (lengths[j] if residual else 0)
        require(length <= n + 1, "length bound failure")
        balances.append(bal)
        minima.append(low)
        lengths.append(length)
        sums.append(sums[-1] + bal)

    @lru_cache(None)
    def explicit(n):
        tag, _, residual = shape(n)
        return (tag,) + (explicit(residual - 1) if residual else ())

    for n in range(1000):
        bal = low = 0
        for tag in explicit(n):
            bal += {"MP": 0, "S": -1, "AX": 10}[tag]
            low = min(low, bal)
        require((bal, low, len(explicit(n))) == (balances[n], minima[n], lengths[n]), "explicit-word mismatch")
    require([explicit(n) for n in range(3)] == [("MP",), ("S",), ("MP",)], "initial words mismatch")
    require(sums[:4] == [0, 0, -1, -1], "initial balances mismatch")
    require(min(sums[n] + minima[n] for n in range(count)) == -1, "wrong global finite minimum")
    require(min(sums[n] - sums[1] + minima[n] for n in range(1, count)) == -1, "wrong cutoff-one minimum")
    require(all(sums[k] + k >= 0 for k in range(count + 1)), "shifted invariant failure")
    diagonals = 0
    for s in range(2, isqrt(2 * count) + 2):
        lo, hi = s * (s + 1) // 2, (s + 1) * (s + 2) // 2
        if hi > count:
            break
        require(all(sums[n] - sums[lo] + minima[n] >= 0 for n in range(lo, hi)), "diagonal prefix failure")
        require(sums[hi] - sums[lo] >= 7 * s - 9, "diagonal balance bound failure")
        require(sums[lo] >= -1, "diagonal initial invariant failure")
        diagonals += 1

    def credit(cutoff):
        s = (isqrt(8 * cutoff + 1) - 1) // 2
        end = max(3, (s + 1) * (s + 2) // 2)
        return max([0] + [-(sums[n] - sums[cutoff] + minima[n]) for n in range(cutoff, end)])

    require(credit(0) == credit(1) == 1 and credit(2) == 0, "exact initial credit mismatch")
    return {
        "status": "FINITE_CORROBORATION_PASS",
        "scope": "The universal bound is proved in proofs/permuted_credit.md; this check corroborates the indexing and recurrence",
        "tags": {"MP": 0, "S": 1, "AX": "c+2"},
        "guard_scope": "Either single-guard S or two-guard composite S'; common normal-return stack effect only",
        "conservative_weights": {"MP": 0, "S": -1, "AX": 10},
        "candidate_summaries": count,
        "explicit_words": 1000,
        "complete_diagonals": diagonals,
        "minimum_from_cutoffs_zero_and_one": -1,
        "exact_conservative_credit_at_cutoff_one": 1,
        "ten_head_initial_margin": 9,
        "credits_first_twenty": [credit(n) for n in range(20)],
    }


def check_dominated(root):
    reader_path = root / "reference/transfer-parent/checks/check_fixed_certificate.py"
    cert_path = root / "reference/transfer-parent/inputs/dominated_rho8_full_certificate.json"
    spec = importlib.util.spec_from_file_location("t215_independent_dominated_reader", reader_path)
    require(spec is not None and spec.loader is not None, "cannot load included dominated certificate reader")
    reader = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(reader)
    data = read_json(cert_path)
    report, _, _, _, _ = reader.verify(data, True)
    require(report["verified"] and report["proof_nodes"] == 3728, "unexpected dominated-certificate result")
    require(report["term_table_nodes"] == 5160, "unexpected dominated term census")
    return {
        "status": "INHERITED_INDEPENDENT_READER_PASS",
        "scope": "Fixed full dominated-rho8 certificate; no generator, search, binary runtime, or full set-theory calibration",
        "reader": str(reader_path.relative_to(root)),
        "normalization": "Only I(T,T)=T; T is native zero, integer leaf zero is a metavariable",
        "substitution_scope": "Complete simultaneous schematic instantiation, not an unrestricted numerical inference rule",
        "result": report,
    }


def audit(packet_root=None):
    """Return the deterministic audit record; do not write any files."""
    root = Path(packet_root).resolve() if packet_root else Path(__file__).resolve().parents[1]
    commutation = check_commutation(root)
    credit = check_credit()
    dominated = check_dominated(root)
    relative_inputs = [
        "formalism/ordered_commutation_dag.json",
        "proofs/permuted_credit.md",
        "reference/transfer-parent/inputs/dominated_rho8_full_certificate.json",
        "reference/transfer-parent/checks/check_fixed_certificate.py",
    ]
    return {
        "status": "MATHEMATICS_AUDIT_PASS",
        "commutation": commutation,
        "scheduler_credit": credit,
        "dominated_rho8": dominated,
        "input_sha256": {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in relative_inputs},
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "remaining_premises": [
            "The inherited complete native-calculus/ZFC calibration",
            "Classical DNE follows from the inherited classical propositional interface, including retained rho6",
            "The ordinary all-natural induction in proofs/permuted_credit.md",
            "The selected machine's own exact source contracts, whole-tape runtime, and blank startup",
        ],
        "not_claimed": ["Lean/Rocq kernel certification", "a 214-state machine", "a physical state saving from ordered rho4"],
    }


def verify(packet_root=None):
    """Compatibility API for packet replay: audit in memory without writing."""
    return audit(packet_root)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1], help="extracted packet root")
    parser.add_argument("--out", type=Path, help="audit JSON output; defaults to ROOT/evidence/mathematics_audit.json")
    args = parser.parse_args(argv)
    result = audit(args.root)
    out = args.out or args.root / "evidence/mathematics_audit.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({
        "status": result["status"],
        "commutation_nodes": result["commutation"]["stored_nodes"],
        "commutation_theorem_dependencies": result["commutation"]["output_dependency_nodes"],
        "credit_candidates": result["scheduler_credit"]["candidate_summaries"],
        "credit_diagonals": result["scheduler_credit"]["complete_diagonals"],
        "dominated_nodes": result["dominated_rho8"]["result"]["proof_nodes"],
    }, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
