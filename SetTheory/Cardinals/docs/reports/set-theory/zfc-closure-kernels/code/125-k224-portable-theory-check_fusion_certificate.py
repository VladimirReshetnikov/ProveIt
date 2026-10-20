#!/usr/bin/env python3
"""Independently check the closed K-bundle Hilbert certificate.

No generator code is imported. Accepted proof leaves are K,S,Peirce,rho2,
rho6. The only inference rules are modus ponens and theorem generalization.
K/S/Peirce are upstream derived schemas, not new set-theoretic assumptions.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path


def require(condition, text):
    if not condition:
        raise ValueError(text)


def check(data):
    require(data["format"] == "k-fusion-hilbert-v1", "unexpected format")
    ts, ps = data["terms"], data["proofs"]
    inv = {}
    for i, t in enumerate(ts):
        require(tuple(t) not in inv, "duplicate formula nodes")
        tag = t[0]
        if tag == "I":
            require(len(t) == 3 and all(isinstance(n, int) and 0 <= n < i for n in t[1:]), "bad implication node")
        elif tag == "Q":
            require(len(t) == 3 and isinstance(t[2], int) and 0 <= t[2] < i, "bad quantifier node")
        else:
            require(tag in ("F", "meta", "Rel", "Eq"), "unknown formula atom")
            require(len(t) == {"F": 1, "meta": 2, "Rel": 3, "Eq": 3}[tag], "bad atom arity")
        inv[tuple(t)] = i
    def at(*key):
        require(tuple(key) in inv, "missing required formula constructor")
        return inv[tuple(key)]
    F = at("F")
    I = lambda a, b: at("I", a, b)
    Q = lambda x, a: at("Q", x, a)
    N = lambda a: I(a, F)
    Ex = lambda x, a: N(Q(x, N(a)))
    schema_counts = {}
    for n, p in enumerate(ps):
        rule, form, refs, args = p["rule"], p["formula"], p["refs"], p["args"]
        require(isinstance(form, int) and 0 <= form < len(ts), "bad conclusion index")
        require(all(isinstance(r, int) and 0 <= r < n for r in refs), "non-earlier proof premise")
        schema_counts[rule] = schema_counts.get(rule, 0) + 1
        if rule in ("K", "S", "P", "rho2", "rho6"):
            require(not refs, "axiom has premises")
            if rule == "K":
                require(len(args) == 2, "K arity")
                a, b = args
                want = I(a, I(b, a))
            elif rule == "S":
                require(len(args) == 3, "S arity")
                a, b, c = args
                want = I(I(a, I(b, c)), I(I(a, b), I(a, c)))
            elif rule == "P":
                require(len(args) == 2, "P arity")
                a, b = args
                want = I(I(I(a, b), a), a)
            elif rule == "rho2":
                require(len(args) == 3, "rho2 arity")
                x, a, b = args
                want = I(Q(x, I(a, b)), I(Q(x, a), Q(x, b)))
            else:
                require(len(args) == 2, "rho6 arity")
                x, a = args
                want = I(Ex(x, Q(x, a)), a)
        elif rule == "mp":
            require(len(refs) == 2 and not args, "MP arity")
            a = ps[refs[0]]["formula"]
            impl = ts[ps[refs[1]]["formula"]]
            require(impl[0] == "I" and impl[1] == a, "MP antecedent mismatch")
            want = impl[2]
        elif rule == "gen":
            require(len(refs) == 1 and len(args) == 1, "GEN arity")
            want = Q(args[0], ps[refs[0]]["formula"])
        else:
            raise ValueError("unaccepted proof rule: " + rule)
        require(form == want, "wrong conclusion for " + rule)
    ends = data["endpoints"]
    require(len(ends) == 2 and all(0 <= n < len(ps) for n in ends), "bad endpoints")
    old, fused = data["old_bundle"], data["fused_bundle"]
    require(ps[ends[0]]["formula"] == I(old, fused), "forward endpoint mismatch")
    require(ps[ends[1]]["formula"] == I(fused, old), "backward endpoint mismatch")
    reachable = set()
    def visit(n):
        if n in reachable:
            return
        reachable.add(n)
        for r in ps[n]["refs"]:
            visit(r)
    for n in ends:
        visit(n)
    require(len(reachable) == len(ps), "irrelevant proof nodes in certificate")
    return {"status": "PASS_CLOSED_HILBERT_CERTIFICATE", "proof_nodes": len(ps),
            "formula_dag_nodes": len(ts), "rule_counts": schema_counts,
            "endpoints": "old_bundle -> fused_bundle; fused_bundle -> old_bundle",
            "basis": "K/S/Peirce derived from rho8 upstream; literal rho2/rho6; MP/GEN only",
            "set_axioms_used": 0, "freshness_assumptions": 0}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("certificate", type=Path, nargs="?", default=Path(__file__).with_name("fusion_certificate.json"))
    p.add_argument("--output", type=Path, default=Path(__file__).with_name("fusion_certificate_receipt.json"))
    a = p.parse_args()
    raw = a.certificate.read_bytes()
    data = json.loads(raw)
    result = check(data)
    # These controls show the checker rejects invalid inference, a changed
    # target formula, and an attempted hypothesis or unsupported rule.
    controls = []
    for kind in ("wrong_endpoint", "broken_modus_ponens", "hypothesis_leaf"):
        bad = copy.deepcopy(data)
        if kind == "wrong_endpoint":
            bad["old_bundle"] = bad["fused_bundle"]
        elif kind == "broken_modus_ponens":
            for pr in bad["proofs"]:
                if pr["rule"] == "mp":
                    pr["refs"][0] = pr["refs"][1]
                    break
        else:
            bad["proofs"][0]["rule"] = "hyp"
        try:
            check(bad)
        except ValueError:
            controls.append(kind)
        else:
            raise ValueError("tamper accepted: " + kind)
    result["rejected_tamper_controls"] = controls
    result["sha256"] = hashlib.sha256(raw).hexdigest()
    a.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
