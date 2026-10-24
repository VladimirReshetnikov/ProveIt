#!/usr/bin/env python3
"""Frozen signed-integer compiler for the eight-column direct C222 certificate."""
import argparse
import collections
import hashlib
import importlib.util
import json
import pathlib
import polynomial as sparse

def signed_class(base, infer_quotient_signs=False):
    class SignedCompiler(base):
        def __init__(self):
            super().__init__()
            self.unrestricted = set()
            self.inferred_nonnegative = set()
            self.sign_inference = []

        def c(self, n):
            return self.node(("c", n))

        def sub(self, a, b):
            if b == self.c(0):
                return a
            if a == b:
                return self.c(0)
            if self.nodes[a][0] == self.nodes[b][0] == "c":
                return self.c(self.nodes[a][1] - self.nodes[b][1])
            return self.node(("s", a, b))

        def signed(self, a):
            return a

        def diff(self, a, b):
            return self.sub(a, b)

        def iadd(self, a, b):
            return self.add(a, b)

        def imul(self, a, b):
            return self.mul(a, b)

        def isum(self, xs):
            return self.sum(xs)

        def iprod(self, xs):
            return self.prod(xs)

        def sos(self, residuals):
            return self.sum([self.mul(r, r) for r in residuals])

        def assertpoly(self, residual, label):
            self.eq(residual, self.c(0), label)

        def mod(self, a, b, m, label):
            q = self.fresh(label + ".signed_q")
            self.unrestricted.add(self.nodes[q][1])
            return self.sub(self.add(a, self.mul(m, q)), b)

        def divmod(self, n, d):
            self.calls["divmod"] += 1
            before = (len(self.vars), len(self.eqs), len(self.nodes))
            q, r, s = [self.fresh("division." + j) for j in ["quotient", "remainder", "slack"]]
            self.eq(n, self.add(self.mul(q, d), r), "division equation")
            self.eq(d, self.addc(self.add(r, s), 1), "positive divisor/remainder bound")
            if infer_quotient_signs:
                index = self.nodes[q][1]
                self.unrestricted.add(index)
                self.inferred_nonnegative.add(index)
                self.sign_inference.append({"rule": "euclidean_quotient", "variable": index, "dividend_node": n, "divisor_node": d, "remainder_node": r, "slack_node": s})
            self.ledger.append({"kind": "divmod", "arguments": (n, d), "result": (q, r), "before": before, "after": (len(self.vars), len(self.eqs), len(self.nodes))})
            return q, r

    return SignedCompiler

def prune(c):
    live = {node for left, right, label in c.eqs for node in (left, right)}
    for i in range(len(c.nodes) - 1, -1, -1):
        if i in live and c.nodes[i][0] in ("a", "s", "m"):
            live.update(c.nodes[i][1:])
    used_vars = {c.nodes[i][1] for i in live if c.nodes[i][0] == "v"}
    if used_vars != set(range(len(c.vars))):
        raise ValueError("Dead semantic input requires proof and explicit elimination")
    mapping, nodes = {}, []
    for i, n in enumerate(c.nodes):
        if i not in live:
            continue
        mapping[i] = len(nodes)
        nodes.append(list(n) if n[0] in ("c", "v") else [n[0], *[mapping[j] for j in n[1:]]])
    return {
        "format": "mixed-integer-arithmetic-dag-v1",
        "variable_names": c.vars,
        "unrestricted_inputs": sorted(c.unrestricted),
        "nonnegative_inputs": sorted(set(range(len(c.vars))) - c.unrestricted),
        "nodes": nodes,
        "equalities": [[mapping[a], mapping[b], label] for a, b, label in c.eqs],
        "calls": dict(c.calls),
        "inferred_nonnegative_inputs": sorted(c.inferred_nonnegative),
        "sign_inference": [{**r, **{k: mapping[v] for k, v in r.items() if k.endswith("_node")}} for r in c.sign_inference],
    }

def flatten(circuit, max_affine_terms=16):
    forms, rows = [], []
    ninputs = len(circuit["variable_names"])
    nvar = ninputs
    wire_map = {}
    nonlinear_wires = 0
    affine_barriers = 0
    for ni, n in enumerate(circuit["nodes"]):
        op = n[0]
        if op == "c":
            a = {(): n[1]} if n[1] else {}
        elif op == "v":
            a = {(n[1],): 1}
        elif op in ("a", "s"):
            a = sparse.add(forms[n[1]], forms[n[2]], 1 if op == "a" else -1)
        else:
            p = sparse.mul(forms[n[1]], forms[n[2]])
            if any(len(mon) > 1 for mon in p):
                a = {(nvar,): 1}
                wire_map[ni] = nvar
                nvar += 1
                nonlinear_wires += 1
                rows.append({"label": "nonlinear gate " + str(ni), "terms": sparse.enc(sparse.add(a, p, -1))})
            else:
                a = p
        if max_affine_terms and len(a) > max_affine_terms:
            p = a
            a = {(nvar,): 1}
            wire_map[ni] = nvar
            nvar += 1
            affine_barriers += 1
            rows.append({"label": "affine support barrier " + str(ni), "terms": sparse.enc(sparse.add(a, p, -1))})
        forms.append(a)
    for left, right, label in circuit["equalities"]:
        rows.append({"label": label, "terms": sparse.enc(sparse.add(forms[left], forms[right], -1))})
    for j in circuit["nonnegative_inputs"]:
        aa, bb, cc = nvar, nvar + 1, nvar + 2
        nvar += 3
        p = {(j,): 1, (aa, aa): -1, (bb, bb): -1, (cc, cc): -1, (cc,): -1}
        rows.append({"label": "semantic nonnegativity " + str(j), "terms": sparse.enc(p)})
    final = collections.defaultdict(int)
    for row in rows:
        p = {tuple(mon): coef for coef, mon in row["terms"]}
        if max(map(len, p), default=0) > 2:
            raise ValueError("Residual is not quadratic")
        for mon, coef in sparse.mul(p, p).items():
            final[mon] += coef
    final = {mon: coef for mon, coef in final.items() if coef}
    degree = max(map(len, final))
    used = {j for mon in final for j in mon}
    if degree != 4 or used != set(range(nvar)):
        raise ValueError("Degree or variable liveness failure")
    polynomial = {"format": "ordinary-polynomial-sparse-v1", "domain": "unrestricted integers", "variable_count": nvar, "terms": sparse.enc(final)}
    summary = {
        "domain": "unrestricted integers",
        "ordinary_polynomial_variables": nvar,
        "ordinary_polynomial_degree": degree,
        "ordinary_polynomial_monomials": len(final),
        "input_existentials": ninputs,
        "unrestricted_semantic_inputs": len(circuit["unrestricted_inputs"]),
        "nonnegative_semantic_inputs": len(circuit["nonnegative_inputs"]),
        "nonlinear_wires": nonlinear_wires,
        "retained_affine_wires": affine_barriers,
        "max_substituted_affine_terms": max_affine_terms,
        "nonnegativity_witnesses": 3 * len(circuit["nonnegative_inputs"]),
        "SOS_residuals": len(rows),
        "max_abs_coefficient": max(map(abs, final.values())),
        "largest_residual_support": max(len(row["terms"]) for row in rows),
        "calls": circuit["calls"],
    }
    return rows, polynomial, summary

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=pathlib.Path)
    args = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parent
    builder = root / "source" / "build_direct.py"
    output_path = args.output if args.output else root / "equations"
    spec = importlib.util.spec_from_file_location("source_compiler", builder)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    c, row, output, binding = module.build_circuit(signed_class(module.Compiler, True))
    circuit = prune(c)
    rows, polynomial, summary = flatten(circuit, 16)
    summary["source_builder_sha256"] = hashlib.sha256(builder.read_bytes()).hexdigest()
    summary["infer_quotient_signs"] = True
    row_source = {"variables": row.vars, "nodes": row.nodes, "output": output}
    output_path.mkdir(parents=True, exist_ok=True)
    for name, obj in [("circuit_integer.json", circuit), ("residuals_integer.json", rows), ("equation_integer.json", polynomial), ("summary_integer.json", summary), ("row_source.json", row_source)]:
        sparse.dump(output_path / name, obj)
    sparse.dump(output_path / "source_circuit_before_pruning.json", {
        "format": "mixed-integer-arithmetic-dag-v1", "variable_names": c.vars,
        "unrestricted_inputs": sorted(c.unrestricted), "nodes": c.nodes,
        "equalities": c.eqs, "source_binding": binding,
        "call_ledger": c.ledger,
    })
    print(json.dumps(summary, indent=2))

if __name__ == "__main__":
    main()
