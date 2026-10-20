#!/usr/bin/env python3
"""Construct a closed Hilbert derivation of the K-bundle normalization.

The basis is K/S/Peirce (derived from rho8 in upstream CD230.v), rho2, and
rho6. No set-theory axiom or unproved congruence rule enters this certificate.
Output is data for the independent checker check_fusion_certificate.py.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


class Builder:
    def __init__(self):
        self.terms = []
        self.term_ids = {}
        self.proofs = []
        self.proof_ids = {}
        self.dependencies = []
        self.deduction_cache = {}
        self.identity_cache = {}
        self.dne_cache = {}
        self.dni_cache = {}
        self.efq_cache = {}
        self.norm_cache = {}
        self.F = self.term("F")

    def term(self, *key):
        if key not in self.term_ids:
            self.term_ids[key] = len(self.terms)
            self.terms.append(key)
        return self.term_ids[key]

    def I(self, a, b):
        return self.term("I", a, b)

    def Q(self, x, a):
        return self.term("Q", x, a)

    def N(self, a):
        return self.I(a, self.F)

    def And(self, a, b):
        return self.N(self.I(a, self.N(b)))

    def Ex(self, x, a):
        return self.N(self.Q(x, self.N(a)))

    def proof(self, rule, form, refs=(), args=(), deps=frozenset()):
        key = rule, form, tuple(refs), tuple(args)
        if key not in self.proof_ids:
            self.proof_ids[key] = len(self.proofs)
            self.proofs.append({"rule": rule, "formula": form,
                                "refs": list(refs), "args": list(args)})
            self.dependencies.append(deps)
        return self.proof_ids[key]

    def hyp(self, a):
        return self.proof("hyp", a, deps=frozenset([a]))

    def k(self, a, b):
        return self.proof("K", self.I(a, self.I(b, a)), args=(a, b))

    def s(self, a, b, c):
        form = self.I(self.I(a, self.I(b, c)),
                      self.I(self.I(a, b), self.I(a, c)))
        return self.proof("S", form, args=(a, b, c))

    def p(self, a, b):
        return self.proof("P", self.I(self.I(self.I(a, b), a), a),
                          args=(a, b))

    def rho2(self, x, a, b):
        form = self.I(self.Q(x, self.I(a, b)),
                      self.I(self.Q(x, a), self.Q(x, b)))
        return self.proof("rho2", form, args=(x, a, b))

    def rho6(self, x, a):
        return self.proof("rho6", self.I(self.Ex(x, self.Q(x, a)), a),
                          args=(x, a))

    def mp(self, p, q):
        # p proves A, q proves A -> B.
        a = self.proofs[p]["formula"]
        t = self.terms[self.proofs[q]["formula"]]
        if t[0] != "I" or t[1] != a:
            raise ValueError("invalid generated modus ponens")
        return self.proof("mp", t[2], refs=(p, q),
                          deps=self.dependencies[p] | self.dependencies[q])

    def gen(self, x, p):
        if self.dependencies[p]:
            raise ValueError("only theorems may be generalized")
        return self.proof("gen", self.Q(x, self.proofs[p]["formula"]),
                          refs=(p,), args=(x,))

    def identity(self, a):
        if a not in self.identity_cache:
            q = self.mp(self.k(a, self.I(a, a)), self.s(a, self.I(a, a), a))
            self.identity_cache[a] = self.mp(self.k(a, a), q)
        return self.identity_cache[a]

    def deduce(self, h, p):
        key = h, p
        if key in self.deduction_cache:
            return self.deduction_cache[key]
        item = self.proofs[p]
        a = item["formula"]
        if h not in self.dependencies[p]:
            result = self.mp(p, self.k(a, h))
        elif item["rule"] == "hyp":
            if a != h:
                raise ValueError("bad hypothesis dependency")
            result = self.identity(h)
        elif item["rule"] == "mp":
            left, right = item["refs"]
            middle = self.proofs[left]["formula"]
            lifted_right = self.deduce(h, right)
            lifted_left = self.deduce(h, left)
            result = self.mp(lifted_left,
                             self.mp(lifted_right, self.s(h, middle, a)))
        else:
            raise ValueError("theorem rule depends on a hypothesis")
        if self.proofs[result]["formula"] != self.I(h, a):
            raise ValueError("deduction conclusion mismatch")
        self.deduction_cache[key] = result
        return result

    def efq(self, a):
        if a not in self.efq_cache:
            h = self.hyp(self.F)
            q = self.Q(0, self.N(self.Q(0, a)))
            ex = self.mp(h, self.k(self.F, q))
            self.efq_cache[a] = self.deduce(self.F, self.mp(ex, self.rho6(0, a)))
        return self.efq_cache[a]

    def dni(self, a):
        if a not in self.dni_cache:
            p = self.mp(self.hyp(a), self.hyp(self.N(a)))
            self.dni_cache[a] = self.deduce(a, self.deduce(self.N(a), p))
        return self.dni_cache[a]

    def dne(self, a):
        if a not in self.dne_cache:
            na, nna = self.N(a), self.N(self.N(a))
            false = self.mp(self.hyp(na), self.hyp(nna))
            under = self.mp(false, self.efq(a))
            arrow = self.deduce(na, under)
            result = self.mp(arrow, self.p(a, self.F))
            self.dne_cache[a] = self.deduce(nna, result)
        return self.dne_cache[a]

    def trans(self, ab, bc):
        fa, fb = self.terms[self.proofs[ab]["formula"]], self.terms[self.proofs[bc]["formula"]]
        if fa[0] != "I" or fb[0] != "I" or fa[2] != fb[1]:
            raise ValueError("transitivity premise mismatch")
        return self.deduce(fa[1], self.mp(self.mp(self.hyp(fa[1]), ab), bc))

    def imp_congruence(self, a, b, af, ab, c, d, cf, cb):
        # af:A->B, ab:B->A, cf:C->D, cb:D->C.
        old, new = self.I(a, c), self.I(b, d)
        inner = self.mp(self.mp(self.mp(self.hyp(b), ab), self.hyp(old)), cf)
        forward = self.deduce(old, self.deduce(b, inner))
        inner = self.mp(self.mp(self.mp(self.hyp(a), af), self.hyp(new)), cb)
        backward = self.deduce(new, self.deduce(a, inner))
        return old, new, forward, backward

    def all_congruence(self, x, old, new, forward, backward):
        pf = self.mp(self.gen(x, forward), self.rho2(x, old, new))
        pb = self.mp(self.gen(x, backward), self.rho2(x, new, old))
        return self.Q(x, old), self.Q(x, new), pf, pb

    def normalize(self, original):
        if original in self.norm_cache:
            return self.norm_cache[original]
        t = self.terms[original]
        if t[0] == "I":
            a, b, af, ab = self.normalize(t[1])
            c, d, cf, cb = self.normalize(t[2])
            if a == b and c == d:
                item = original, original, self.identity(original), self.identity(original)
            else:
                item = self.imp_congruence(a, b, af, ab, c, d, cf, cb)
        elif t[0] == "Q":
            _, new, pf, pb = self.normalize(t[2])
            if new == t[2]:
                item = original, original, self.identity(original), self.identity(original)
            else:
                item = self.all_congruence(t[1], t[2], new, pf, pb)
        else:
            item = original, original, self.identity(original), self.identity(original)
        old, mid, pf, pb = item
        mt = self.terms[mid]
        if mt[0] == "I" and mt[2] == self.F:
            inner = self.terms[mt[1]]
            if inner[0] == "I" and inner[2] == self.F:
                target = inner[1]
                item = old, target, self.trans(pf, self.dne(target)), self.trans(self.dni(target), pb)
        self.norm_cache[original] = item
        return item

    def export(self, roots, original, fused):
        needed = set()
        def visit(n):
            if n in needed:
                return
            for r in self.proofs[n]["refs"]:
                visit(r)
            needed.add(n)
        for n in roots:
            visit(n)
        ordered = sorted(needed)
        renaming = {n: i for i, n in enumerate(ordered)}
        proofs = []
        for n in ordered:
            item = dict(self.proofs[n])
            if self.dependencies[n]:
                raise ValueError("exported proof has a hypothesis")
            item["refs"] = [renaming[r] for r in item["refs"]]
            proofs.append(item)
        return {"format": "k-fusion-hilbert-v1", "terms": self.terms,
                "proofs": proofs, "endpoints": [renaming[r] for r in roots],
                "old_bundle": original, "fused_bundle": fused,
                "basis_note": "K,S,P are the upstream CD230 derived schemas; rho2/rho6 are retained literal logical rows."}


def make_bundle(B, equality_binder="k"):
    a, b, k = "a", "b", "k"
    m = B.term("meta", "m")
    rel = lambda x, y: B.term("Rel", x, y)
    eq = lambda x, y: B.term("Eq", x, y)
    r = rel(b, k)
    subset = B.Q(k, B.I(rel(k, a), rel(k, b)))
    request = B.Q(b, B.I(m, B.Ex(b, B.And(m, r))))
    support = B.Ex(a, B.And(m, B.Q(a, B.I(subset, request))))
    closure = B.Q(b, B.I(r, support))
    core = B.Ex(k, B.And(B.I(m, r), closure))
    vr = B.I(rel(a, b), B.Q(k, rel(a, b)))
    ve = B.I(eq(a, b), B.Q(equality_binder, eq(a, b)))
    old = B.And(core, B.And(vr, ve))
    # Independently stated target, corresponding to fused_k_theory.md.
    W = B.Q(b, B.I(m, B.N(B.Q(b, B.I(m, B.N(r))))))
    U = B.Q(a, B.I(subset, W))
    H = B.Q(b, B.I(r, B.N(B.Q(a, B.I(m, B.N(U))))))
    Kf = B.N(B.Q(k, B.I(B.I(m, r), B.N(H))))
    target = B.N(B.I(Kf, B.I(vr, B.N(ve))))
    return old, target


def term_census(B, t):
    result = {"implications": 0, "quantifiers": 0, "falsity_occurrences": 0,
              "meta_occurrences": 0, "membership_occurrences": 0, "equality_occurrences": 0}
    def walk(n):
        x = B.terms[n]
        if x[0] == "I":
            result["implications"] += 1
            walk(x[1]); walk(x[2])
        elif x[0] == "Q":
            result["quantifiers"] += 1
            walk(x[2])
        else:
            key = {"F": "falsity_occurrences", "meta": "meta_occurrences",
                   "Rel": "membership_occurrences", "Eq": "equality_occurrences"}[x[0]]
            result[key] += 1
    walk(t)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("fusion_certificate.json"))
    parser.add_argument("--equality-binder", default="k",
                        help="Independent schematic equality-vacuity binder; use kappa for the Rel-code helper.")
    options = parser.parse_args()
    B = Builder()
    old, target = make_bundle(B, options.equality_binder)
    _, normal, forward, backward = B.normalize(old)
    if normal != target:
        raise ValueError("normal form differs from independently specified fused bundle")
    data = B.export((forward, backward), old, target)
    if options.equality_binder != "k":
        data["equality_binder"] = options.equality_binder
    data["old_census"] = term_census(B, old)
    data["new_census"] = term_census(B, target)
    options.output.write_text(json.dumps(data, separators=(",", ":")) + "\n")
    print(json.dumps({"certificate": str(options.output), "closed_proof_nodes": len(data["proofs"]),
                      "formula_dag_nodes": len(data["terms"]), "old": data["old_census"],
                      "new": data["new_census"]}, indent=2))


if __name__ == "__main__":
    main()
