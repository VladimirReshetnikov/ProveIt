#!/usr/bin/env python3
"""Finite symbolic certificate for the all-natural rotating-pop obstruction.

Each comparison follows only injectivity of the exact Cantor constructors
and disjoint remainder tags modulo four. No finite numeric sampling is used
to justify the quantified adjacency lemma. The transition-invariant proof
itself is in rotating_pop_obstruction.tex.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path


def I(a, b): return ("I", a, b)
def Q(a, b): return ("Q", a, b)
def E(a, b): return ("E", a, b)
def M(a, b): return ("M", a, b)
def N(a): return I(a, 1)
def Ex(a, b): return N(Q(a, N(b)))
TAG = {"I": 0, "M": 1, "Q": 2, "E": 3}


def tag(t):
    if isinstance(t, tuple): return TAG[t[0]]
    if isinstance(t, int): return t % 4
    return None


def unequal_certificate(a, b, path=()):
    """Find a tag contradiction under matching injective constructors."""
    ta, tb = tag(a), tag(b)
    if ta is not None and tb is not None and ta != tb:
        return {"path": list(path), "left_tag": ta, "right_tag": tb,
                "left": a, "right": b}
    if isinstance(a, tuple) and isinstance(b, tuple) and a[0] == b[0]:
        for k in (1, 2):
            result = unequal_certificate(a[k], b[k], path + (k,))
            if result is not None: return result
    return None


def main():
    a, b, c, u, h, t = "A", "B", "C", "U", "H", "T"
    r1 = Ex(a, E(a, b))
    r2 = I(Q(a, I(b, c)), I(Q(a, b), Q(a, c)))
    r3 = I(E(a, b), I(M(c, a), M(c, b)))
    r4 = I(Q(a, Q(b, c)), Q(b, Q(a, c)))
    r5 = I(E(c, a), I(M(c, b), M(a, b)))
    r6 = I(Ex(a, Q(a, c)), c)
    r7 = I(E(c, a), I(E(c, b), Q(M(a, b), E(a, b))))
    ell = I(I(I(c, u), a), I(I(a, c), I(b, c)))
    gen = Q(u, h)
    # Full seed-bundle tail retained literally, not replaced by an axiom.
    def B0(b_, k, matrix):
        return Q(b_, I(matrix, N(Q(b_, I(matrix, N(M(b_, k)))))))
    def S0(a_, b_, k):
        return Q(k, I(M(k, a_), M(k, b_)))
    def C0(a_, b_, k, matrix):
        return Q(b_, I(M(b_, k), N(Q(a_, I(matrix,
            N(Q(a_, I(S0(a_, b_, k), B0(b_, k, matrix)))))))))
    j = Q(c, I(C0(a, b, c, c), N(B0(b, c, c))))
    v = I(M(a, b), Q(c, M(a, b)))
    gate = N(I(v, j))
    spine = [gate, r1, r2, r3, r4, r5, r6, r7, ell, gen, t]
    names = ["G", "R1", "R2", "R3", "R4", "R5", "R6", "R7", "L", "GEN", "old_top"]
    proofs = []
    for k, (major, minor) in enumerate(zip(spine, spine[1:])):
        if tag(major) != 0:
            proof = {"kind": "major_tag", "major_tag": tag(major), "required_tag": 0}
        else:
            assert isinstance(major, tuple) and major[0] == "I"
            mismatch = unequal_certificate(major[1], minor)
            assert mismatch is not None, (names[k], names[k+1])
            proof = {"kind": "antecedent_injectivity", **mismatch}
        proofs.append({"pair": [names[k], names[k+1]], "proof": proof})
    assert len(proofs) == 10
    assert all(tag(x) in (0, 2) for x in spine[:-1])
    result = {
        "status": "ALL_TEN_LITERAL_ADJACENCY_OBSTRUCTIONS_PASS",
        "constructors": {"I": "4 P", "M": "4 P + 1", "Q": "4 P + 2", "E": "4 P + 3"},
        "proof_rule": "Matching constructor codes have equal arguments; differing tags cannot be equal.",
        "zero_major": "I(a,b)=0 iff a=b=0, so a zero major never has a positive consequent.",
        "generated_nonfalsity": "Every generated gate/row has tag 0; GEN has tag 2; falsity has tag 1.",
        "cases": proofs,
        "scope": "Finite symbolic adjacency certificate for all natural parameters. The command invariant, scheduler proof, and physical certificates are separate written obligations.",
        "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    out = Path(__file__).with_name("rotating_adjacency_result.json")
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "pairs": len(proofs), "output": str(out)}, indent=2))


if __name__ == "__main__": main()
