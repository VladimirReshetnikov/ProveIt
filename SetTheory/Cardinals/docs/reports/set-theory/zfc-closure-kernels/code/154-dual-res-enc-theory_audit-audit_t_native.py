#!/usr/bin/env python3
"""Bind the independent T+B countermodel audit to literal Rocq source terms.

This checks source AST identities, arithmetic constructor declarations, and
the complete rule inventory.  It is not a formal proof of the countermodel.
No Python packages outside the standard library are needed.

Usage:
  python3 audit_t_native.py --codes222 Codes222.v --codes230 Codes230.v \
      --kcode230 KCode230.v --thm222 Thm222.v --enum222 Enum222.v \
      --receipt audit_t_native_receipt.json
"""

import argparse
import hashlib
import json
import re
from pathlib import Path


ARITY = {
    "wim": 2, "wel": 2, "wal": 2, "weq": 2,
    "wn": 1, "wex": 2, "vrel": 3, "nks222": 3,
}


def strip_comments(text):
    # Coq permits nested comments.
    depth, i, out = 0, 0, []
    while i < len(text):
        if text[i:i + 2] == "(*":
            depth += 1
            i += 2
        elif text[i:i + 2] == "*)":
            assert depth, "Unmatched comment terminator"
            depth -= 1
            i += 2
        else:
            if not depth:
                out.append(text[i])
            i += 1
    assert depth == 0, "Unclosed comment"
    return "".join(out)


def definition(text, name):
    pattern = rf"\bDefinition\s+{re.escape(name)}\b[^.]*?:=\s*([^.]*)\."
    hit = re.search(pattern, strip_comments(text))
    assert hit, f"Missing definition {name}"
    return " ".join(hit.group(1).split())


def parse(term):
    tokens = re.findall(r"[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[()]", term)
    assert "".join(tokens) == re.sub(r"\s+", "", term), term
    pos = 0

    def one():
        nonlocal pos
        tok = tokens[pos]
        pos += 1
        if tok == "(":
            ans = one()
            assert tokens[pos] == ")", (term, pos)
            pos += 1
            return ans
        assert tok != ")", (term, pos)
        if tok in ARITY:
            return (tok, *(one() for _ in range(ARITY[tok])))
        return tok

    ans = one()
    assert pos == len(tokens), (term, pos, tokens[pos:])
    return ans


def I(a, b):
    return ("wim", a, b)


def R(a, b):
    return ("wel", a, b)


def Q(a, b):
    return ("wal", a, b)


def E(a, b):
    return ("weq", a, b)


def N(a):
    return I(a, "F")


def X(a, b):
    return N(Q(a, N(b)))


def substitute(tree, env):
    if isinstance(tree, str):
        return env.get(tree, tree)
    return (tree[0], *(substitute(x, env) for x in tree[1:]))


def expand(tree, defs):
    if isinstance(tree, str):
        return tree
    op, *args = tree
    args = [expand(x, defs) for x in args]
    if op == "wn":
        return N(*args)
    if op == "wex":
        return X(*args)
    if op in ("vrel", "nks222"):
        return expand(substitute(defs[op], dict(zip("abc", args))), defs)
    return (op, *args)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for name in ("codes222", "codes230", "kcode230", "thm222", "enum222"):
        ap.add_argument("--" + name, required=True, type=Path)
    ap.add_argument("--receipt", required=True, type=Path)
    args = ap.parse_args()
    sources = {}
    texts = {}
    for name in ("codes222", "codes230", "kcode230", "thm222", "enum222"):
        path = getattr(args, name)
        raw = path.read_bytes()
        texts[name] = raw.decode()
        sources[name] = {"file": path.name, "sha256": hashlib.sha256(raw).hexdigest()}

    expected_arithmetic = {
        "P": "tri (a + b) + b",
        "wim": "4 * P a b",
        "wel": "4 * P i j + 1",
        "wal": "4 * P i a + 2",
        "weq": "4 * P i j + 3",
        "F": "1",
        "wn": "wim a F",
        "wex": "wn (wal x (wn a))",
    }
    for name, expected in expected_arithmetic.items():
        assert definition(texts["kcode230"], name) == expected, name
    tri = "Fixpoint tri (n : nat) : nat := match n with 0 => 0 | S m => S m + tri m end."
    assert tri in " ".join(strip_comments(texts["kcode230"]).split())

    a, b, c, u = "a", "b", "c", "u"
    logical = {
        "rho1": X(a, E(a, b)),
        "rho2": I(Q(a, I(b, c)), I(Q(a, b), Q(a, c))),
        "rho3": I(E(a, b), I(R(c, a), R(c, b))),
        "rho4": I(Q(a, Q(b, c)), Q(b, Q(a, c))),
        "rho5": I(E(c, a), I(R(c, b), R(a, b))),
        "rho6": I(X(a, Q(a, b)), b),
        "rho8": I(I(I(c, u), a), I(I(a, c), I(b, c))),
    }
    for name, expected in logical.items():
        assert expand(parse(definition(texts["codes230"], name)), {}) == expected, name

    # Independently assemble the exact helper expansion used in the proof.
    r = R(b, c)
    s = Q(c, I(R(c, a), R(c, b)))
    w = Q(b, I(c, N(Q(b, I(c, N(r))))))
    uu = Q(a, I(s, w))
    h = Q(b, I(r, N(Q(a, I(c, N(uu))))))
    k = Q(c, I(h, N(w)))
    v = I(R(a, b), Q(c, R(a, b)))
    g = I(E(c, a), I(E(c, b), Q(R(a, b), E(a, b))))
    defs = {name: parse(definition(texts["codes222"], name))
            for name in ("growG", "vrel", "nks222", "bundle222")}
    for name, expected in {"growG": g, "vrel": v, "nks222": k,
                           "bundle222": N(I(v, k))}.items():
        assert expand(defs[name], defs) == expected, name

    # Bind ALL rule clauses, not just their names.
    thm = " ".join(strip_comments(texts["thm222"]).split())
    clauses = thm.split("Inductive thm222 : nat -> Prop :=", 1)[1].rstrip(".").strip()
    clauses = [clause.strip() for clause in clauses.split("|") if clause.strip()]
    expected_clauses = [
        "W_true : thm222 0",
        "W_mp t b : thm222 t -> thm222 (wim t b) -> thm222 b",
        "W_gen a h : thm222 h -> thm222 (wal a h)",
        "W_r1 a b : thm222 (rho1 a b)",
        "W_r2 a b c : thm222 (rho2 a b c)",
        "W_r3 a b c : thm222 (rho3 a b c)",
        "W_r4 a b c : thm222 (rho4 a b c)",
        "W_r5 a b c : thm222 (rho5 a b c)",
        "W_r6 a b : thm222 (rho6 a b)",
        "W_rG a b c : thm222 (growG a b c)",
        "W_r8 a b c u : thm222 (rho8 a b c u)",
        "W_bundle a b c : c <> a -> c <> b -> thm222 (bundle222 a b c)",
    ]
    assert clauses == expected_clauses, clauses
    enum = " ".join(strip_comments(texts["enum222"]).split())
    gate = "Definition gate (a b c : nat) : nat := if Nat.eqb c a || Nat.eqb c b then 0 else bundle222 a b c."
    assert gate in enum

    receipt = {
        "status": "EXACT_NATIVE_SOURCE_BINDING_PASS",
        "scope": "AST equality and source rule binding only; independent mathematical audit is in T_COUNTERMODEL_AUDIT.md.",
        "sources": sources,
        "constructor_declarations_checked": len(expected_arithmetic) + 1,
        "logical_row_asts_checked": list(logical),
        "seed_calculus_asts_checked": list(defs),
        "full_rule_clauses_checked": len(clauses),
        "gate_checked": True,
    }
    args.receipt.write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
