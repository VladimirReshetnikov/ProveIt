#!/usr/bin/env python3
"""Finite, independent controls for the clause and assignment interfaces.

These checks are not finite models of K_cl (which has no finite models),
and do not prove consistency, compiler correctness, or a machine state bound.
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
import re
import time
from pathlib import Path

import finite_kernel as fk


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def epsc_exhaustive(max_n=3):
    """Compare EPSC directly with six-clause witnesses on all E,R of size <=n.

    E and R are independent binary relations. This isolates the logical
    transformation of B5; the assignment/class axioms are not imposed.
    A global Pick is chosen once for each E and works for every R.
    """
    counts = []
    true_instances = 0
    witness_replays = 0
    for n in range(1, max_n + 1):
        values = range(n)
        count = 0
        for e_bits in range(1 << (n * n)):
            members = [sum(((e_bits >> (z * n + x)) & 1) << z for z in values) for x in values]
            pick = [next((z for z in values if (members[x] >> z) & 1), 0) for x in values]
            for r_bits in range(1 << (n * n)):
                rows = [(r_bits >> (x * n)) & ((1 << n) - 1) for x in values]
                outputs = 0
                for row in rows:
                    outputs |= row
                input_bounds = []
                for x in values:
                    union = 0
                    for y in values:
                        if (rows[x] >> y) & 1:
                            union |= members[y]
                    input_bounds.append([q for q in values if union & ~members[q] == 0])
                bounded = all(input_bounds)
                hulls = []
                for h in values:
                    active = [x for x in values if members[x] == 0 or (members[h] >> x) & 1]
                    if members[h] & ~outputs == 0 and all(rows[x] & ~members[h] == 0 for x in active):
                        hulls.append(h)
                original = not bounded or bool(hulls)

                # Independent clause-side existence: test the bad alternative
                # by individual (output, member) witnesses for EVERY q, and the
                # hull alternative via literal booleans and existential Sup.
                bads = []
                for a in values:
                    if all(any(((rows[a] >> y) & 1) and (members[y] & ~members[q])
                               for y in values) for q in values):
                        bads.append(a)
                clause_hulls = []
                for h in values:
                    good = True
                    for x, y in itertools.product(values, repeat=2):
                        rel = bool((rows[x] >> y) & 1)
                        eh_y = bool((members[h] >> y) & 1)
                        initial = bool((members[x] >> pick[x]) & 1) or not rel or eh_y
                        recurrent = not bool((members[h] >> x) & 1) or not rel or eh_y
                        if not initial or not recurrent:
                            good = False
                            break
                    support = all(not ((members[h] >> y) & 1) or any((rows[x] >> y) & 1 for x in values)
                                  for y in values)
                    if good and support:
                        clause_hulls.append(h)
                transformed = bool(bads or clause_hulls)
                check(original == transformed, (n, e_bits, r_bits, "EPSC/CNF"))
                check(hulls == clause_hulls, (n, e_bits, r_bits, "hull witnesses"))
                if original:
                    true_instances += 1
                    # Explicit phase reuse: one Target and one Next table.
                    g = bounded
                    target = hulls[0] if g else bads[0]
                    next_values, mem_values = [], []
                    for q in values:
                        if g:
                            next_values.append(next((x for x in values if (rows[x] >> q) & 1), 0))
                            mem_values.append(0)
                        else:
                            y = next(y for y in values if ((rows[target] >> y) & 1) and members[y] & ~members[q])
                            z = next(z for z in values if ((members[y] & ~members[q]) >> z) & 1)
                            next_values.append(y)
                            mem_values.append(z)
                    for q in values:
                        check(g or bool((rows[target] >> next_values[q]) & 1), "bad relation")
                        check(g or bool((members[next_values[q]] >> mem_values[q]) & 1), "bad member")
                        check(g or not bool((members[q] >> mem_values[q]) & 1), "bad bound")
                    for x, y in itertools.product(values, repeat=2):
                        rel = bool((rows[x] >> y) & 1)
                        eh_y = bool((members[target] >> y) & 1)
                        check(not g or bool((members[x] >> pick[x]) & 1) or not rel or eh_y, "initial")
                        check(not g or not bool((members[target] >> x) & 1) or not rel or eh_y, "recurrent")
                        check(not g or not eh_y or bool((rows[next_values[y]] >> y) & 1), "support")
                    witness_replays += 1
                count += 1
        counts.append({"domain_size": n, "relation_pairs": count})
    return {"cases": counts, "true_instances": true_instances, "witness_replays": witness_replays,
            "scope": "B5 equivalence only; no full-theory finite models"}


def assignment_controls():
    """Two independent semantics of the finite formula-representation step."""
    rng = random.Random(16102026)
    formulas = [("atom", 0, 1), ("atom", 1, 0), ("exists", 3, ("atom", 0, 3)),
                ("exists", 0, ("nand", ("atom", 0, 1), ("atom", 2, 0))),
                ("exists", 1, ("exists", 1, ("atom", 0, 1)))]

    def random_formula(depth):
        if depth == 0 or rng.randrange(4) == 0:
            return ("atom", rng.randrange(4), rng.randrange(4))
        if rng.randrange(2):
            return ("nand", random_formula(depth - 1), random_formula(depth - 1))
        return ("exists", rng.randrange(4), random_formula(depth - 1))

    formulas.extend(random_formula(4) for _ in range(35))
    n = 2
    assignments = list(itertools.product(range(n), repeat=4))
    index = {a: i for i, a in enumerate(assignments)}
    all_mask = (1 << len(assignments)) - 1
    checks = 0
    packed_checks = 0
    for e_bits in range(1 << (n * n)):
        def relation(x, y):
            return bool((e_bits >> (x * n + y)) & 1)

        def direct(f, env):
            if f[0] == "atom":
                return relation(env[f[1]], env[f[2]])
            if f[0] == "nand":
                return not (direct(f[1], env) and direct(f[2], env))
            for z in range(n):
                changed = list(env)
                changed[f[1]] = z
                if direct(f[2], changed):
                    return True
            return False

        cache = {}

        def class_code(f):
            if f in cache:
                return cache[f]
            if f[0] == "atom":
                mask = sum(int(relation(a[f[1]], a[f[2]])) << i for i, a in enumerate(assignments))
            elif f[0] == "nand":
                mask = all_mask ^ (class_code(f[1]) & class_code(f[2]))
            else:
                source = class_code(f[2])
                mask = 0
                for i, a in enumerate(assignments):
                    for z in range(n):
                        changed = list(a)
                        changed[f[1]] = z
                        if (source >> index[tuple(changed)]) & 1:
                            mask |= 1 << i
                            break
            cache[f] = mask
            return mask

        for f in formulas:
            code = class_code(f)
            for i, env in enumerate(assignments):
                check(direct(f, env) == bool((code >> i) & 1), "class representation")
                checks += 1
            # A code is metadata in the original b[0]. After both argument
            # updates it is no longer there; the outer projection retains it.
            for p, v3, x, y in itertools.product(range(n), repeat=4):
                base = [code, 0, p, v3]
                saved = base[0]
                changed = list(base)
                changed[0], changed[1] = x, y
                check(bool((saved >> index[tuple(changed)]) & 1) == direct(f, changed), "packed original projection")
                packed_checks += 1
    return {"formula_count": len(formulas), "relations": 16,
            "assignment_evaluations": checks, "packed_evaluations": packed_checks,
            "scope": "finite syntax/assignment controls, not one-sorted K_cl models"}


def ground_controls():
    c, d = fk.term("c"), fk.term("d")
    f = lambda x: fk.term("f", x)
    p, n = fk.positive, fk.negative
    cases = [
        ("empty theory", (), True), ("empty clause", ((),), False),
        ("reflexivity", ((n("=", c, c),),), False),
        ("distinct constants", ((n("=", c, d),),), True),
        ("function congruence", ((p("=", c, d),), (n("=", f(c), f(d)),)), False),
        ("predicate congruence first coordinate", ((p("=", c, d),), (p("E", c, c),), (n("E", d, c),)), False),
        ("predicate congruence second coordinate", ((p("=", c, d),), (p("E", c, c),), (n("E", c, d),)), False),
        ("cyclic denotation permitted", ((p("=", c, f(c)),),), True),
        ("nontrivial Boolean split", ((p("P", c), p("Q", c)), (n("P", c),), (n("Q", c),)), False),
    ]
    for name, clauses, expected in cases:
        result = fk.ground_satisfiable(clauses)
        check((result is not None) == expected, name)
    # Exact independent finite-model enumeration for the three atoms
    # c=d, E(c,c), E(d,c), across all 3^3 unit/absent choices.
    atoms = [("=", c, d), ("E", c, c), ("E", d, c)]
    brute_count = 0
    for choices in itertools.product((-1, 0, 1), repeat=3):
        clauses = tuple((fk.literal(choice == 1, *atom),) for choice, atom in zip(choices, atoms) if choice)
        model_exists = False
        for equal in (False, True):
            for ec, ed in itertools.product((False, True), repeat=2):
                if equal and ec != ed:
                    continue
                vals = (equal, ec, ed)
                if all(choice == 0 or (choice == 1) == value for choice, value in zip(choices, vals)):
                    model_exists = True
        check((fk.ground_satisfiable(clauses) is not None) == model_exists, "independent finite model comparison")
        brute_count += 1
    # Actual NAND rows refute N(c,c)=c, using a nonempty-domain ground s=c.
    payload = fk.build()
    subs = {"a": c, "b": c, "s": c}
    nand = [fk.instantiate(payload["clauses"][i]["literals"], subs) for i in (2, 3, 4)]
    check(fk.ground_satisfiable((*nand, (p("=", fk.term("N", c, c), c),))) is None,
          "selector distinction from actual clauses")
    return {"named_controls": len(cases), "independent_unit_sets": brute_count,
            "actual_NAND_distinction": True, "whole_kernel_search_run": False}


def tptp_roundtrips(data_dir):
    """Reparse generated CNF with an independent restricted TPTP parser."""
    token_re = re.compile(r"[A-Za-z][A-Za-z0-9_]*|!=|[(),.|~=]")
    completed = 0
    for path in sorted(data_dir.glob("*.p")):
        payload = json.loads(path.with_suffix(".json").read_text())
        reverse = {("c0" if n == "c" else "upd" if n == "C" else n.lower()): n for n in payload["signature"]}
        rel_reverse = {r.lower(): r for r in payload["relations"]}
        parsed = []
        for line in path.read_text().splitlines():
            if line.startswith("%"):
                continue
            toks = token_re.findall(line)
            cursor = 0

            def take(value=None):
                nonlocal cursor
                tok = toks[cursor]
                cursor += 1
                if value is not None:
                    check(tok == value, "TPTP token " + str((tok, value)))
                return tok

            def args():
                take("(")
                result = [read_term()]
                while toks[cursor] == ",":
                    take(",")
                    result.append(read_term())
                take(")")
                return result

            def read_term():
                name = take()
                if name[0].isupper():
                    return fk.variable(name.lower())
                children = args() if cursor < len(toks) and toks[cursor] == "(" else []
                return fk.term(reverse[name], *children)

            take("cnf"); take("("); take(); take(","); take("axiom"); take(","); take("(")
            clause = []
            while True:
                sign = True
                if toks[cursor] == "~":
                    take("~")
                    sign = False
                if toks[cursor] in rel_reverse and toks[cursor] != "=":
                    rel = rel_reverse[take()]
                    clause.append(fk.literal(sign, rel, *args()))
                else:
                    left = read_term()
                    op = take()
                    check(op in ("=", "!="), "equality operator")
                    right = read_term()
                    clause.append(fk.literal(op == "=", "=", left, right))
                if toks[cursor] != "|":
                    break
                take("|")
            take(")"); take(")"); take(".")
            check(cursor == len(toks), "TPTP exact EOF")
            parsed.append(clause)
        expected = [row["literals"] for row in payload["clauses"]]
        check(json.dumps(parsed) == json.dumps(expected), "TPTP payload roundtrip " + path.name)
        completed += 1
    return completed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="relations through size 2; full defaults through size 3")
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parents[1] / "data")
    args = parser.parse_args()
    started = time.monotonic()
    args.out.mkdir(parents=True, exist_ok=True)
    metrics = []
    for packed in (False, True):
        for branch in ("direct", "predicate", "equality"):
            metrics.append(fk.write_payload(fk.build(packed, branch), args.out))
    for branch in ("direct", "predicate"):
        for strategy in ("shared", "packed", "slice"):
            metrics.append(fk.write_payload(fk.compress(fk.build(True, branch), strategy), args.out))
    for strategy in ("shared", "packed"):
        metrics.append(fk.write_payload(fk.compress(fk.build(True, "equality"), strategy), args.out))
    metrics.append(fk.write_payload(fk.compress(fk.build(), "shared", False), args.out))
    (args.out / "kernel_metrics.json").write_text(json.dumps(metrics, indent=2) + "\n")
    report = {"status": "finite checks passed", "not_a_formal_consistency_proof": True,
              "tptp_roundtrips": tptp_roundtrips(args.out),
              "ground_controls": ground_controls(),
              "assignment_controls": assignment_controls(),
              "closure_controls": epsc_exhaustive(2 if args.quick else 3)}
    report["seconds"] = round(time.monotonic() - started, 3)
    (args.out / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
