#!/usr/bin/env python3
"""Independent replay of two small propositional research certificates.

No finite-matrix result here claims anything about the entire CP/GIC theory.
The positive certificate upgrades the K/B/Peirce logical control only; it is
not a new binary machine or a compilation correctness certificate.
"""
import json
from itertools import product
from pathlib import Path


def parse(text):
    names = {}
    i = 0

    def go():
        nonlocal i
        c = text[i]
        i += 1
        if c == "C":
            return ("i", go(), go())
        if c == "F":
            return ("f",)
        assert c.islower(), (text, c)
        return ("v", names.setdefault(c, len(names)))

    result = go()
    assert i == len(text), text
    return result


def canonical(term):
    names = {}

    def go(t):
        if t[0] == "v":
            return ("v", names.setdefault(t[1], len(names)))
        if t[0] == "i":
            return ("i", go(t[1]), go(t[2]))
        assert t == ("f",)
        return t

    return go(term)


def rename(term, offset):
    if term[0] == "v":
        return ("v", term[1] + offset)
    if term[0] == "i":
        return ("i", rename(term[1], offset), rename(term[2], offset))
    return term


def detach(major, minor):
    assert major[0] == "i"
    subst = {}

    def resolve(t):
        while t[0] == "v" and t[1] in subst:
            t = subst[t[1]]
        return t

    def occurs(v, t):
        t = resolve(t)
        return (t == ("v", v) or
                (t[0] == "i" and (occurs(v, t[1]) or occurs(v, t[2]))))

    def unify(left, right):
        pending = [(left, right)]
        while pending:
            a, b = pending.pop()
            a, b = resolve(a), resolve(b)
            if a == b:
                continue
            if a[0] != "v" and b[0] == "v":
                a, b = b, a
            if a[0] == "v":
                assert not occurs(a[1], b), (a, b)
                subst[a[1]] = b
            else:
                assert a[0] == b[0] == "i", (a, b)
                pending.extend([(a[1], b[1]), (a[2], b[2])])

    def instantiate(t):
        t = resolve(t)
        if t[0] == "i":
            return ("i", instantiate(t[1]), instantiate(t[2]))
        return t

    unify(major[1], rename(minor, 1000))
    return canonical(instantiate(major[2]))


def replay_cd(path, axiom_strings=None, target_strings=None):
    if axiom_strings is None:
        axiom_strings = ["CpCqp", "CCpqCCqrCpr", "CCCpqpp"]
    if target_strings is None:
        target_strings = ["CCCpqrCCrpCsp", "CCpCqrCCpqCpr"]
    axioms = [parse(s) for s in axiom_strings]
    expected_targets = set(target_strings)
    nodes = {}
    targets = {}
    detachment_count = 0
    for line in path.read_text().splitlines():
        fields = line.split()
        if fields[0] == "N":
            _, number, major, minor, text = fields
            number, major, minor = map(int, [number, major, minor])
            assert number not in nodes
            term = parse(text)
            if major < 0:
                assert minor == -1 and 0 <= number < len(axioms)
                assert term == axioms[number]
            else:
                assert major < number and minor < number
                assert detach(nodes[major], nodes[minor]) == term
                detachment_count += 1
            nodes[number] = term
        else:
            assert fields[0] == "T" and len(fields) == 3
            _, target, number = fields
            number = int(number)
            assert target in expected_targets and target not in targets
            assert parse(target) == nodes[number]
            targets[target] = number
    assert set(targets) == expected_targets
    return {
        "initial_axioms": axiom_strings,
        "nodes": len(nodes),
        "detachment_steps": detachment_count,
        "targets": targets,
        "certificate": path.name,
        "result": "PASS",
    }


def matrix_obstruction():
    rows = [[3, 3, 3, 3], [3, 3, 0, 3],
            [3, 0, 3, 3], [0, 0, 0, 3]]
    n, top, falsity = 4, 3, 0
    C = lambda a, b: rows[a][b]
    assert C(top, top) == top
    axioms = {
        "K": (2, lambda a, b: C(a, C(b, a))),
        "I": (1, lambda a: C(a, a)),
        "EFQ": (1, lambda a: C(falsity, a)),
        "DNE": (1, lambda a: C(C(C(a, falsity), falsity), a)),
        "L_u_F": (3, lambda a, b, c:
                  C(C(C(c, falsity), a), C(C(a, c), C(b, c)))),
        "L_u_Truth": (3, lambda a, b, c:
                      C(C(C(c, top), a), C(C(a, c), C(b, c)))),
        "L_u_a": (3, lambda a, b, c:
                  C(C(C(c, a), a), C(C(a, c), C(b, c)))),
        "L_u_c": (3, lambda a, b, c:
                  C(C(C(c, c), a), C(C(a, c), C(b, c)))),
    }
    checks = {}
    for name, (arity, formula) in axioms.items():
        cases = list(product(range(n), repeat=arity))
        assert all(formula(*case) == top for case in cases), name
        checks[name] = len(cases)
    for a, b in product(range(n), repeat=2):
        assert a != top or C(a, b) != top or b == top
    p, q = 1, 2
    peirce = C(C(C(p, q), p), p)
    a, b, c = 1, 0, 2
    s = C(C(a, C(b, c)), C(C(a, b), C(a, c)))
    assert peirce == s == 0
    return {
        "implication": rows,
        "designated_values": [top],
        "falsity": falsity,
        "valid_schema_instances": checks,
        "MP_pairs": 16,
        "refuted": {
            "Peirce": {"arguments": [1, 2], "value": peirce},
            "S": {"arguments": [1, 0, 2], "value": s},
        },
        "scope": "Propositional basis only; not the full CP/GIC theory.",
        "result": "PASS",
    }


def additional_basis_obstructions():
    specifications = [
        ("K_not_redundant", [[2, 2, 2], [0, 2, 0], [0, 2, 2]], {1, 2},
         ["B", "Peirce", "PeirceF", "I", "EFQ", "DNE"], "K", [2, 1]),
        ("DNE_does_not_replace_Peirce", [[2, 2, 2], [1, 2, 2], [0, 1, 2]], {2},
         ["K", "B", "I", "EFQ", "DNE"], "PeirceF", [1]),
    ]
    results = {}
    for name, rows, designated, valid, target, counterassignment in specifications:
        n, falsity, truth = len(rows), 0, len(rows) - 1
        C = lambda a, b: rows[a][b]
        formulas = {
            "K": (2, lambda a, b: C(a, C(b, a))),
            "B": (3, lambda a, b, c: C(C(a, b), C(C(b, c), C(a, c)))),
            "Peirce": (2, lambda a, b: C(C(C(a, b), a), a)),
            "PeirceF": (1, lambda a: C(C(C(a, falsity), a), a)),
            "I": (1, lambda a: C(a, a)),
            "EFQ": (1, lambda a: C(falsity, a)),
            "DNE": (1, lambda a: C(C(C(a, falsity), falsity), a)),
        }
        checks = {}
        for axiom in valid:
            arity, formula = formulas[axiom]
            assignments = list(product(range(n), repeat=arity))
            assert all(formula(*args) in designated for args in assignments)
            checks[axiom] = len(assignments)
        assert C(truth, truth) == truth and truth in designated and falsity not in designated
        for a, b in product(range(n), repeat=2):
            assert a not in designated or C(a, b) not in designated or b in designated
        value = formulas[target][1](*counterassignment)
        assert value not in designated
        results[name] = {"result": "PASS", "implication": rows,
            "designated_values": sorted(designated), "falsity": falsity, "truth": truth,
            "truth_alias_Imp_T_T_equals_T": True,
            "valid_schema_instances": checks, "MP_pairs": n * n,
            "refuted": {"schema": target, "arguments": counterassignment, "value": value},
            "scope": "Propositional basis only; not the full CP/GIC source."}
    return results


if __name__ == "__main__":
    root = Path(__file__).resolve().parent
    print(json.dumps({
        "result": "PASS",
        "K_B_Peirce": replay_cd(root / "formalism_kbp_proof.txt"),
        "K_B_PeirceF_with_derived_EFQ": replay_cd(root / "formalism_kbpf_proof.txt",
            ["CpCqp", "CCpqCCqrCpr", "CCCpFpp", "CFp"],
            ["CCCpqrCCrpCsp", "CCCpqpp"]),
        "restricted_L_obstruction": matrix_obstruction(),
        "additional_basis_obstructions": additional_basis_obstructions(),
    }, indent=2))
