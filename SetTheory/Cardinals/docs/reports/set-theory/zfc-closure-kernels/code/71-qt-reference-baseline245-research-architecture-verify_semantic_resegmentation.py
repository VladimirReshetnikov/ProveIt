#!/usr/bin/env python3
"""Independently derive the exact 702/533 AX word identity from frozen ASTs.

This intentionally does not use the supplied fine_atom_expansions map.
Minimum spelling length is measured in the fixed 44-atom vocabulary, not in
binary machine states. The 147-rule orientation-valid seed demonstrates the
important difference between those two objectives.
"""
from collections import defaultdict
from functools import cache
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def verify():
    source = json.loads((HERE / "reference/closed-sequence-grammar-next22.json").read_text())
    symbols = json.loads((HERE / "reference/semantic-symbols.json").read_text())
    rows = json.loads((HERE / "semantic_rows.json").read_text())
    ast = source["ast_dag"]
    assert len(ast) == 226

    @cache
    def bounds(i):
        r = ast[i]
        if r[0] == "L":
            op, *arg = r[1]
            return (1, 0) if op == "dec" else (arg[0], 0) if op == "brk" else (0, arg[0]) if op == "cont" else (0, 0)
        a, b = bounds(r[1]), bounds(r[2])
        return max(a[0] - 1, b[0], 0), max(a[1], b[1] - 1, 0)

    @cache
    def finest(i):
        r = ast[i]
        return finest(r[1]) + finest(r[2]) if r[0] == "N" and bounds(r[1]) == bounds(r[2]) == (0, 0) else (i,)

    atom = {c: finest(source["atoms"][name]["ast"]) for c, name in symbols.items()}
    assert len(atom) == 44
    assert all(bounds(source["atoms"][name]["ast"]) == (0, 0) for name in symbols.values())
    encode = {v: k for k, v in symbols.items()}
    published = "".join(encode[x] for x in source["flattened_semantic_words"]["76"])
    new = (HERE / "AX_minimal_atoms.txt").read_text().strip()

    def expand(word):
        return tuple(x for c in word for x in atom[c])

    exact = finest(source["sequence_ast_roots"]["76"])
    assert published == rows["published_AX_word"] and len(published) == 702
    assert new == rows["atom_parsed_AX_word"] and len(new) == 533
    assert expand(published) == expand(new) == exact and len(exact) == 1270
    assert len(set(exact)) == 20
    assert len({x for values in atom.values() for x in values}) == 30
    assert expand(rows["reencoded_AX_word"]) == exact
    assert rows["prefix"] + "".join(rows["rows"]) + rows["tail"] == rows["reencoded_AX_word"]
    for raw, parsed in zip([rows["prefix"], *rows["rows"], rows["tail"]],
                           [rows["atom_parsed_prefix"], *rows["atom_parsed_rows"], rows["atom_parsed_tail"]]):
        assert expand(raw) == expand(parsed)
    assert rows["equality_tag_increment_count"] == 3
    increment = encode["70:0"]
    assert ast[source["atoms"]["70:0"]["ast"]] == ["L", ["inc", 1]]
    assert rows["macros"]["182"] == rows["macros"]["119"] + increment * 3

    # Bellman recurrence over every cut and every dictionary atom. Finite
    # optimal-substructure induction proves the exact minimum, no heuristic.
    distance = [10 ** 9] * (len(exact) + 1)
    distance[-1] = 0
    for i in range(len(exact) - 1, -1, -1):
        for word in atom.values():
            if exact[i:i + len(word)] == word:
                distance[i] = min(distance[i], 1 + distance[i + len(word)])
    assert distance[0] == 533

    lines = (HERE / "reference/semantic.txt").read_text().splitlines()
    nrules, nroots, natoms = map(int, lines[0].split())
    assert (nrules, nroots, natoms) == (127, 24, 44)
    rules = {w: (w[:int(k)], w[int(k):]) for k, w, q in map(str.split, lines[1:nrules + 1])}
    names = {int(q): w for k, w, q in map(str.split, lines[1:nrules + 1])}
    allowed = {c: int(v) for c, v in map(str.split, lines[nrules + nroots + 1:])}
    assert len(rules) == 127
    expanded_grammar = defaultdict(list)
    expanded_atoms = defaultdict(list)
    for w in rules:
        expanded_grammar[expand(w)].append(w)
    for c, word in atom.items():
        expanded_atoms[word].append(c)
    assert all(len(v) == 1 for v in expanded_grammar.values())
    assert all(len(v) == 1 for v in expanded_atoms.values())
    assert not (expanded_grammar.keys() & expanded_atoms.keys())

    def closure(roots, rule_map):
        live = set()
        def visit(w):
            if len(w) == 1 or w in live:
                return
            live.add(w)
            a, b = rule_map[w]
            assert w == a + b
            assert len(a) > 1 or allowed[a] & 1
            assert len(b) > 1 or allowed[b] & 2
            visit(a)
            visit(b)
        for w in roots:
            visit(w)
        return live

    boot = json.loads((HERE / "reference/bootstrap246.json").read_text())["old_labels"]
    required = source["required_entry_roots"]
    free_roots = [names[q] for q in required if q != 76]
    free_roots += [names[q] for q, bit, count in boot["used_rows"] if q in names]
    core = closure(free_roots, rules)
    assert len(core) == 51
    seed = json.loads((HERE / "AX_seed.json").read_text())
    seeded = dict(rules)
    seeded.update({w: (a, b) for w, a, b in seed["new_rules"]})
    seed_live = closure([new if q == 76 else names[q] for q in required], seeded)
    assert len(seed_live) == 147
    return {
        "status": "PASS", "immutable_ast_nodes": 226,
        "existing_semantic_atoms": 44, "dictionary_finest_atoms": 30,
        "AX_finest_tokens": 1270, "AX_distinct_finest_atoms": 20,
        "published_AX_calls": 702, "new_AX_calls": 533,
        "exact_AX_expansion_equality": True,
        "AX_fine_AST_ID_sequence_sha256": hashlib.sha256(json.dumps(exact, separators=(",", ":")).encode()).hexdigest(),
        "minimum_AX_calls_in_fixed_dictionary": distance[0],
        "correct_equality_increment_tag": 3,
        "duplicate_expanded_grammar_pairs": 0,
        "duplicate_expanded_atomic_pairs": 0,
        "grammar_atom_expanded_collisions": 0,
        "mandatory_grammar_closure_with_original_boot": len(core),
        "original_AX_private_grammar_states": 127 - len(core),
        "new_spelling_seed_live_grammar_states": len(seed_live),
        "seed_atomic_incoming_orientations_checked": True,
        "scope": "Exact semantic word/resegmentation result; no reduced-state machine follows from 533 alone. The final245 machine uses the original AX word."
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-report", type=Path)
    args = parser.parse_args()
    if not __debug__:
        parser.error("Assertions are required; do not use -O.")
    result = json.dumps(verify(), indent=2) + "\n"
    if args.write_report:
        args.write_report.write_text(result)
    print(result, end="")
