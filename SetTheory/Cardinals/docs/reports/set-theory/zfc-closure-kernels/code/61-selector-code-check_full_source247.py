#!/usr/bin/env python3
"""Port of the prefix250 full-source/full-PC audit to the exact Prefix247 table.
Only the table identity, row count, and current repository pin are changed.
The reference implementation is bundled unchanged in reference250/code/.

The source parser and full-length path arithmetic are independent of the
prototype's cached sites, inc(), and strip().  Literal binary rules are still
checked by prefix_affine, whose ordinary soundness proof is reviewed in the
companion note.  This is not a replacement proof assistant.
"""
from __future__ import annotations

import argparse
from collections import Counter
from hashlib import sha1, sha256
import importlib.util
import json
from pathlib import Path
import re

PIN = "e0b512a63e2c1ca6a1698fa437b8568f1643ff6b"
PROG_BLOB = "254106e2b20762ddd89b2fad4765af5248d41469"
PROG_SHA256 = "1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746"
TABLE_SHA256 = "0d37614f3caf37139b0be127837630539224acd1c45d748cf5704abfc3230b42"
PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def parse_source(path):
    data = path.read_bytes()
    assert sha256(data).hexdigest() == PROG_SHA256
    assert sha1(f"blob {len(data)}\0".encode() + data).hexdigest() == PROG_BLOB
    text = data.decode("utf-8")
    body = text.split("Definition p254_tab", 1)[1].split(":= [", 1)[1].split("].", 1)[0]
    assert "(*" not in body
    # Tokenize from the current position and reject any unmatched material;
    # no regex extraction silently skips malformed table content.
    tokens, pos = [], 0
    pattern = re.compile(r"\s*(CN|CI|CD|CB|CC|CH|[0-9]+|[(),;])")
    while body[pos:].strip():
        match = pattern.match(body, pos)
        assert match, ("unparsed source material", pos, body[pos:pos+80])
        tokens.append(match.group(1))
        pos = match.end()
    cursor = 0

    def expect(token):
        nonlocal cursor
        assert tokens[cursor] == token, (cursor, tokens[cursor], token)
        cursor += 1

    def edge():
        nonlocal cursor
        op = tokens[cursor]
        assert op in {"CN", "CI", "CD", "CB", "CC", "CH"}
        cursor += 1
        arg = None
        if op != "CH":
            assert tokens[cursor].isdigit()
            arg = int(tokens[cursor])
            cursor += 1
        return op, arg

    nodes = []
    while cursor < len(tokens):
        expect("(")
        a = edge()
        expect(",")
        b = edge()
        expect(")")
        nodes.append((a, b))
        if cursor < len(tokens):
            expect(";")
    declaration = text.split("Definition p254 : prog :=", 1)[1].split("|}.", 1)[0]
    root = int(re.search(r"root\s*:=\s*(\d+)", declaration).group(1))
    declared = int(re.search(r"nnodes\s*:=\s*(\d+)", declaration).group(1))
    assert root == 0 and declared == len(nodes) == 6459
    indegrees = Counter()
    for i, pair in enumerate(nodes):
        for op, r in pair:
            if op == "CN":
                assert i < r < len(nodes)
                indegrees[r] += 1
            elif op in ("CI", "CD"):
                assert 0 <= r < 9
    assert indegrees == Counter({i: 1 for i in range(1, len(nodes))})
    sites, visited = [], set()
    stack = [(root, "")]
    while stack:
        node, word = stack.pop()
        assert node not in visited
        visited.add(node)
        # Push right then left to derive the actual DFS source order.
        for bit, (op, r) in reversed(list(enumerate(nodes[node]))):
            if op == "CN":
                stack.append((r, word + str(bit)))
        # Use a separate literal edge worklist below; visited only checks the
        # forward tree property independently of the path enumeration.
    assert visited == set(range(len(nodes)))
    work = [("CN", root, "")]
    while work:
        op, r, word = work.pop()
        if op == "CN":
            for bit in (1, 0):
                child_op, child_arg = nodes[r][bit]
                work.append((child_op, child_arg, word + str(bit)))
        else:
            sites.append([word, op, PHYSICAL[r] if op in ("CI", "CD") else r])
    assert len(sites) == 6460 and len({p for p, _, _ in sites}) == 6460
    return nodes, sites


def full_inc(word):
    # Preserve the complete input width, matching RegisterPath.incPath.
    out = list(word)
    carry = True
    for i in range(len(out) - 1, -1, -1):
        if not carry:
            break
        if out[i] == "0":
            out[i], carry = "1", False
        else:
            out[i] = "0"
    return "".join(out), carry


def full_strip(word, bit, count):
    # Direct implementation of stripRev followed by reversal.
    reversed_word = list(reversed(word))
    at = 0
    while count != 0 and at < len(reversed_word):
        if reversed_word[at] == bit:
            count -= 1
        at += 1
    return "".join(reversed(reversed_word[at:]))


def read_tm(path):
    assert digest(path) == TABLE_SHA256
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        q, b, w, d, t = line.split()
        assert (q, int(b)) not in table
        table[q, int(b)] = int(w), d, t
    assert len(table) == 494
    return table


def module(path):
    spec = importlib.util.spec_from_file_location("reviewed_" + path.stem, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def check_oracle(affine):
    checks = 0
    for r in range(9):
        assert affine.oracle("95", None, ("mark", r)) is None
        checks += 1
        for wrong in range(9):
            if wrong == r:
                continue
            for zero in (False, True):
                assert affine.oracle("95", (wrong, zero), ("mark", r)) is None
                checks += 1
        for zero in (False, True):
            got = affine.oracle("95", (r, zero), ("mark", r))
            expected = ("112", ("plain", None), 0) if zero else (
                "48", ("plain", ("dec", r)), 1)
            assert got == expected
            checks += 1
        assert affine.oracle("73", None, ("mark", r)) == (
            "48", ("plain", ("inc", r)), 0)
        checks += 1
        for state in affine.SKIP:
            for effect in ("inc", "dec"):
                assert affine.oracle(state, None, ("plain", (effect, r))) is None
                checks += 1
    return checks


def check_sites(affine, table, sites):
    case_counts, rule_counts = Counter(), Counter()
    minimum = 10**9
    full_path_cases, max_rules, overflow_cases = 0, 0, 0
    for p, op, r in sites:
        assert len(p) <= 40
        for zero in ((True, False) if op == "CD" else (None,)):
            branch = (r, zero) if op == "CD" else None
            extra, effect, overflow = 0, None, False
            if op == "CI":
                successor, overflow = full_inc(p)
                effect = "inc", r
            elif op == "CD" and not zero:
                successor, overflow = full_inc(p)
                effect, extra = ("dec", r), 1
            elif op == "CD":
                successor, overflow = full_inc(full_strip(p, "0", 1))
            elif op == "CB":
                successor, overflow = full_inc(full_strip(p, "0", r))
            elif op == "CC":
                successor = full_strip(p, "1", r)
            else:
                assert op == "CH"
                successor = ""
            constant_gap = 40 + extra + int(overflow) - len(successor)
            assert constant_gap >= 0
            right = ([('b', int(b)) for b in successor] +
                     [('r', 0, 1, constant_gap), ('b', 1),
                      ('box', ('plain', effect))])
            rules, literal = affine.run(table, p, branch,
                affine.canon([('b', 1)], right), halt=(op == "CH"), fuel=1000)
            assert literal > 0
            key = op + ("/zero" if zero else "/positive") if op == "CD" else op
            case_counts[key] += 1
            rule_counts.update(rules)
            minimum, max_rules = min(minimum, literal), max(max_rules, sum(rules.values()))
            full_path_cases += 1
            overflow_cases += int(overflow)
    assert full_path_cases == 8391
    return dict(cases=full_path_cases, by_operation=dict(case_counts),
                target_paths_keep_all_overflow_and_trailing_zero_cells=True,
                overflow_cases=overflow_cases, minimum_literal_steps=minimum,
                max_rules=max_rules, rule_counts=dict(rule_counts))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--program", type=Path, required=True)
    ap.add_argument("--sites", type=Path, required=True)
    ap.add_argument("--table", type=Path, required=True)
    ap.add_argument("--checker", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    if not __debug__:
        ap.error("Assertions must be enabled.")
    nodes, sites = parse_source(args.program)
    cached = json.loads(args.sites.read_text())
    assert sites == cached, "fresh source expansion differs from cached sites"
    affine = module(args.checker)
    table = read_tm(args.table)
    result = dict(status="PASS", source_pin=PIN, program_sha256=PROG_SHA256,
                  program_github_blob=PROG_BLOB, table_sha256=TABLE_SHA256,
                  affine_checker_sha256=digest(args.checker),
                  cached_sites_sha256=digest(args.sites),
                  fully_consumed_source_tokens=True, node_count=len(nodes),
                  rooted_forward_full_binary_tree=True, source_site_count=len(sites),
                  source_sites_equal_cached_exactly=True,
                  minimum_leaf_depth=min(len(p) for p, _, _ in sites),
                  maximum_leaf_depth=max(len(p) for p, _, _ in sites),
                  physical_register_map=list(PHYSICAL),
                  oracle_guard_checks=check_oracle(affine),
                  universal_guarded_recheck=check_sites(affine, table, sites))
    data = json.dumps(result, indent=2) + "\n"
    args.output.write_text(data)
    print(data, end="")


if __name__ == "__main__":
    main()
