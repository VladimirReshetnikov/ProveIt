#!/usr/bin/env python3
"""Independent, standard-library audit of the selected PA TM reference designs.

This checks literal identity, deterministic rooted graph isomorphism, source
metrics, and two finite startups. It is NOT a consistency or nonhalting proof.
All inputs are named and SHA-256 pinned in inputs/manifest.json.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
import hashlib
import json
from pathlib import Path
import re


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def pinned(root, item):
    raw = (root / item["file"]).read_bytes()
    require(digest(raw) == item["sha256"], "Input hash mismatch: " + item["file"])
    return raw


def table(raw):
    rows = {}
    for line in raw.decode("ascii").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        q, b, w, direction, target = line.split()
        q, b, w, target = map(int, (q, b, w, target))
        require(b in (0, 1) and w in (0, 1), "Nonbinary row")
        require(direction in ("L", "R"), "Invalid direction")
        require((q, b) not in rows, "Duplicate row")
        rows[q, b] = w, direction, target
    working = {q for q, b in rows}
    require(set(rows) == {(q, b) for q in working for b in (0, 1)}, "Incomplete domain")
    halts = {target for w, direction, target in rows.values()} - working
    require(len(halts) == 1, "Expected a unique distinguished halt")
    require(0 in working, "Missing start state 0")
    return rows, working, halts.pop()


def canonical(rows, working, halt):
    order, queue = {0: 0}, deque([0])
    while queue:
        q = queue.popleft()
        for bit in (0, 1):
            target = rows[q, bit][2]
            if target != halt and target not in order:
                order[target] = len(order)
                queue.append(target)
    require(set(order) == working, "Unreachable working state in reference table")
    triples = []
    for q in order:
        triples.append([[w, d, "H" if t == halt else order[t]]
                        for w, d, t in (rows[q, 0], rows[q, 1])])
    return triples, order


def check_isomorphism(a, b, mapping, halt_a, halt_b):
    require(len(set(mapping.values())) == len(mapping), "Noninjective isomorphism")
    require(mapping[0] == 0, "Start not fixed")
    for (q, bit), (write, direction, target) in a.items():
        new_target = halt_b if target == halt_a else mapping[target]
        require(b[mapping[q], bit] == (write, direction, new_target), "Bad isomorphism row")


OPS = {".inc": "CI", ".dec": "CD", ".breakTo": "CB", ".continueTo": "CC", ".halt": "CH"}


def lean_tree(raw):
    env = {}
    def term(tokens):
        token = tokens.popleft()
        if token == "(":
            answer = term(tokens)
            require(tokens.popleft() == ")", "Unbalanced source expression")
            return answer
        if token == ".node":
            return term(tokens), term(tokens)
        if token == ".leaf":
            return term(tokens)
        if token in OPS:
            return OPS[token], None if token == ".halt" else int(tokens.popleft())
        require(token in env, "Unknown tree reference " + token)
        return env[token]
    for name, rhs in re.findall(r"^def (\w+) : Tree := (.+)$", raw.decode(), re.M):
        tokens = deque(re.findall(r"\(|\)|\.[A-Za-z]+|[A-Za-z_][A-Za-z_0-9]*|[0-9]+", rhs))
        env[name] = term(tokens)
        require(not tokens, "Unparsed tree suffix")
    require("trie" in env, "Missing trie definition")
    return env["trie"]


def is_leaf(node):
    return isinstance(node[0], str)


def flatten(node, path=""):
    if is_leaf(node):
        return [[path, *node]]
    return flatten(node[0], path + "0") + flatten(node[1], path + "1")


def site_tree(rows):
    leaves = {path: (op, arg) for path, op, arg in rows}
    require(len(leaves) == len(rows), "Duplicate source path")
    prefixes = {path[:i] for path in leaves for i in range(len(path) + 1)}
    def visit(path):
        if path in leaves:
            require(path + "0" not in prefixes and path + "1" not in prefixes,
                    "Source leaf has descendants")
            return leaves[path]
        require(path + "0" in prefixes and path + "1" in prefixes, "Incomplete tree")
        return visit(path + "0"), visit(path + "1")
    root = visit("")
    require(flatten(root) == rows, "Noncanonical source order")
    return root


def source_stats(root):
    distinct = set()
    def visit(node):
        if node in distinct:
            return
        distinct.add(node)
        if not is_leaf(node):
            visit(node[0]); visit(node[1])
    visit(root)
    rows = flatten(root)
    return {"sites": len(rows),
            "distinct_internal_nodes": sum(not is_leaf(x) for x in distinct),
            "distinct_leaf_instructions": sum(is_leaf(x) for x in distinct),
            "total_distinct_subtrees": len(distinct),
            "maximum_path": max(len(p) for p, _, _ in rows),
            "maximum_zero_run": max(len(s) for p, _, _ in rows for s in p.split("1")),
            "opcodes": dict(sorted(Counter(op for p, op, arg in rows).items()))}


def ordinal_graph(rows):
    """Resolve structured jumps by subtree intervals and ancestor orientation."""
    indices = {path: i for i, (path, op, arg) in enumerate(rows)}
    bounds = {}
    def intervals(path):
        if path in indices:
            answer = indices[path], indices[path] + 1
        else:
            left, right = intervals(path + "0"), intervals(path + "1")
            require(left[1] == right[0], "Noncontiguous source subtree")
            answer = left[0], right[1]
        bounds[path] = answer
        return answer
    intervals("")
    def jump(path, edge, count):
        while path:
            last, path = path[-1], path[:-1]
            if last == edge:
                count -= 1
                if count == 0:
                    return bounds[path][1] % len(rows) if edge == "0" else bounds[path][0]
        return 0
    graph = []
    for i, (path, op, arg) in enumerate(rows):
        successor = (i + 1) % len(rows)
        if op == "CI": targets = [successor]
        elif op == "CD": targets = [jump(path, "0", 1), successor]
        elif op == "CB": targets = [jump(path, "0", arg)]
        elif op == "CC": targets = [jump(path, "1", arg)]
        elif op == "CH": targets = []
        else: raise ValueError("Unknown source opcode")
        graph.append([op, arg, targets])
    return graph


def startup(rows, steps, target_state):
    q, head, ones = 0, 0, set()
    for _ in range(steps):
        require((q, int(head in ones)) in rows, "Premature halt in finite startup")
        write, direction, q = rows[q, int(head in ones)]
        if write: ones.add(head)
        else: ones.discard(head)
        head += 1 if direction == "R" else -1
    require(q == target_state, "Unexpected startup control")
    expected = {-1, 0, 48}
    cell = 49
    for value in [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26:
        expected.update(range(cell + 1, cell + value + 2))
        cell += value + 2
    relative = {cell - head for cell in ones}
    require(relative == expected, "Unexpected entire startup tape")
    return {"steps": steps, "state": q, "head": head, "one_cells_relative_to_head": sorted(relative),
            "full_tape_checked": True, "claim": "finite startup only"}


def helper_equivalences(root, manifest, loaded):
    """Recheck all eighteen accepted merge-plus-helper transformations.

    The predecessor bit is forced by the complete incoming edge census.
    Each changed step is then simulated on the entire two-cell footprint;
    reading an unspecified exterior cell is rejected. These finite facts
    support a positive bounded-stuttering simulation on every initial tape.
    """
    baselines = {}
    for label, item in manifest.get('helper_baselines', {}).items():
        rows, working, halt = table(pinned(root, item))
        serial, _ = canonical(rows, working, halt)
        require(serial == loaded[item['graph_table_id']][3], 'Helper baseline binding mismatch')
        baselines[label] = rows, working, halt
    receipts = []
    for item in manifest.get('helper_recipes', []):
        rows, working, halt = baselines[item['baseline']]
        child, cw, ch = table(pinned(root, item['native']))
        drop, keep, bit, x0, x1, w0, w1 = item['parameters']
        require(drop != keep and drop != 0 and keep != 0 and 500 not in working,
                'Bad helper endpoints')
        require(ch == halt and len(cw) == len(working) == 208, 'Helper state count mismatch')
        pi = lambda q: keep if q == drop else q
        expected = {(q, b): (w, d, pi(n)) for (q, b), (w, d, n) in rows.items() if q != drop}
        expected[keep, bit] = bit, 'L', 500
        expected[500, 0] = w0, 'R', pi(x0)
        expected[500, 1] = w1, 'R', pi(x1)
        require(child == expected, 'Helper literal patch mismatch')
        serial, names = canonical(child, cw, ch)
        dense, _, dh, ds, dn = loaded[item['id']]
        require(serial == ds, 'Helper native/dense graph mismatch')
        inverse = {v: k for k, v in dn.items()}
        check_isomorphism(child, dense, {q: inverse[n] for q, n in names.items()}, ch, dh)
        blocks, census = [], {}
        for q in (drop, keep):
            incoming = [(s, b, w, d) for (s, b), (w, d, n) in rows.items() if n == q]
            require(incoming and all(d == 'R' for s, b, w, d in incoming), 'Incoming direction not forced')
            tags = {w for s, b, w, d in incoming}
            require(len(tags) == 1, 'Predecessor tag not forced')
            tag = next(iter(tags)); census[q] = incoming
            for read in (0, 1):
                tape = {-1: tag, 0: read}; state, head = keep, 0
                write, direction, target = rows[q, read]
                goal = {-1: tag, 0: write}
                goal_head = 1 if direction == 'R' else -1
                trace = []
                for count in range(1, 129):
                    require(state != halt, 'Internal halt in helper block')
                    require(head in tape, 'Helper reads unspecified exterior cell')
                    scanned = tape[head]; w, d, n = child[state, scanned]
                    trace.append([state, head, scanned, w, d, n])
                    tape[head] = w; head += 1 if d == 'R' else -1; state = n
                    if state == pi(target) and head == goal_head and tape == goal:
                        break
                else:
                    raise ValueError('Helper block failed to reach exact positive endpoint')
                blocks.append({'old_state': q, 'read': read, 'preceding_bit': tag,
                               'steps': count, 'trace': trace})
        receipts.append({'id': item['id'], 'baseline_class': item['baseline'],
                         'parameters': item['parameters'], 'incoming_census': census,
                         'local_blocks': blocks, 'maximum_block_steps': max(b['steps'] for b in blocks),
                         'ordinary_rows_commute': True, 'whole_tape_endpoints_checked': True,
                         'initial_state_preserved': True})
    require(len(receipts) in (0, 18), 'Expected all eighteen helper variants')
    return receipts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path("comparison_receipt.json"))
    parser.add_argument("--inputs", type=Path, default=Path(__file__).resolve().parent / "inputs")
    args = parser.parse_args()
    manifest = json.loads((args.inputs / "manifest.json").read_text())
    results, loaded, classes = [], {}, []
    for item in manifest["tables"]:
        rows, working, halt = table(pinned(args.inputs, item))
        serial, labels = canonical(rows, working, halt)
        group = next((i for i, old in enumerate(classes) if old == serial), None)
        if group is None:
            group = len(classes)
            classes.append(serial)
        motif = [q for q in sorted(working) if rows[q, 0][:2] == (0, "L")
                 and rows[q, 1][:2] == (1, "R")
                 and rows[q, 0][2] == rows[q, 1][2] in working]
        results.append({"id": item["id"], "sha256": item["sha256"], "states": len(working),
                        "rows": len(rows), "halt": halt, "graph_reachable_states": len(labels),
                        "isomorphism_class": group, "mixed_entry_motif_states": motif,
                        "bfs_state_map": labels})
        loaded[item["id"]] = rows, working, halt, serial, labels
    witnesses = []
    for i, a in enumerate(results):
        for b in results[i + 1:]:
            if a["isomorphism_class"] == b["isomorphism_class"]:
                ar, _, ah, _, am = loaded[a["id"]]
                br, _, bh, _, bm = loaded[b["id"]]
                inverse = {v: k for k, v in bm.items()}
                mapping = {q: inverse[n] for q, n in am.items()}
                check_isomorphism(ar, br, mapping, ah, bh)
                witnesses.append({"from": a["id"], "to": b["id"], "map": mapping})
    sources, source_rows = [], {}
    for item in manifest["sources"]:
        raw = pinned(args.inputs, item)
        root = lean_tree(raw) if item["format"] == "lean" else site_tree(json.loads(raw))
        rows = flatten(root)
        graph = ordinal_graph(rows)
        sources.append({"id": item["id"], "sha256": item["sha256"], **source_stats(root),
                        "control_edges": sum(len(targets) for op, arg, targets in graph)})
        source_rows[item["id"]] = rows, graph
    a, b = source_rows["u208_A"], source_rows["u208_B"]
    require([r[1:] for r in a[0]] == [r[1:] for r in b[0]], "U208 primitive words differ")
    require(a[1] == b[1], "U208 ordinal graphs differ")
    helpers = helper_equivalences(args.inputs, manifest, loaded)
    u208_classes = len({x['isomorphism_class'] for x in results if x['id'].startswith('u208_')})
    if helpers:
        require(u208_classes == 20, 'Expected twenty incoming U208 graph classes')
    out = {"scope": "Reference comparison; no new smaller machine or consistency proof",
           "source_pins": manifest["source_pins"], "tables": results,
           "isomorphism_witnesses": witnesses, "sources": sources,
           "incoming_u208_graph_classes": u208_classes,
           "accepted_helper_equivalences": helpers,
           "additional_incoming_archive_status": manifest.get('incoming_research_status', []),
           "u208_same_primitive_word_and_ordinal_graph": True,
           "u208_different_source_addresses": sum(x[0] != y[0] for x, y in zip(a[0], b[0])),
           "pa196_startup": startup(loaded["pa196"][0], 58154, 75),
           "pa209_startup": startup(loaded["pa209"][0], 58210, 81)}
    args.output.write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps({"tables_checked": len(results), "u208_classes": u208_classes,
                      "helper_equivalences_checked": len(helpers),
                      "isomorphism_witnesses_checked": len(witnesses), "sources": sources,
                      "full_startups_checked": 2, "output": str(args.output)}, indent=2))


if __name__ == "__main__":
    main()
