#!/usr/bin/env python3
"""Independent exact-source, literal-patch, and label-normalization audit.

Uses only Python's standard library; no discovery, CFG, or runtime module is
imported.  Every input path is configurable, while exact core input hashes
remain pinned.  This checker does NOT execute or certify physical runtime.
"""
import argparse
from bisect import bisect_right
from collections import Counter
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
DEFAULTS = {
    "original_source": "intake/K219_Construction_2026-10-20/machine/sites219.json",
    "zero_source": "allocation/zero_terminal_compiled/compiled/sites.json",
    "retagged_source": "decoder/retagged_four_row_stage1/valid_0003_54cb4e3e2f947172/sites.json",
    "retagged_seed_source": "decoder/retagged_four_row_stage1/valid_0003_0f13d32570b08259/sites.json",
    "combined_source": "decoder/composed_zero_retagged/sites.json",
    "original_table": "intake/K219_Construction_2026-10-20/machine/k219.native.tm",
    "zero_table": "allocation/zero_terminal_compiled/compiled/candidate.tm",
    "retagged_table": "decoder/retagged_four_row_stage1/valid_0003_54cb4e3e2f947172/candidate.tm",
    "retagged_seed_table": "decoder/retagged_four_row_stage1/valid_0003_0f13d32570b08259/candidate.tm",
    "combined_table": "decoder/composed_zero_retagged/candidate.tm",
    "combined_native_table": "decoder/composed_zero_retagged/candidate.native.tm",
}
HASHES = {
    "original_source": "0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789",
    "zero_source": "4a8994303330d0d8031929ace7f61737db86aee7beb9cbdf3ba593a0315bc4c2",
    "retagged_source": "ba259d31c81ec18b3bb5be6f2162ed0373b9bfdad1b184c551c7c09737956b4a",
    "retagged_seed_source": "ba259d31c81ec18b3bb5be6f2162ed0373b9bfdad1b184c551c7c09737956b4a",
    "combined_source": "7f58e08a02ec892e968e19a16825ca200e7b8bb4366efeb8df1cc25d63c8e890",
    "original_table": "b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26",
    "zero_table": "b8e431c2543c71e9fdb86faf38c21c8c7aa9c61eb735b059966e6127bbe5d821",
    "retagged_table": "54cb4e3e2f947172474676a478c331e5073fce612f3fc7b5c13742a8aba9363f",
    "retagged_seed_table": "0f13d32570b0825902670c2a9f9948e834e8ff6288d79573ac46d832e698e203",
    "combined_table": "4de59b14b068fac0071463b7237b740630ccaa7159d4cb4f097fc77a45bffb5c",
    "combined_native_table": "be7b593e272bef8c77dd9cc2248a7485302b6d43e155ea587322881842be0558",
}
ZERO_ORDINALS = [4570, 4576, 4588, 4594, 4602, 4608, 4711, 4717]
NATIVE_TO_SEARCH = {301: 102, 302: 120}


def require(condition, detail):
    if not condition:
        raise AssertionError(detail)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def json_digest(data):
    return digest(json.dumps(data, sort_keys=True, separators=(",", ":")).encode())


def validate_source(rows):
    require(type(rows) is list and len(rows) == 4744, "source occurrence count")
    paths = []
    for row in rows:
        require(type(row) is list and len(row) == 3, ("source row", row))
        p, op, a = row
        require(type(p) is str and p and set(p) <= {"0", "1"}, ("address", row))
        require(op in ("CI", "CD", "CB", "CC", "CH"), ("primitive", row))
        if op in ("CI", "CD"):
            require(type(a) is int and 0 <= a <= 8, ("register", row))
        elif op in ("CB", "CC"):
            require(type(a) is int and a > 0, ("control count", row))
        else:
            require(a is None, ("halt argument", row))
        paths.append(p)
    require(paths == sorted(set(paths)), "unique left-to-right source ordinals")
    leaves = dict(zip(paths, range(len(paths))))
    interiors = {p[:k] for p in paths for k in range(len(p))}
    require(not (set(leaves) & interiors), "prefix-free source leaves")
    all_nodes = interiors | set(leaves)
    require(all(p + b in all_nodes for p in interiors for b in "01"), "full binary source tree")
    return leaves, interiors


def ancestor_cfg(rows):
    """Walk ancestors using only left/right edge events and subtree entry."""
    leaves, interiors = validate_source(rows)

    def descend(node):
        while node not in leaves:
            require(node in interiors, ("missing subtree", node))
            node += "0"
        return leaves[node]

    def return_normally(node):
        # Completing a right child completes its pair. Completing a left
        # child enters its sibling. Completing the root restarts the source.
        for k in range(len(node) - 1, -1, -1):
            if node[k] == "0":
                return descend(node[:k] + "1")
        return descend("")

    def control(node, kind, count):
        # Break counts left ancestors; continue counts right ancestors.
        for k in range(len(node) - 1, -1, -1):
            if node[k] == ("0" if kind == "break" else "1"):
                count -= 1
                if count == 0:
                    return return_normally(node[:k]) if kind == "break" else descend(node[:k])
        return descend("")

    graph = []
    for p, op, a in rows:
        if op == "CH":
            graph.append([])
        elif op == "CI":
            graph.append([return_normally(p)])
        elif op == "CD":
            graph.append([control(p, "break", 1), return_normally(p)])
        else:
            graph.append([control(p, "break" if op == "CB" else "continue", a)])
    return graph


def arithmetic_cfg(rows):
    """Independent integer successor/cut addressing and dyadic leaf lookup.

    A leaf p represents [p*2^(D-|p|),(p+1)*2^(D-|p|)). This resolver does
    not use the ancestor resolver's traversal or prefix-entry procedure.
    """
    depth = max(len(p) for p, _, _ in rows)
    starts = [int(p, 2) << (depth - len(p)) for p, _, _ in rows]
    sizes = [1 << (depth - len(p)) for p, _, _ in rows]
    require(starts[0] == 0 and starts[-1] + sizes[-1] == 1 << depth, "dyadic endpoints")
    require(all(starts[i] + sizes[i] == starts[i + 1] for i in range(len(rows) - 1)), "dyadic partition")
    resolutions = []

    def locate(address):
        length, value = address
        require(0 <= length <= depth and 0 <= value < 1 << length, ("encoded address", address))
        position = value << (depth - length)
        i = bisect_right(starts, position) - 1
        require(0 <= i < len(rows) and position < starts[i] + sizes[i], ("lookup", address))
        # A cut address may extend a target leaf only with zero padding.
        # Interval membership alone would not establish this condition.
        leaf_length = len(rows[i][0])
        suffix_length = max(0, length - leaf_length)
        suffix = value & ((1 << suffix_length) - 1)
        require(suffix == 0, ("stray one in target suffix", address, rows[i][0]))
        resolutions.append([length, value, i, suffix_length])
        return i

    def successor(address):
        n, value = address
        return n, (value + 1) % (1 << n)

    def cut(address, desired_bit, n):
        length, value = address
        matches = 0
        for removed in range(length):
            if ((value >> removed) & 1) == desired_bit:
                matches += 1
                if matches == n:
                    return length - removed - 1, value >> (removed + 1)
        return 0, 0

    graph = []
    for p, op, a in rows:
        address = (len(p), int(p, 2))
        if op == "CH":
            targets = []
        elif op == "CI":
            targets = [successor(address)]
        elif op == "CD":
            targets = [successor(cut(address, 0, 1)), successor(address)]
        elif op == "CB":
            targets = [successor(cut(address, 0, a))]
        else:
            targets = [cut(address, 1, a)]
        graph.append([locate(target) for target in targets])
    require(locate((0, 0)) == 0, "source initial address")
    return graph, {"no_stray_one_checks_including_entry": len(resolutions),
                   "address_resolution_sha256": json_digest(resolutions), "maximum_depth": depth}


def recover_tree(rows):
    nodes = {p: (op, a) for p, op, a in rows}
    interiors = {p[:i] for p in nodes for i in range(len(p))}
    for p in sorted(interiors, key=len, reverse=True):
        nodes[p] = nodes[p + "0"], nodes[p + "1"]
    return nodes[""], nodes


def rewrite(tree, before, after):
    paths = []

    def walk(t, p):
        if t == before:
            paths.append(p)
            return after
        if isinstance(t[0], str):
            return t
        return walk(t[0], p + "0"), walk(t[1], p + "1")

    return walk(tree, ""), paths


def retag_audit(before, after, before_cfg, after_cfg):
    require(before_cfg == after_cfg, "retagging must preserve exact ordered CFG edges")
    changed_ops, changed_paths = [], []
    for i, (a, b) in enumerate(zip(before, after)):
        if a[0] != b[0]:
            changed_paths.append(i)
        if a[1:] != b[1:]:
            require(a[1:] == ["CC", 2] and b[1:] == ["CC", 3], ("unexpected retag", i, a, b))
            changed_ops.append({"ordinal": i, "old_path": a[0], "new_path": b[0],
                                "old": a[1:], "new": b[1:], "successor": before_cfg[i][0]})
        if a[1] in ("CI", "CD", "CH"):
            require(a[1:] == b[1:], ("changed register operation", i))
    require(len(changed_ops) == 81 and len(changed_paths) == 405, "retag census")
    return {"exact_ordinal_cfg_equal": True, "unchanged_CI_CD_CH_operations": True,
            "all_other_primitive_arguments_unchanged": True, "changed_control_count": 81,
            "changed_path_count": 405, "changed_controls": changed_ops,
            "changed_path_ordinals": changed_paths}


def zero_audit(before, after, before_cfg, after_cfg):
    incoming = [[] for _ in after]
    for i, edges in enumerate(after_cfg):
        for branch, target in enumerate(edges):
            incoming[target].append([i, branch])
    changes = []
    for i, (a, b) in enumerate(zip(before, after)):
        require(a[0] == b[0], ("zero substitution changed address", i))
        if a == b:
            require(before_cfg[i] == after_cfg[i], ("zero substitution changed unrelated CFG", i))
            continue
        require(a[1:] == ["CB", 1] and b[1:] == ["CD", 6], ("zero substitution", i))
        require(before_cfg[i] == after_cfg[i][:1], ("changed zero successor", i))
        require(i != 0 and incoming[i] == [[i - 2, 0]], ("guard predecessors", i, incoming[i]))
        require(before[i - 2] == after[i - 2] and after[i - 2][1:] == ["CD", 6], ("guard operation", i))
        changes.append({"ordinal": i, "path": b[0], "unique_incoming_edge": incoming[i][0],
                        "entry_guard": "R6=0", "shared_successor": before_cfg[i][0],
                        "new_positive_successor_unreachable_from_source_entry": after_cfg[i][1]})
    require([x["ordinal"] for x in changes] == ZERO_ORDINALS, "eight exact zero-terminal ordinals")
    return {"all_natural_lockstep_from_source_entry": True, "changed": changes,
            "guard_derived_from_all_cfg_predecessors_not_samples": True,
            "generic_physical_runtime_cases_excluded_by_this_audit": 0}


def source_audit(inputs):
    source_keys = ["original_source", "zero_source", "retagged_source", "combined_source"]
    data, graphs, reports, trees = {}, {}, {}, {}
    for key in source_keys:
        rows = json.loads(inputs[key].read_text())
        ancestor = ancestor_cfg(rows)
        arithmetic, domain = arithmetic_cfg(rows)
        require(ancestor == arithmetic, ("independent CFG disagreement", key))
        root, nodes = recover_tree(rows)
        unique = set(nodes.values())
        data[key], graphs[key], trees[key] = rows, ancestor, root
        reports[key] = {"sha256": HASHES[key], "leaf_occurrences": len(rows),
                        "interior_occurrences": len(nodes) - len(rows),
                        "unique_dag_nodes": len(unique),
                        "unique_interior_dag_nodes": sum(not isinstance(t[0], str) for t in unique),
                        "primitive_counts": dict(sorted(Counter(op for _, op, _ in rows).items())),
                        "generic_primitive_cases": sum(2 if op == "CD" else 1 for _, op, _ in rows),
                        "ordinal_cfg_sha256": json_digest(ancestor),
                        "ancestor_and_arithmetic_cfg_identical": True, **domain}
    require(json.loads(inputs["retagged_seed_source"].read_text()) == data["retagged_source"], "seed source identity")
    O, Z, R, C = source_keys
    retag = retag_audit(data[O], data[R], graphs[O], graphs[R])
    retag_zero = retag_audit(data[Z], data[C], graphs[Z], graphs[C])
    require(retag == retag_zero, "same exact retag transformation on both source backgrounds")
    zero = zero_audit(data[O], data[Z], graphs[O], graphs[Z])
    zero_retagged = zero_audit(data[R], data[C], graphs[R], graphs[C])
    require(zero == zero_retagged, "same guarded zero transformation after reassociation")

    I = ("CI", 1)
    old_rotation = (((I, I), (I, I)), ("CC", 2))
    new_rotation = ((I, I), ((I, I), ("CC", 3)))
    D5, D6 = ("CD", 5), ("CD", 6)
    P = D6, ("CC", 2)
    U, V = (P, ("CB", 1)), (P, D6)
    A = D5, ("CC", 1)
    old_macro, new_macro = (((D5, U), D6), (A, U)), (((D5, V), D6), (A, V))

    rotated_O, rotation_paths = rewrite(trees[O], old_rotation, new_rotation)
    zeroed_O, zero_paths = rewrite(trees[O], old_macro, new_macro)
    rotated_Z, rotation_paths_Z = rewrite(trees[Z], old_rotation, new_rotation)
    zeroed_R, zero_paths_R = rewrite(trees[R], old_macro, new_macro)
    require(rotated_O == trees[R] and zeroed_O == trees[Z], "literal individual full-tree rewrites")
    require(rotated_Z == zeroed_R == trees[C], "literal full-tree commuting composition")
    require(rotation_paths == rotation_paths_Z and len(rotation_paths) == 81, "81 exact rotation occurrences")
    require(zero_paths == zero_paths_R and len(zero_paths) == 4, "four exact equality macro occurrences")
    require(not set(ZERO_ORDINALS) & set(retag["changed_path_ordinals"]), "zero leaves unaffected by rotations")
    # Also prove the complete ordinal-level source equality without tree code.
    composed = []
    for old, z, r in zip(data[O], data[Z], data[R]):
        composed.append([r[0], *(z[1:] if old[1:] != z[1:] else r[1:])])
    require(composed == data[C], "independent ordinal composition")
    return {"sources": reports, "original_to_retagged": retag,
            "zero_to_combined": retag_zero, "original_to_zero_guard_proof": zero,
            "retagged_to_combined_guard_proof": zero_retagged,
            "composition": {"full_tree_rewrites_commute_exactly": True,
                            "independent_ordinal_reconstruction_equal": True,
                            "rotation_occurrences": rotation_paths, "zero_macro_occurrences": zero_paths,
                            "rotation_before": old_rotation, "rotation_after": new_rotation,
                            "zero_macro_before": old_macro, "zero_macro_after": new_macro,
                            "not_inferred_from_disjoint_table_rows": True}}


def read_table(path):
    table, start = {}, []
    for lineno, raw in enumerate(path.read_text().splitlines(), 1):
        if raw.startswith("#! start "):
            start.append(int(raw.split()[-1]))
        elif raw and not raw.startswith("#"):
            parts = raw.split()
            require(len(parts) == 5, ("table syntax", path, lineno))
            q, bit, write, direction, target = parts
            q, bit, write, target = map(int, (q, bit, write, target))
            require(q >= 0 and target >= 0 and bit in (0, 1) and write in (0, 1)
                    and direction in ("L", "R") and (q, bit) not in table, ("table row", path, lineno))
            table[q, bit] = write, direction, target
    require(start == [0], ("start", path))
    states = {q for q, _ in table}
    require(len(states) == 219 and len(table) == 438, ("state census", path))
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, ("binary totality", path))
    require({target for _, _, target in table.values()} - states == {254}, ("halt", path))
    require(0 in states and 84 in states and 254 not in states, ("distinguished labels", path))
    todo, reached = [0], {0}
    for q in todo:
        for bit in (0, 1):
            z = table[q, bit][2]
            if z != 254 and z not in reached:
                reached.add(z)
                todo.append(z)
    require(reached == states, ("graph reachability", path))
    return table


def rename(table, mapping):
    labels = {q for q, _ in table} | {z for _, _, z in table.values()}
    actual = {q: mapping.get(q, q) for q in labels}
    require(len(set(actual.values())) == len(actual), "injective complete label normalization")
    require(all(actual[q] == q for q in (0, 84, 254)), "normalization preserves distinguished labels")
    return {(actual[q], b): (w, d, actual[z]) for (q, b), (w, d, z) in table.items()}


def table_bytes(table):
    return ("#! start 0\n" + "".join(f"{q} {b} {w} {d} {z}\n"
            for (q, b), (w, d, z) in sorted(table.items()))).encode()


def table_diff(a, b):
    require(a.keys() == b.keys(), "patch must preserve state-row domain")
    return {key: b[key] for key in a if a[key] != b[key]}


def patch_records(base, patch):
    return [{"state": q, "read": b, "before": base[q, b], "after": patch[q, b]}
            for q, b in sorted(patch)]


def table_audit(inputs):
    keys = [key for key in DEFAULTS if key.endswith("_table")]
    tables = {key: read_table(inputs[key]) for key in keys}
    native = tables["original_table"]
    require(301 in {q for q, _ in native} and 302 in {q for q, _ in native}
            and 102 not in {q for q, _ in native} and 120 not in {q for q, _ in native}, "native fresh-label domain")
    base = rename(native, NATIVE_TO_SEARCH)
    zero, retag, seed, combined = [tables[key] for key in
                                  ("zero_table", "retagged_table", "retagged_seed_table", "combined_table")]
    zero_patch = {(38, 1): (1, "R", 119), (53, 0): (0, "R", 108), (53, 1): (1, "R", 21),
                  (88, 1): (1, "R", 53), (102, 1): (1, "R", 53), (103, 0): (0, "R", 228),
                  (119, 0): (0, "R", 68), (119, 1): (1, "R", 69), (134, 1): (1, "R", 103)}
    standalone_patch = {(139, 0): (0, "R", 99), (139, 1): (1, "R", 160), (160, 1): (1, "L", 63)}
    composition_seed_patch = {**standalone_patch, (139, 0): (0, "L", 139)}
    require(table_diff(base, zero) == zero_patch, "exact nine-row zero patch")
    require(table_diff(base, retag) == standalone_patch, "exact standalone retag patch")
    require(table_diff(base, seed) == composition_seed_patch, "exact composition seed retag patch")
    require(not zero_patch.keys() & composition_seed_patch.keys(), "table patch domains")
    require(table_diff(base, combined) == {**zero_patch, **composition_seed_patch}, "combined exact twelve-row patch")
    require(table_diff(zero, combined) == composition_seed_patch, "combined versus zero patch")
    require(table_diff(seed, combined) == zero_patch, "combined versus actual retag seed patch")
    require(table_diff(retag, seed) == {(139, 0): (0, "L", 139)}, "standalone/seed distinction")
    require({**base, **zero_patch, **composition_seed_patch} ==
            {**base, **composition_seed_patch, **zero_patch} == combined, "full table patch composition")
    native_combined = tables["combined_native_table"]
    require(rename(native_combined, NATIVE_TO_SEARCH) == combined, "combined native-to-search table equality")
    inverse = {v: k for k, v in NATIVE_TO_SEARCH.items()}
    require(rename(combined, inverse) == native_combined, "combined inverse normalization")
    require(table_bytes(rename(native_combined, NATIVE_TO_SEARCH)) == inputs["combined_table"].read_bytes(),
            "combined forward byte reconstruction")
    require(table_bytes(rename(combined, inverse)) == inputs["combined_native_table"].read_bytes(),
            "combined inverse byte reconstruction")
    # Native labels and normalized search labels name states, not source ordinals.
    return {"working_states_each": 219, "binary_rows_each": 438, "start": 0, "dispatcher": 84, "halt": 254,
            "all_working_states_graph_reachable_each": True,
            "input_sha256": {key: HASHES[key] for key in keys},
            "normalized_original_serialization_sha256": digest(table_bytes(base)),
            "native_to_search_nonidentity": NATIVE_TO_SEARCH,
            "combined_forward_and_inverse_byte_reconstruction": True,
            "zero_patch": patch_records(base, zero_patch),
            "standalone_retag_patch": patch_records(base, standalone_patch),
            "combined_retag_seed_patch": patch_records(base, composition_seed_patch),
            "combined_patch": patch_records(base, {**zero_patch, **composition_seed_patch}),
            "standalone_to_composition_seed_patch": patch_records(retag, {(139, 0): (0, "L", 139)}),
            "exact_table_patch_composition": True,
            "composition_uses_different_retagged_physical_seed": True,
            "physical_runtime_or_startup_proved_here": False}


PROOF = """# Exact source transport and literal table-patch audit

This is a reproducible mathematical certificate for source transport, table
identity, and state-label normalization. It does not replace fresh blank-tape
startup or unbounded physical-runtime certification of either table. No
physical runtime engine or discovery helper is imported by source_check.py.

## Inputs and source semantics

All core source and table bytes are SHA256-pinned in the standalone checker
and source_transport.json. Each complete source is a full binary syntax tree
with 4,744 primitive occurrences, in left-to-right ordinal order. A positive
decrement subtracts one and returns normally. A zero decrement preserves its
register and returns break 1. Breaks count enclosing left edges; continues
count enclosing right edges. Matching break exits its pair, whereas matching
continue reenters its pair. Source control falling through the root restarts
at ordinal 0. CH halts.

Two independently implemented resolvers validate every ordered CFG edge.
The first walks ancestor edges and descends to the first leaf. The second
uses integer successor modulo address length, bit cuts, and binary search in
the dyadic interval partition induced by the leaves. Every arithmetic target
is also checked for the stronger property that any suffix extending beyond
the resolved leaf consists entirely of zeros. Thus a mere interval hit
cannot accidentally validate a target with stray ones. Both decrement guards
are included, even if a later reachability argument makes one unreachable.

## Retagging preserves every source primitive step

Write I = CI1. Exactly 81 occurrences of

    (((I,I),(I,I)),CC2)

are replaced with

    ((I,I),((I,I),CC3)).

This changes 405 primitive addresses and exactly 81 arguments, each CC2 to
CC3. CI, CD, and CH operations and every other primitive argument are
unchanged. The checker reconstructs the actual complete trees and applies
these literal replacements; it does not trust a discovery recipe.

Supplementarily, both displayed open trees increment R1 four times and
return continue 1, changing no other register. In the first tree CC2 is
propagated through one enclosing right edge. In the second tree CC3 is
propagated through two enclosing right edges. All increments terminate for
every natural register vector, so this local contract itself is also exact.

The original and standalone-retagged programs have identical ordinal CFGs.
The zero-terminal and combined programs likewise have identical ordinal
CFGs, with precisely the same retag changes. All register operations and
branch conditions are equal at corresponding ordinals. Hence induction on
source primitive steps gives lockstep equality from corresponding ordinals
and arbitrary equal natural register vectors, including halt and divergence.
This is an exact finite syntactic/CFG check supporting an all-natural theorem,
not numerical testing of finitely many register values.

## Guarded zero terminals

The only operation differences original-to-zero, and retagged-to-combined,
are CB1 to CD6 at ordinals 4570, 4576, 4588, 4594, 4602, 4608, 4711, 4717.
For each changed ordinal i, the checker builds the complete incoming-edge
list, including both decrement branches. Its unique incoming edge is the
zero edge of the unchanged CD6 at i-2. Initial ordinal 0 is not changed.
Consequently every reachable entry to a changed leaf has R6=0. Its new CD6
step is register identity and its zero successor is precisely the old CB1
successor. Every other primitive and ordered edge is unchanged. Induction
proves lockstep equivalence from source entry for every initial natural
register vector. No incoming edge or generic runtime case is omitted.

There is an independent local open-tree explanation. Set P=(CD6,CC2),
U=(P,CB1), V=(P,CD6), and A=(CD5,CC1). If R6 is positive, P decrements it
and returns continue 1, propagated by both U and V without entering their
right child. If R6 is zero, P returns normally with the register still zero;
both right children then return break 1 without changing registers. Thus U
and V have equal finite open-tree contracts for all natural registers.
The checker finds exactly four literal full-tree replacements

    (((CD5,U),CD6),(A,U)) -> (((CD5,V),CD6),(A,V)).

## Exact composition, not an inference from disjoint table rows

The checker starts from the complete original tree O. Let T be the 81 literal
retagging/reassociation substitutions and Z the four equality-macro zero
substitutions. It checks T(O)=R, Z(O)=Z0, T(Z0)=C, and Z(R)=C, where R, Z0,
and C are the pinned standalone-retagged, zero-terminal, and combined source
files. Counts and occurrence paths agree in both orders. A second,
ordinal-by-ordinal reconstruction checks the complete combined source again.
The zero-entry predecessor proof is separately repeated in the retagged
background. Therefore both the source transformations and their all-natural
proofs compose. Disjoint table patch rows alone would not prove this result.

## Literal tables and normalization

Every table is independently parsed and checked for 219 working states,
438 binary transition rows, start 0, dispatcher 84, halt target 254, and
graph reachability of every working label. Native source-table state labels
301 and 302 are normalized to absent search labels 102 and 120, respectively;
all other state labels are fixed. This mapping is checked to be bijective
on every source and target label. For the combined table both forward and
inverse normalizations reproduce the exact pinned bytes, not just behavior.

Against the normalized original table, the zero-terminal table changes
exactly nine literal rows. The standalone retagged table changes exactly
three: 139/0 becomes 0 R 99, 139/1 becomes 1 R 160, and 160/1 becomes 1 L 63.
The combined construction uses a DIFFERENT retagged physical seed: its
139/0 row is 0 L 139. That seed differs from the standalone retagged table
at exactly this one row and has the same source file. The combined table is
exactly the nine-row zero patch plus that three-row seed patch. All old/new
rows, hashes, and the one-row seed distinction are recorded in the report.
No physical refinement is inferred merely from patch disjointness.

## Reproduction and scope

Run `python source_check.py` in the research checkout. For an archive with a
different layout, run `python source_check.py --help` and set each input path
using its named option; use `--output-dir` for the two generated reports.
All paths are configurable but the accepted input bytes are not weakened.
Only Python's standard library is needed. Checks remain active under -O.

Successful source_transport.json status means all assertions above passed.
Its source equivalences can be combined with independently certified startup
and unbounded primitive refinement to transport the accepted source theorem
to the two exact physical machines. This certificate by itself does not claim
that pending physical proofs passed, prove consistency, or satisfy the goal
of at most 218 states.
"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key, relative in DEFAULTS.items():
        parser.add_argument("--" + key.replace("_", "-"), type=Path,
                            default=ROOT / "research_sub219" / relative)
    parser.add_argument("--output-dir", type=Path, default=HERE)
    args = parser.parse_args()
    inputs = {key: getattr(args, key) for key in DEFAULTS}
    for key, path in inputs.items():
        require(digest(path.read_bytes()) == HASHES[key], ("input SHA256 mismatch", key, str(path)))
    sources = source_audit(inputs)
    tables = table_audit(inputs)
    report = {"status": "INDEPENDENT_ALL_NATURAL_RETAGGED_COMPOSED_SOURCE_AND_LITERAL_TABLE_TRANSPORT_PASS",
              "checker_sha256": digest(Path(__file__).read_bytes()), "input_sha256": HASHES,
              **sources, "tables": tables,
              "scope": "All-natural exact source transport, independent address domains, literal full-tree composition, exact physical table patches and bijective normalization. No blank-tape startup or unbounded physical runtime proof is performed here."}
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "source_transport.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    (args.output_dir / "PROOF_SOURCE.md").write_text(PROOF)
    print(json.dumps({"status": report["status"], "retagged_controls": 81, "moved_addresses": 405,
                      "guarded_zero_terminals": 8, "full_tree_composition": True,
                      "combined_uses_distinct_seed": True, "output_dir": str(args.output_dir)}, indent=2))


if __name__ == "__main__":
    main()
