#!/usr/bin/env python3
"""Replay the inherited QH5 emitter, multiplier binding and exchange proof.

Python 3.10+, standard library only. Run without -O. The exact 190-token
emitter checker is preserved from the pinned AX11 packet's secondary QH5
delivery. This wrapper independently resolves source paths, repeats the
61 coefficient-loop bindings and all outside successor equalities, and
replays the flat K/S/MP exchange certificate. It does not import a machine
builder or a physical symbolic executor. See inherited_qh5/PROVENANCE.json.
"""
from functools import lru_cache
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
FROZEN = HERE / "inherited_qh5"
QH5 = PACKAGE / "construction" / "inputs" / "qh5"


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def read_json(path):
    return json.loads(path.read_text())


def freeze(value):
    return tuple(map(freeze, value)) if isinstance(value, (list, tuple)) else value


def is_node(value):
    return isinstance(value, tuple) and len(value) == 2


def read_grammar(path):
    data = read_json(path)
    rules = data["rules"]

    def expand(value, active=frozenset()):
        if isinstance(value, str) and value in rules:
            require(value not in active, "cyclic grammar")
            return expand(rules[value], active | {value})
        if isinstance(value, list):
            if len(value) == 3 and value[0] == "leaf":
                return tuple(value)
            require(len(value) == 2, "non-binary grammar production")
            return tuple(expand(child, active) for child in value)
        require(isinstance(value, str), "invalid grammar reference")
        return value

    return expand(data["root"])


def source_sites(grammar, nodes):
    sites = []

    def visit(term, path, active=frozenset()):
        if isinstance(term, str):
            require(term not in active, "cyclic source node")
            body = grammar if term == "x67" else nodes[term]
            visit(body, path, active | {term})
        elif is_node(term):
            visit(term[0], path + (0,), active)
            visit(term[1], path + (1,), active)
        else:
            require(len(term) == 3 and term[0] == "leaf", "invalid source leaf")
            sites.append((path, term[1], term[2]))

    visit("node172", ())
    require(len({path for path, _, _ in sites}) == len(sites), "duplicate source path")
    return sites


def resolve(sites):
    exact = {path: i for i, (path, _, _) in enumerate(sites)}

    @lru_cache(None)
    def locate(path):
        if path in exact:
            return exact[path]
        for i, (leaf, _, _) in enumerate(sites):
            # A subtree denotes its leftmost leaf. Padding a leaf by zero
            # bits is the same leftmost address; nonzero suffixes are barred.
            if leaf[:len(path)] == path:
                return i
            if path[:len(leaf)] == leaf and not any(path[len(leaf):]):
                return i
        raise AssertionError(("unresolved source address", path))

    def after(path):
        for i in range(len(path) - 1, -1, -1):
            if path[i] == 0:
                return locate(path[:i] + (1,))
        raise AssertionError(("unexpected outer source exit", path))

    def cut(path, bit, count):
        require(isinstance(count, int) and count > 0, "invalid source cut count")
        for i in range(len(path) - 1, -1, -1):
            if path[i] == bit:
                count -= 1
                if count == 0:
                    return path[:i]
        raise AssertionError(("source cut underflow", path, bit))

    instructions = []
    for path, op, arg in sites:
        if op == "inc":
            row = ("inc", arg, after(path))
        elif op == "dec":
            row = ("dec", arg, after(cut(path, 0, 1)), after(path))
        elif op == "breakTo":
            row = ("jump", after(cut(path, 0, arg)))
        elif op == "continueTo":
            row = ("jump", locate(cut(path, 1, arg)))
        else:
            require(op == "halt", "unknown source primitive")
            row = ("halt",)
        instructions.append(row)
    return instructions


def occurrences(grammar, nodes, name):
    paths = []

    def visit(term, path):
        if isinstance(term, str):
            if term == name:
                paths.append(path)
            visit(grammar if term == "x67" else nodes[term], path)
        elif is_node(term):
            visit(term[0], path + (0,))
            visit(term[1], path + (1,))

    visit("node172", ())
    return paths


def check_multiplier():
    old_nodes = {name: freeze(body) for name, body in read_json(FROZEN / "qh6.nodes.json").items()}
    new_nodes_json = read_json(QH5 / "machine" / "nodes.json")
    new_nodes = {name: freeze(body) for name, body in new_nodes_json.items()}
    require(set(old_nodes) == set(new_nodes), "QH5 source node set changed")
    require({name for name in old_nodes if old_nodes[name] != new_nodes[name]} == {"node61"},
            "coefficient source change extends outside node61")
    inc = ("leaf", "inc", 1)
    require(old_nodes["node61"] == ((inc, "node60"), (inc, "node60")), "old coefficient is not six")
    require(new_nodes["node61"] == ((inc, "node60"), "node60"), "new coefficient is not five")
    require(new_nodes["node60"] == (inc, inc), "two-increment body changed")
    require(new_nodes["node163"] == ("node6", "node54"), "no-push MP binding")
    require(new_nodes["node170"] == (("node36", ("node167", "node145")), "node57"),
            "cache-only Shift binding")
    require(read_json(PACKAGE / "machine" / "nodes.json") == new_nodes_json,
            "final AX11QH5 source nodes differ from the checked QH5 nodes")

    grammar = read_grammar(QH5 / "construction" / "inputs" / "q.grammar.json")
    old_sites, sites = source_sites(grammar, old_nodes), source_sites(grammar, new_nodes)
    old_code, code = resolve(old_sites), resolve(sites)
    require((len(old_sites), len(sites)) == (3775, 3714), "source site counts")
    require(code == list(map(freeze, read_json(QH5 / "machine" / "instructions.json"))),
            "independently resolved QH5 graph differs from frozen construction input")
    encoded_sites = [["".join(map(str, path)), op, arg] for path, op, arg in sites]
    require(encoded_sites == read_json(QH5 / "machine" / "sites.json"), "QH5 source address binding")

    old_paths, new_paths = occurrences(grammar, old_nodes, "node61"), occurrences(grammar, new_nodes, "node61")
    require(old_paths == new_paths and len(old_paths) == 61, "61 multiplier occurrences")
    cons_paths = occurrences(grammar, old_nodes, "node65")
    require(cons_paths == occurrences(grammar, new_nodes, "node65"), "Cons paths changed")
    require([path + (1, 1, 1, 0) for path in cons_paths] == old_paths,
            "multiplier body does not occur exactly once in each Cons")

    prefix = [
        ("dec", 2, 8, 1), ("inc", 7, 2), ("dec", 6, 4, 3), ("jump", 7),
        ("dec", 7, 7, 5), ("inc", 6, 6), ("jump", 4), ("jump", 0),
        ("dec", 7, 11, 9), ("inc", 2, 10), ("jump", 8),
        ("dec", 1, 15, 12), ("inc", 7, 13), ("inc", 6, 14), ("jump", 11),
        ("dec", 6, 21, 16), ("inc", 7, 17), ("dec", 6, 20, 18),
        ("inc", 1, 19), ("jump", 17), ("jump", 11),
    ]
    old_removed, new_removed, entries, blocks = set(), set(), {}, []
    for path in old_paths:
        old_ids = [i for i, (p, _, _) in enumerate(old_sites) if p[:len(path)] == path]
        new_ids = [i for i, (p, _, _) in enumerate(sites) if p[:len(path)] == path]
        require(old_ids == list(range(old_ids[0], old_ids[0] + 6)), "old body extent")
        require(new_ids == list(range(new_ids[0], new_ids[0] + 5)), "new body extent")
        for ids, instructions in ((old_ids, old_code), (new_ids, code)):
            start, end = ids[0], ids[-1] + 1
            require(all(instructions[i] == ("inc", 1, i + 1) for i in ids), "increment body")
            base = start - 22
            actual_prefix = []
            for row in instructions[base:base + 21]:
                actual_prefix.append(row[:2] + tuple(v - base for v in row[2:])
                                     if row[0] in ("inc", "dec") else ("jump", row[1] - base))
            require(actual_prefix == prefix, "21-site Cons unpair/pair prefix")
            require(instructions[start - 1] == ("dec", 7, end + 1, start), "multiplier guard")
            require(instructions[end] == ("jump", start - 1), "multiplier back edge")
        old_removed.update(old_ids)
        new_removed.update(new_ids)
        entries[old_ids[0]] = new_ids[0]
        blocks.append({"path": "".join(map(str, path)), "old_start": old_ids[0],
                       "new_start": new_ids[0], "old_length": 6, "new_length": 5})

    old_kept = [i for i in range(len(old_code)) if i not in old_removed]
    new_kept = [i for i in range(len(code)) if i not in new_removed]
    require(len(old_kept) == len(new_kept) == 3409, "outside source count")
    relocation = dict(zip(old_kept, new_kept))
    relocation.update(entries)

    def targets(row):
        return row[2:] if row[0] in ("inc", "dec") else row[1:] if row[0] == "jump" else ()

    def relocate(row):
        if row[0] in ("inc", "dec"):
            return row[:2] + tuple(relocation[t] for t in row[2:])
        return ("jump", relocation[row[1]]) if row[0] == "jump" else row

    for i, j in zip(old_kept, new_kept):
        require(relocate(old_code[i]) == code[j], "outside instruction/successor changed")
    for instructions, removed, starts in ((old_code, old_removed, set(entries)),
                                          (code, new_removed, set(entries.values()))):
        for i, row in enumerate(instructions):
            if i not in removed:
                require(all(t not in removed or t in starts for t in targets(row)),
                        "external entry into multiplier body interior")
    require(relocation[25] == 25 and old_sites[25][0] == sites[25][0], "scheduler seed site changed")
    binding = {"from_coefficient": 6, "to_coefficient": 5, "occurrences": 61,
               "unchanged_primitive_sites": 3409,
               "all_61_constructors_have_exact_unpair_pair_prefix": True,
               "only_formula_constructor_loop_bodies_change": True,
               "no_external_entries_to_body_interior": True,
               "all_resolved_outside_successors_preserved": True,
               "same_seed_site": 25, "blocks": blocks}
    require(binding == read_json(FROZEN / "source_binding.json"), "inherited binding receipt differs")
    return {"occurrences": 61, "outside_sites_and_successors": 3409,
            "old_sites": len(old_code), "new_sites": len(code),
            "exact_cons_prefix_sites": 21, "final_source_nodes_bound": True,
            "no_external_body_entries": True}


def check_exchange():
    certificate = read_json(FROZEN / "exchange_certificate.json")
    lines = certificate["lines"]
    formulas = []
    counts = {"K": 0, "S": 0, "MP": 0}

    def imp(a, b):
        return ("I", a, b)

    for i, line in enumerate(lines):
        formula, rule = freeze(line["formula"]), line["rule"]
        require(rule in counts, "unexpected exchange proof rule")
        counts[rule] += 1
        if rule == "K":
            a, b = map(freeze, line["parameters"])
            require(formula == imp(a, imp(b, a)), "invalid K instance")
        elif rule == "S":
            a, b, c = map(freeze, line["parameters"])
            require(formula == imp(imp(a, imp(b, c)), imp(imp(a, b), imp(a, c))),
                    "invalid S instance")
        else:
            major, minor = line["major"], line["minor"]
            require(0 <= major < i and 0 <= minor < i, "exchange proof forward dependency")
            require(formulas[major] == imp(formulas[minor], formula), "invalid exchange MP")
        formulas.append(formula)
    p, q, r = "P", "Q", "R"
    expected = imp(imp(p, imp(q, r)), imp(q, imp(p, r)))
    require(certificate["assumptions"] == [], "undischarged exchange assumptions")
    require(certificate["conclusion_line"] == len(lines) - 1, "exchange conclusion index")
    require(formulas[-1] == expected and len(lines) == 61, "exchange conclusion/length")
    return {"lines": len(lines), "rules": counts, "assumptions": [],
            "schema": "(P -> (Q -> R)) -> (Q -> (P -> R))",
            "dependency": "K and S derived from restricted rho8; retained Lean reference template"}


def verify():
    require(__debug__ and not sys.flags.optimize, "run without -O or PYTHONOPTIMIZE")
    provenance = read_json(FROZEN / "PROVENANCE.json")
    for record in provenance["files"]:
        actual = hashlib.sha256((FROZEN / record["file"]).read_bytes()).hexdigest()
        require(actual == record["sha256"], "inherited file hash mismatch: " + record["file"])

    # Import the preserved emitter checker alone. The builder and physical
    # interpreter are deliberately outside this small source-level replay.
    spec = importlib.util.spec_from_file_location("_inherited_qh5_commands", FROZEN / "check_commands.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.ROOT = QH5 / "construction"
    emitter = module.emitter_check()
    multiplier = check_multiplier()
    exchange = check_exchange()
    return {"status": "PASS", "emitter_tokens": emitter["tokens"],
            "emitter_coefficient": emitter["constructor_coefficient"],
            "complete_symbolic_emitter": emitter,
            "multiplier_binding": multiplier, "exchange": exchange,
            "frozen_hashes_checked": len(provenance["files"]),
            "scope": "Exact inherited QH5 emitter and finite source bindings plus flat exchange replay. The new AX11 splice and physical simulation are checked separately; no new kernel endpoint is claimed."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    arguments = parser.parse_args()
    result = verify()
    rendered = json.dumps(result, indent=2) + "\n"
    if arguments.output:
        arguments.output.write_text(rendered)
    print(rendered)
