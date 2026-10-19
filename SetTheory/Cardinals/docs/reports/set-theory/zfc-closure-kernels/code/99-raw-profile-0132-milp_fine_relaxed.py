#!/usr/bin/env python3
"""Search a finite grammar dictionary with joint caller routing using MILP.

The solver supplies proposals only. Its numerical statuses are not trusted as
mathematical certificates. Every positive proposal needs independent grammar,
source-bisimulation, runtime and initialization checks.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--fine-map", type=Path, required=True)
    parser.add_argument("--fine-locks", type=Path, required=True)
    parser.add_argument("--orientation-permissions", type=Path)
    parser.add_argument("--seed", action="append", type=Path, required=True)
    parser.add_argument("--vocabulary", action="append", type=Path, default=[],
                        help="Add exact words from a grammar without treating it as a feasible seed")
    parser.add_argument("--rotation-rounds", type=int, default=0,
                        help="Close the finite dictionary under valid binary-tree rotations this many times")
    parser.add_argument("--repeat-dictionary", action="store_true")
    parser.add_argument("--max-rules", type=int, default=127)
    parser.add_argument("--seconds", type=float, default=120)
    args = parser.parse_args()
    base = args.package
    source = json.loads((base / "inputs/closed-sequence-grammar-next22.json").read_text())
    symbols = json.loads((base / "inputs/semantic-symbols.json").read_text())
    fine = json.loads(args.fine_map.read_text())
    spell = lambda w: "".join(fine["atom_words"][c] for c in w)
    encode = {v: fine["atom_words"][k] for k, v in symbols.items()}
    symbols = {w: c for c, w in fine["atom_words"].items()}
    lines = (base / "inputs/semantic.txt").read_text().splitlines()
    nr, nroot, _ = map(int, lines[0].split())
    names = {int(q): spell(w) for k, w, q in map(str.split, lines[1:nr + 1])}
    allowed = {spell(c): int(m) for c, m in map(str.split, lines[nr + 1 + nroot:])}
    permissions = json.loads(args.orientation_permissions.read_text()) if args.orientation_permissions else []
    for p in permissions:
        assert allowed[p["word"]] == p["old_mask"] and p["new_mask"] == 3
        allowed[p["word"]] = 3
    universe = set()
    seeds = []
    for path in args.seed:
        d = json.loads(path.read_text())
        seeds.append(d)
        universe.update(w for w, left, right in d["rules"])
    override = seeds[0].get("source_override")
    if override:
        assert override["state"] == 76 and override["original_word"] == names[76]
        names[76] = override["new_word"]
        assert all(d.get("source_override") == override for d in seeds)
    if args.repeat_dictionary:
        frequency = Counter()
        strings = set(names[q] for q in source["required_entry_roots"])
        for w in strings:
            for length in range(2, min(80, len(w)) + 1):
                frequency.update(w[i:i + length] for i in range(len(w) - length + 1))
        universe.update(w for w, n in frequency.items() if n >= 2)
    universe.update(names.values())
    universe.difference_update(symbols)
    for path in args.vocabulary:
        universe.update(w for w, left, right in json.loads(path.read_text())["rules"] if w not in symbols)
    def choices_for(w, dictionary):
        choices = []
        for k in range(1, len(w)):
            a, b = w[:k], w[k:]
            if not (a in dictionary or a in symbols) or not (b in dictionary or b in symbols):
                continue
            if a in symbols and not allowed[a] & 1:
                continue
            if b in symbols and not allowed[b] & 2:
                continue
            choices.append((a, b))
        return choices
    rotation_sizes = [len(universe)]
    for round_index in range(args.rotation_rounds):
        prior = {w: choices_for(w, universe) for w in universe}
        added = set()
        for w, alternatives in prior.items():
            for a, b in alternatives:
                for x, y in prior.get(a, []):
                    v = y + b
                    if not (x in symbols and not allowed[x] & 1) and not (y in symbols and not allowed[y] & 1):
                        if v not in symbols:
                            added.add(v)
                for x, y in prior.get(b, []):
                    v = a + x
                    if not (y in symbols and not allowed[y] & 2) and not (x in symbols and not allowed[x] & 2):
                        if v not in symbols:
                            added.add(v)
        universe.update(added)
        rotation_sizes.append(len(universe))
        print("ROTATION_CLOSURE", round_index + 1, len(universe), flush=True)
    words = sorted(universe, key=lambda w: (len(w), w))
    domains = {w: choices_for(w, universe) for w in words}

    variable_names, lower, upper, objective = [], [], [], []
    def variable(name, cost=0):
        v = len(variable_names)
        variable_names.append(name)
        lower.append(0)
        upper.append(1)
        objective.append(cost)
        return v
    x = {w: variable(("word", w), 1) for w in words}
    z = {(w, a, b): variable(("rule", w, a, b)) for w in words for a, b in domains[w]}
    rows, lo, hi = [], [], []
    def constraint(terms, lb=-np.inf, ub=np.inf):
        rows.append(dict(terms))
        lo.append(lb)
        hi.append(ub)
    for w in words:
        constraint([(x[w], -1), *((z[w, a, b], 1) for a, b in domains[w])], 0, 0)
        for a, b in domains[w]:
            for c in set((a, b)):
                if c not in symbols:
                    constraint([(z[w, a, b], 1), (x[c], -1)], ub=0)
    released = {24, 89, 107, 152, 154, 175, 188, 207, 213, 245}
    mandatory = {names[q] for q in source["required_entry_roots"] if q not in released}
    lock_lines = args.fine_locks.read_text().splitlines()
    assert len(lock_lines)-1 == int(lock_lines[0])
    locks = lock_lines[1:]
    for row in locks:
        w, bit, target = row.split()
        # Locks already use exact fine-token words.
        mandatory.add(w)
        matching = [z[w, a, b] for a, b in domains[w] if (a, b)[int(bit)] == target]
        constraint([(v, 1) for v in matching], 1, 1)
    for w in mandatory:
        lower[x[w]] = upper[x[w]] = 1

    groups = defaultdict(list)
    for c in source["left_entry_projection_constraints"]:
        r = c["reason"]
        prefix = c["prefix"]
        if r.get("via") == 177:
            prefix = str(r["previous"]) + prefix
        assert 1 <= len(prefix) <= 2
        groups[r["source"], r["read"]].append((prefix, "".join(encode[t] for t in c["word"])))
    route_variables = defaultdict(list)
    for group, cs in groups.items():
        for w in words:
            for a, b in domains[w]:
                conditions = []
                valid = True
                for prefix, target in cs:
                    child = (a, b)[int(prefix[0])]
                    if len(prefix) == 1:
                        if child != target:
                            valid = False
                            break
                    elif child in symbols:
                        valid = False
                        break
                    else:
                        matching = [z[child, ca, cb] for ca, cb in domains[child] if (ca, cb)[int(prefix[1])] == target]
                        if not matching:
                            valid = False
                            break
                        conditions.append(matching)
                if not valid:
                    continue
                v = variable(("route", *group, w, a, b))
                route_variables[group].append((v, w))
                constraint([(v, 1), (z[w, a, b], -1)], ub=0)
                for matching in conditions:
                    constraint([(v, 1), *((child_var, -1) for child_var in matching)], ub=0)
        assert route_variables[group], group
        constraint([(v, 1) for v, w in route_variables[group]], 1, 1)
    constraint([(v, 1) for v in x.values()], ub=args.max_rules)
    # Exact integer positive controls for the formulation itself. The final
    # state-budget inequality is deliberately excluded: a known 128-rule seed
    # should violate a requested 127 budget while satisfying every other row.
    seed_model_checks = []
    for seed in seeds:
        graph = {w: (a, b) for w, a, b in seed["rules"]}
        route_map = {(r["source"], r["read"]): r["word"] for r in seed["routes"]}
        assignment = [0] * len(variable_names)
        for w, (a, b) in graph.items():
            assignment[x[w]] = assignment[z[w, a, b]] = 1
        for group, possibilities in route_variables.items():
            expected = route_map[group]
            picked = [v for v, w in possibilities if w == expected and tuple(variable_names[v][-2:]) == graph[expected]]
            assert len(picked) == 1
            assignment[picked[0]] = 1
        for i, row in enumerate(rows[:-1]):
            value = sum(coefficient * assignment[v] for v, coefficient in row.items())
            assert lo[i] <= value <= hi[i], ("known seed violates model", i, value, lo[i], hi[i])
        assert all(lb <= value <= ub for value, lb, ub in zip(assignment, lower, upper))
        seed_model_checks.append({"status": "PASS_EXACT_INTEGER_ASSIGNMENT", "rules": len(graph),
                                  "linear_rows_checked": len(rows) - 1, "budget_row_excluded": True})
    rr, cc, dd = [], [], []
    for i, terms in enumerate(rows):
        for j, value in terms.items():
            rr.append(i)
            cc.append(j)
            dd.append(value)
    matrix = coo_matrix((dd, (rr, cc)), shape=(len(rows), len(variable_names))).tocsc()
    start = time.monotonic()
    print("MODEL", len(words), "words", len(z), "rules", len(variable_names), "variables", len(rows), "constraints", flush=True)
    result = milp(np.asarray(objective), integrality=np.ones(len(variable_names)),
                  bounds=Bounds(np.asarray(lower), np.asarray(upper)),
                  constraints=LinearConstraint(matrix, np.asarray(lo), np.asarray(hi)),
                  options={"time_limit": args.seconds, "mip_rel_gap": 0.0})
    summary = {"status": "NO_VALIDATED_MACHINE", "solver_status": int(result.status),
               "solver_message": result.message, "seconds": time.monotonic() - start,
               "dictionary_words": len(words), "possible_binary_rules": len(z),
               "variables": len(variable_names), "constraints": len(rows),
               "rotation_closure_dictionary_sizes": rotation_sizes,
               "known_seed_model_checks": seed_model_checks,
               "bound": args.max_rules, "input_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in args.seed},
               "scope": "Finite-dictionary numerical MILP proposal search. Infeasibility status is not an independently checked exact certificate, and says nothing about unrestricted grammars."}
    if result.x is not None:
        selected = [(w, a, b) for (w, a, b), v in z.items() if result.x[v] > 0.5]
        routes = []
        for group, possibilities in route_variables.items():
            selected_route = [w for v, w in possibilities if result.x[v] > 0.5]
            assert len(selected_route) == 1
            routes.append({"source": group[0], "read": group[1], "word": selected_route[0]})
        graph = {w: (a, b) for w, a, b in selected}
        live = set()
        def visit(w):
            if w in symbols or w in live:
                return
            live.add(w)
            for c in graph[w]:
                visit(c)
        for w in mandatory | {r["word"] for r in routes}:
            visit(w)
        selected = [[w, *graph[w]] for w in sorted(live)]
        output = {"status": "ABSTRACT_FINE_ROUTING_GRAMMAR_ONLY", "rules_count": len(selected),
                  "framework_states": 118, "erase177": True, "retarget": -2,
                  "properties": [], "roots": sorted(mandatory), "routes": routes,
                  "rules": selected, "milp_search": summary}
        output["terminal_orientation_relaxations"] = permissions
        if override:
            output["source_override"] = override
        args.output.write_text(json.dumps(output, indent=2) + "\n")
        summary["candidate_rules"] = len(selected)
        summary["candidate_path"] = str(args.output)
    args.output.with_suffix(".summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
