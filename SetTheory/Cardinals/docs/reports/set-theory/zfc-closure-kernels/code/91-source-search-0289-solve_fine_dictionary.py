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
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent / "runtime/code"))
from audit_fine_grammar import make_vocabulary

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--seed", action="append", type=Path, required=True)
    parser.add_argument("--repeat-dictionary", action="store_true")
    parser.add_argument("--max-rules", type=int, default=127)
    parser.add_argument("--seconds", type=float, default=120)
    args = parser.parse_args()
    base = args.package
    source, terminals, names, allowed, encode_old = make_vocabulary()
    symbols = json.loads((base / "inputs/semantic-symbols.json").read_text())
    encode = {name: encode_old(c) for c,name in symbols.items()}
    universe = set()
    seeds = []
    for path in args.seed:
        d = json.loads(path.read_text())
        seeds.append(d)
        universe.update(w for w, left, right in d["rules"])
    if args.repeat_dictionary:
        frequency = Counter()
        strings = set(names[q] for q in source["required_entry_roots"])
        for w in strings:
            for length in range(2, min(80, len(w)) + 1):
                frequency.update(w[i:i + length] for i in range(len(w) - length + 1))
        universe.update(w for w, n in frequency.items() if n >= 2)
    universe.update(names.values())
    universe.difference_update(terminals)
    words = sorted(universe, key=lambda w: (len(w), w))
    domains = {}
    for w in words:
        choices = []
        for k in range(1, len(w)):
            a, b = w[:k], w[k:]
            if not (a in universe or a in terminals) or not (b in universe or b in terminals):
                continue
            if a in terminals and not allowed[a] & 1:
                continue
            if b in terminals and not allowed[b] & 2:
                continue
            choices.append((a, b))
        domains[w] = choices

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
                if c not in terminals:
                    constraint([(z[w, a, b], 1), (x[c], -1)], ub=0)
    released = {24, 89, 107, 152, 154, 175, 188, 207, 213, 245}
    mandatory = {names[q] for q in source["required_entry_roots"] if q not in released}
    locks = (base / "inputs/state_reduction/bootstrap-lock54.txt").read_text().splitlines()[1:]
    for row in locks:
        w, bit, target = row.split()
        w,target=encode_old(w),encode_old(target)
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
                    elif child in terminals:
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
            if w in terminals or w in live:
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
        args.output.write_text(json.dumps(output, indent=2) + "\n")
        summary["candidate_rules"] = len(selected)
        summary["candidate_path"] = str(args.output)
    args.output.with_suffix(".summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2), flush=True)


if __name__ == "__main__":
    main()
