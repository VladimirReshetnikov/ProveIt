#!/usr/bin/env python3
"""Finite diagnostics for the unary induction bootstrap.

Tests local first-order implications on all binary relations of size <= 4.
These relations are NOT asserted to satisfy the infinite unary schema.
The consistency equivalence is proved mathematically in the manuscript.
"""
import argparse
import json
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)


def indices(mask, size):
    return [i for i in range(size) if mask & (1 << i)]


def structure(size, relation):
    full = (1 << size) - 1
    members = [sum(((relation >> (x * size + a)) & 1) << x for x in range(size))
               for a in range(size)]
    eqclasses = [sum((members[x] == members[y]) << y for y in range(size))
                 for x in range(size)]
    has = lambda x, a: bool(members[a] & (1 << x))
    sat = [all((members[a] & eqclasses[x]) == eqclasses[x]
               for x in indices(members[a], size)) for a in range(size)]
    transitive = [all((members[x] & ~members[a]) == 0
                      for x in indices(members[a], size)) for a in range(size)]
    endpoints = [True] * (1 << size)
    for subset in range(1, 1 << size):
        elements = indices(subset, size)
        least = any(all(members[x] == members[z] or has(x, z) for z in elements)
                    for x in elements)
        greatest = any(all(members[z] == members[x] or has(z, x) for z in elements)
                       for x in elements)
        endpoints[subset] = least and greatest
    numerical = []
    for a in range(size):
        xs = indices(members[a], size)
        linear = (all(not has(x, x) for x in xs)
                  and all(members[x] == members[y] or has(x, y) or has(y, x)
                          for x in xs for y in xs)
                  and all(not (has(x, y) and has(y, z)) or has(x, z)
                          for x in xs for y in xs for z in xs))
        cuts = [t for t in range(size) if members[t] == members[a] or has(t, a)]
        cut_endpoints = all(endpoints[members[r] & members[t]]
                            for r in range(size) for t in cuts)
        numerical.append(sat[a] and transitive[a] and linear
                         and all(sat[x] for x in xs) and cut_endpoints)
    successor = [[members[b] == (members[a] | eqclasses[a]) for b in range(size)]
                 for a in range(size)]
    subsets = [sum(((members[x] & ~members[a]) == 0) << x for x in range(size))
               for a in range(size)]
    return full, members, eqclasses, numerical, successor, subsets


def suite(max_size=4):
    require(1 <= max_size <= 4, "supported diagnostic size is 1..4")
    rows = []
    total_predicates = 0
    total_bad_sources = 0
    total_local = 0
    witness_cases = 0
    empty_cut_cases = 0
    nonempty_cut_cases = 0
    base_failure_cases = 0
    step_failure_cases = 0
    for size in range(1, max_size + 1):
        relations = 1 << (size * size)
        numerical_cases = 0
        base_step_cases = 0
        bad_sources = 0
        for relation in range(relations):
            full, members, eqc, num, succ, subsets = structure(size, relation)
            has = lambda x, a: bool(members[a] & (1 << x))
            empty = [a for a in range(size) if members[a] == 0]
            for a in empty:
                require(num[a], "empty object is not numerical")
            for a in range(size):
                for b in range(size):
                    if members[a] == members[b]:
                        require(num[a] == num[b], "N is not profile invariant")
                if not num[a]:
                    continue
                numerical_cases += 1
                require(not has(a, a), "numerical self member")
                require(all(num[x] for x in indices(members[a], size)), "N not hereditary")
                for b in range(size):
                    if succ[a][b]:
                        require(num[b], "existing successor does not preserve N")
                if members[a]:
                    require(any(num[d] and succ[d][a] for d in indices(members[a], size)),
                            "nonempty numerical object lacks a predecessor")
                    least = [x for x in indices(members[a], size)
                             if all(members[x] == members[z] or has(x, z)
                                    for z in indices(members[a], size))]
                    require(least and all(members[x] == 0 for x in least),
                            "least numerical members are not empty")
            # Every arbitrary truth predicate is used; no definability
            # assumption or source-specific parameter is inserted.
            for good in range(1 << size):
                total_predicates += 1
                q = lambda a: bool(good & (1 << a))
                base = all(q(e) for e in empty)
                step = all(not (num[a] and succ[a][b] and q(a)) or q(b)
                           for a in range(size) for b in range(size))
                if base and step:
                    base_step_cases += 1
                false = full ^ good
                for n in range(size):
                    if not num[n] or q(n):
                        continue
                    if base and step:
                        bad_sources += 1
                    # If a weak unary filter existed here, the endpoint
                    # argument in the paper would contradict base+step.
                    witnesses = [b for b in range(size)
                                 if not (members[b] & ~false)
                                 and not ((subsets[n] & false) & ~members[b])]
                    if base and step:
                        require(not witnesses, "induction bootstrap implication fails")
                    for b in witnesses:
                        witness_cases += 1
                        cut = members[b] & members[n]
                        if cut:
                            nonempty_cut_cases += 1
                            cs = [c for c in indices(cut, size)
                                  if all(members[c] == members[z] or has(c, z)
                                         for z in indices(cut, size))]
                            require(bool(cs), "nonempty cut lacks least failure")
                            c = cs[0]
                        else:
                            empty_cut_cases += 1
                            c = n
                        require(num[c] and not q(c), "least failure is not a numerical failure")
                        if not members[c]:
                            require(not base, "empty failure contradicts base")
                            base_failure_cases += 1
                        else:
                            predecessors = [d for d in indices(members[c], size) if succ[d][c]]
                            require(bool(predecessors), "least failure lacks predecessor")
                            d = predecessors[0]
                            require(q(d) and not step, "least failure does not contradict step")
                            step_failure_cases += 1
        total_bad_sources += bad_sources
        total_local += numerical_cases
        rows.append({"size": size, "relations": relations,
                     "numerical_object_cases": numerical_cases,
                     "predicates_satisfying_base_and_existing_step": base_step_cases,
                     "bad_sources_without_required_unary_filter": bad_sources})
    # Exact lower boundary on matrix freedom: all closed matrices have a
    # truth value, and the two-object empty/universal structure covers both.
    size, members = 2, [0, 3]
    zero_slot_checks = 0
    for source in range(2):
        support = sum(((members[x] & ~members[source]) == 0) << x for x in range(2))
        for truth in (False, True):
            selected = 3 if truth else 0
            output = 1 if truth else 0
            require(not (members[output] & ~selected), "closed-matrix upper clause")
            require(not ((support & selected) & ~members[output]), "closed-matrix lower clause")
            zero_slot_checks += 1
    # The unary empty-object predicate separates the two entries. At source
    # empty it requires the absent singleton {empty}.
    require(all(m != 1 for m in members), "control singleton unexpectedly exists")
    return {"status": "passed", "relations": sum(x["relations"] for x in rows),
            "arbitrary_unary_predicates": total_predicates,
            "local_numerical_object_cases": total_local,
            "bootstrap_bad_sources": total_bad_sources, "by_size": rows,
            "constructed_least_failure_cases": witness_cases,
            "empty_intersection_branch": empty_cut_cases,
            "nonempty_intersection_branch": nonempty_cut_cases,
            "base_failures_exhibited": base_failure_cases,
            "step_failures_exhibited": step_failure_cases,
            "closed_matrix_model": {"members": members, "cases": zero_slot_checks,
                                    "unary_empty_matrix_fails_at_source": 0},
            "scope": "Finite local lemma diagnostics; no tested relation is claimed to model the infinite unary theory."}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-size", type=int, default=4)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = json.dumps(suite(args.max_size), indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(result)
    print(result, end="")
