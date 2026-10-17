#!/usr/bin/env python3
"""Independent bounded semantic audit of the fourteen finite source rows.

The reference formulas come from finite_nbg.construct().  Expected truth values
are computed separately using membership-column sets and direct profiles, not
the formula builder or its abbreviations.  This checks a transcription on small
arbitrary relational structures; it is not a proof of NBG equivalence.

Run with finite_nbg.py and graph_wrapper.py on PYTHONPATH.
New audit code: MIT-0.
"""
import itertools
import json

from finite_nbg import construct
from graph_wrapper import evaluate, free, size


def direct_rows(n, relation):
    domain = set(range(n))
    members = {a: {x for x in domain if (x, a) in relation}
               for a in domain}
    sets = {x for x in domain if any((x, y) in relation for y in domain)}
    unions = {a: set().union(*(members[x] for x in members[a]))
              for a in domain}

    def represented(profile, candidates=domain):
        return any(members[x] == profile for x in candidates)

    rows = {}
    rows['2'] = len({frozenset(members[x]) for x in domain}) == n
    rows['3'] = all(represented({a, d}, sets) for a in sets for d in sets)
    rows['4'] = all(represented(unions[a], sets) for a in sets)
    rows['5'] = all(represented({x for x in domain if members[x] <= members[a]},
                                sets) for a in sets)
    rows['6'] = any(members[a] and all(any(y in members[z]
                                         for z in members[a])
                                     for y in members[a])
                    for a in sets)
    rows['7'] = all(not members[a]
                    or any(not (members[y] & members[a]) for y in members[a])
                    for a in domain)
    rows['A'] = (all(represented(sets - members[a]) for a in domain)
                 and all(represented(members[a] | members[d])
                         for a in domain for d in domain))
    rows['B'] = all(represented(unions[a]) for a in domain)
    rows['C'] = all(represented({z for z in domain
                                if any(members[z] == {x, y}
                                       for x in members[a] for y in members[d])})
                    for a in domain for d in domain)
    rows['D'] = all(represented({z for z in domain
                                if any(members[z] == unions[x]
                                       for x in members[a])})
                    for a in domain)
    rows['E'] = all(represented({z for z in domain
                                if any(members[z] == (members[x] & members[y])
                                       for x in members[a] for y in members[d])})
                    for a in domain for d in domain)
    rows['F'] = all(represented({x for x in domain
                                if any(members[u] == unions[x]
                                       for u in members[a])})
                    for a in domain)
    rows['G'] = represented({z for z in domain
                             if any(members[z] == {x, y} and x in members[y]
                                    for x in domain for y in domain)})
    rows['H'] = all(not (members[d] <= unions[a])
                    or any(members[c] <= members[a]
                           and members[d] <= unions[c] for c in sets)
                    for a in domain for d in sets)
    return rows


def main():
    formulas = construct()
    assert len(formulas) == 14
    assert all(not free(row['formula']) for row in formulas)
    observed = {row['source_row']: set() for row in formulas}
    structures = comparisons = 0
    for n in (1, 2, 3):
        domain = tuple(range(n))
        pairs = tuple(itertools.product(domain, repeat=2))
        for bits in range(1 << len(pairs)):
            relation = {p for i, p in enumerate(pairs) if bits & (1 << i)}
            expected = direct_rows(n, relation)
            for row in formulas:
                result = evaluate(row['formula'], domain, relation)
                assert result == expected[row['source_row']], (n, bits, row)
                observed[row['source_row']].add(result)
                comparisons += 1
            structures += 1
    assert all(values == {False, True} for values in observed.values())
    result = {'status': 'PASS', 'structures': structures,
              'formula_comparisons': comparisons,
              'domain_sizes': [1, 2, 3],
              'both_truth_values_seen_in_every_row': True,
              'axiom_count': len(formulas),
              'formula_nodes': sum(size(row['formula']) for row in formulas),
              'scope': 'bounded transcription regression; no consistency proof',
              'reviewed_generator': 'finite_nbg.py',
              'review_script': 'review_nbg14.py'}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
