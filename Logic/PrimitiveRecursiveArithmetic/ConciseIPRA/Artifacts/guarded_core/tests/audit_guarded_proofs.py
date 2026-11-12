"""Audit guarded atomic D occurrences in named test derivations.

This inspects generated proofs, not the checker implementation, and is
untrusted test support. No checker imports it.
"""
import json
from pathlib import Path
import build_root_cases as builder


def audit_formula(formula):
    if formula[0] == 'eq':
        return 0, 0
    if formula[0] == 'q':
        return audit_formula(formula[2])
    if formula[0] == 'd':
        matrix = formula[3]
        count, bad = audit_formula(matrix)
        if matrix[0] != 'eq':
            return count, bad
        guarded = all(isinstance(t, tuple) and t[0] == 'i'
                      and t[1] == ('v', formula[2]) and t[2] == 0
                      for t in matrix[1:])
        return count + 1, bad + int(not guarded)
    raise ValueError(formula)


def audit(proof):
    count, bad = audit_formula(proof['goal'])
    for key in ('major', 'minor', 'premise', 'continuation'):
        if key in proof:
            c, b = audit(proof[key])
            count += c
            bad += b
    return count, bad


def main():
    rows = []
    for case in builder.build_proofs():
        count, bad = audit(case['proof'])
        row = {'name': case['name'],
               'atomic_D_occurrences_in_named_proof': count,
               'unguarded_occurrences': bad,
               'canonical_goal': case['canonical_goal']}
        rows.append(row)
        if case['canonical_goal'] and bad:
            raise ValueError(row)
    destination = Path(__file__).resolve().parents[1] / 'evidence/guard_audit.json'
    destination.write_text(json.dumps(rows, indent=2) + '\n')
    print(json.dumps(rows, indent=2))


if __name__ == '__main__':
    main()
