#!/usr/bin/env python3
"""Verify the complete finite graph premises of the PA194F zero-cut proof.

Usage: python3 four_site_cut.py P.instructions.json PF.instructions.json
No arithmetic-register sampling, solver, external library, or proof assistant.
The mathematical soundness argument is induction on source execution time.
"""
import argparse
import hashlib
import json
from pathlib import Path

ZERO_SITES = frozenset((3550, 3551, 3552, 3553))
EXPECTED_INSIDE_OLD = {
    3550: ['jump', 3553],
    3551: ['dec', 1, 3553, 3552],
    3552: ['jump', 3551],
    3553: ['jump', 3637],
}
EXPECTED_ENTRIES = {(3545, 3551), (3548, 3550)}


def require(claim, message):
    if not claim:
        raise ValueError(message)


def targets(code):
    if code[0] in ('inc', 'dec'):
        return code[2:]
    if code[0] == 'jump':
        return code[1:]
    return []


def check(program):
    require(len(program) == 3646, 'wrong source site count')
    entering = set()
    for pc, code in enumerate(program):
        require(isinstance(code, list) and code, f'malformed site {pc}')
        op = code[0]
        arities = {'halt': 1, 'jump': 2, 'inc': 3, 'dec': 4}
        require(op in arities and len(code) == arities[op], f'malformed site {pc}')
        if op in ('inc', 'dec'):
            require(type(code[1]) is int and 0 <= code[1] < 9,
                    f'bad register at {pc}')
        for dest in targets(code):
            require(type(dest) is int and 0 <= dest < len(program),
                    f'bad target at {pc}')
            if dest in ZERO_SITES and pc not in ZERO_SITES:
                require(op == 'dec' and code[1] == 6 and code[2] == dest,
                        f'outside edge does not force X=0: {pc}->{dest}')
                require(code[3] != dest, f'positive branch also enters cut at {pc}')
                entering.add((pc, dest))
        if pc in ZERO_SITES:
            require(not (op == 'inc' and code[1] == 6),
                    f'X can become positive inside zero cut at {pc}')
    require(entering == EXPECTED_ENTRIES, 'wrong complete cut boundary')
    require(25 not in ZERO_SITES, 'seed condition must be vacuous at site 25')
    return sorted(entering)


def verify(old, new):
    require(len(old) == len(new), 'program lengths differ')
    differences = [i for i, (a, b) in enumerate(zip(old, new)) if a != b]
    require(differences == [3553], 'unexpected changed instructions or targets')
    for pc, code in EXPECTED_INSIDE_OLD.items():
        require(old[pc] == code, f'wrong original instruction at {pc}')
    require(new[3553] == ['dec', 6, 3637, 3554], 'wrong replacement instruction')
    entries = check(old)
    require(check(new) == entries, 'programs have different zero-cut boundaries')
    return {
        'status': 'PASS',
        'source_sites': 3646,
        'changed_sites': differences,
        'register_proved_zero': 6,
        'zero_cut_sites': sorted(ZERO_SITES),
        'all_external_entry_edges': entries,
        'all_external_entries_are_zero_branches': True,
        'internal_instructions_preserve_zero': True,
        'seed_pc': 25,
        'seed_register_restrictions': [],
        'conclusion': 'Exact equality of all source configurations at every source time from site 25, for arbitrary natural initial register values.',
        'proof_kind': 'Finite syntactic premises of the stated mathematical induction; no new proof-assistant kernel theorem.',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('old', type=Path)
    parser.add_argument('new', type=Path)
    args = parser.parse_args()
    old_bytes, new_bytes = args.old.read_bytes(), args.new.read_bytes()
    receipt = verify(json.loads(old_bytes), json.loads(new_bytes))
    receipt['source_sha256'] = {
        'old': hashlib.sha256(old_bytes).hexdigest(),
        'new': hashlib.sha256(new_bytes).hexdigest(),
    }
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
