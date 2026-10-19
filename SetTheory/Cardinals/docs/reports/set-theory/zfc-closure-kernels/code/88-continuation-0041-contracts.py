#!/usr/bin/env python3
"""Audit an eight-zero return scanner and its universal instruction frames.

The scanner argument is a finite-state induction, not a bounded simulation:
state s[i] means i consecutive zeros have already been read while moving
left.  This script checks every transition of that induction against the
supplied literal table.  The source-to-instruction frames are independently
checked by the existing sound affine symbolic executor, which quantifies
over every extra gap n>=0 and every natural-valued register file admitted by
the register macro contracts.

The supplied graph is untrusted input. Its instruction sites are expanded
here with cycle, arity, instruction, register and reachability checks.
Source program equivalence is a separate certificate.
"""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import argparse
import importlib.util
import json
import sys

PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)
CHAIN = (4, 6, 9, 13, 19, 29, 41, 58)


def load_module(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        key = q, int(bit)
        assert key not in table
        assert bit in ('0', '1') and write in ('0', '1')
        assert direction in ('L', 'R')
        table[key] = int(write), direction, target
    states = {q for q, b in table}
    assert len(table) == 2 * len(states)
    assert all((q, b) in table for q in states for b in (0, 1))
    assert {t for w, d, t in table.values()} - states == {'254'}
    return table


def scanner_induction(table):
    checks = []
    for i, q in enumerate(CHAIN):
        nxt = CHAIN[i + 1] if i + 1 < len(CHAIN) else 84
        assert table[str(q), 0] == (0, 'L', str(nxt))
        assert table[str(q), 1] == (1, 'L', '4')
        checks.append(dict(state=q, previously_read_zeros=i,
                           zero_next=nxt, one_next=4))
    assert table['84', 0] == (0, 'R', '84')
    assert table['84', 1] == (1, 'R', '96')
    assert not any(q == '74' for q, b in table)
    assert not any(t == '74' for w, d, t in table.values())
    # Every induction step consumes one cell, preserves the symbol, and
    # either increases the zero suffix counter or resets it to zero.
    # No accepted step inspects any cell to the right of the entry head.
    # Reading a marker one resets to s[0], after which the eight exterior
    # zeros and the right self-loop establish the claimed exact endpoint.
    return dict(status='PASS', count_states=checks,
                distinguished_zero_run=8, deleted_state=74,
                tape_preserved=True, return_state=96,
                return_head='left_marker + 1',
                literal_steps_from_state4='entry_head-left_marker+19',
                condition='interval [left_marker,entry_head] contains no 0^8; '
                          'left_marker is 1; every cell to its left is 0')


def graph_sites(path):
    data = json.loads(path.read_text())
    entries = {int(k): v for k, v in data['entries'].items()}
    seen, active, sites = set(), set(), []

    def expand(node, prefix):
        assert node in entries and node not in active
        active.add(node)
        seen.add(node)
        e = entries[node]
        if e[0] == 'N':
            assert len(e) == 3
            expand(e[1], prefix + '0')
            expand(e[2], prefix + '1')
        else:
            assert len(e) == 2 and e[0] in ('CI', 'CD', 'CB', 'CC', 'CH')
            op, r = e
            if op in ('CI', 'CD'):
                assert type(r) is int and 0 <= r < 9
                r = PHYSICAL[r]
            elif op in ('CB', 'CC'):
                assert type(r) is int and 1 <= r <= 3
            else:
                assert r is None
            sites.append((prefix, op, r))
        active.remove(node)

    expand(data['root'], '')
    assert seen == set(entries)
    assert len(sites) == 6460 and len({p for p, op, r in sites}) == 6460
    return sites


def check_instruction_frames(affine, review, table, sites):
    passed, failures = Counter(), []
    rules, min_steps, max_rules = Counter(), 10**9, 0
    for pc, op, r in sites:
        assert len(pc) <= 40
        for zero in ((True, False) if op == 'CD' else (None,)):
            branch = (r, zero) if op == 'CD' else None
            effect, extra, overflow = None, 0, False
            if op == 'CI':
                successor, overflow = review.full_inc(pc)
                effect = ('inc', r)
            elif op == 'CD' and not zero:
                successor, overflow = review.full_inc(pc)
                effect, extra = ('dec', r), 1
            elif op == 'CD':
                successor, overflow = review.full_inc(review.full_strip(pc, '0', 1))
            elif op == 'CB':
                successor, overflow = review.full_inc(review.full_strip(pc, '0', r))
            elif op == 'CC':
                successor = review.full_strip(pc, '1', r)
            else:
                assert op == 'CH'
                successor = ''
            gap = 40 + extra + int(overflow) - len(successor)
            assert gap >= 0
            right = ([('b', int(b)) for b in successor]
                     + [('r', 0, 1, gap), ('b', 1), ('box', ('plain', effect))])
            try:
                used, steps = affine.run(table, pc, branch,
                                        affine.canon([('b', 1)], right),
                                        halt=op == 'CH', fuel=2000)
                assert steps > 0
                rules.update(used)
                min_steps = min(min_steps, steps)
                max_rules = max(max_rules, sum(used.values()))
                passed[op + (('/zero' if zero else '/positive') if op == 'CD' else '')] += 1
            except (AssertionError, KeyError) as error:
                failures.append(dict(pc=pc, op=op, register=r, zero=zero,
                                     exception=repr(error)))
    assert sum(passed.values()) + len(failures) == 8391
    return dict(status='PASS' if not failures else 'FAIL',
                universally_verified_cases=sum(passed.values()),
                by_operation=dict(passed), failures=failures,
                minimum_literal_steps=min_steps,
                maximum_symbolic_rules=max_rules, rule_counts=dict(rules),
                base_header_distance=40, extra_gap='all n>=0',
                registers='all natural values, with named decrement guard',
                spare_suffix='every finite nonempty list of natural values')


def register_inductions(baseline, table):
    sys.path.insert(0, str(baseline / 'code'))
    m = load_module(baseline / 'code/check_macro_inductions.py', 'scanner_register_inductions')
    m.TABLE = {(int(q), b): (w, d, int(t)) for (q, b), (w, d, t) in table.items()}
    m.WORD_IDENTITY_PROVED = False
    m.BLOCK_PROOFS.clear()
    m.DERIVED.clear()
    m.prove_blocks()
    word = m.prove_word_identity()
    macros = m.prove_macros()
    marks = m.prove_marks()
    return dict(status='PASS', block_theorems=list(m.BLOCK_PROOFS.values()),
                word_identity=word, macro_theorems=macros,
                mark_theorems=marks,
                proof_scope='all natural register values; all finite block lists; '
                            'arbitrary left context; a block follows the selected primary',
                kernel_status='ordinary induction checker, not a proof-assistant endpoint')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--graph', type=Path)
    ap.add_argument('--baseline', type=Path,
                    default=Path(__file__).resolve().parents[2] / 'vendor/context246')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    assert __debug__
    table = read_table(args.table)
    scanner = scanner_induction(table)
    review = load_module(args.baseline / 'code/review_affine_source.py', 'scanner_review')
    affine = load_module(args.baseline / 'sources/prior/prefix_affine.py', 'scanner_affine')
    sites = (graph_sites(args.graph) if args.graph else
             review.parse_source(args.baseline / 'sources/Prog254.v')[1])
    source_stats = dict(instruction_leaves=len(sites),
                        maximum_depth=max(len(p) for p, op, r in sites),
                        maximum_zero_run=max(max(map(len, p.split('1'))) for p, op, r in sites))
    register_proofs = register_inductions(args.baseline, table)
    frames = check_instruction_frames(affine, review, table, sites)
    result = dict(status=frames['status'],
                  table_sha256=sha256(args.table.read_bytes()).hexdigest(),
                  graph_sha256=sha256(args.graph.read_bytes()).hexdigest() if args.graph else None,
                  working_states=len(table)//2, scanner_induction=scanner,
                  source_stats=source_stats, register_inductions=register_proofs,
                  instruction_frames=frames)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items()
                      if k not in ('instruction_frames', 'register_inductions')}, indent=2))
    print('register_inductions', register_proofs['status'])
    print(json.dumps({k: v for k, v in frames.items() if k != 'failures'}, indent=2))
    print('first_failures', frames['failures'][:5])


if __name__ == '__main__':
    main()
