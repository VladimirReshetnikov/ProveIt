#!/usr/bin/env python3
"""Unbounded literal runtime checking on certified per-leaf register families.

The source product invariant is independently verified before runtime work.
Each product coordinate is enlarged to an affine arithmetic progression m+d*N
(d=0 denotes {m}); every natural value in the delivered coordinate lies in it.
The original unary/list execution rules remain unchanged. Actual source runs
stay inside the delivered product facts; the enlarged affine families need not
be invariant. A complete calibrated blank initializer is a separate obligation.
"""
from pathlib import Path
import argparse
import hashlib
import importlib
import json
import math
import sys
import time

import check_source_product_invariant as inv


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def affine_family(mask, threshold):
    """Return a progression containing every concretized value, without sampling."""
    small = [n for n in range(threshold) if mask & (1 << n)]
    tails = [threshold + ((parity-threshold) % 2)
             for parity in (0, 1) if mask & (1 << (threshold+parity))]
    starts = small+tails
    inv.require(starts, 'An enabled coordinate has empty concretization')
    minimum = min(starts)
    difference_gcd = 0
    for value in starts:
        difference_gcd = math.gcd(difference_gcd, value-minimum)
    if tails:
        difference_gcd = math.gcd(difference_gcd, 2)
    # For every singleton, value-minimum is divisible by d. For a tail,
    # first-minimum and 2 are divisible by d, hence so is first+2*t-minimum.
    inv.require(all(value >= minimum for value in starts), 'Invalid lower endpoint')
    if difference_gcd:
        inv.require(all((value-minimum) % difference_gcd == 0 for value in starts),
                    'A singleton or tail start is outside the affine family')
        inv.require(not tails or 2 % difference_gcd == 0, 'A tail step is outside the family')
    else:
        inv.require(not tails and len(set(starts)) == 1, 'Only a singleton may have period zero')
    return minimum, difference_gcd


def restricted_case(s, table, lemmas, site, positive, families):
    pc, op, arg = site
    values = [s.add(s.num(minimum), tuple(period*x for x in s.var(2+i)))
              for i, (minimum, period) in enumerate(families)]
    if op == 'CD':
        inv.require(values[arg][0] >= 1 if positive else values[arg] == s.ZERO,
                    'The family does not enforce the decrement guard')
    physical = [None]*9
    for i, j in enumerate(s.r.PHY):
        physical[j] = values[i]
    result, overflow, delta, extra = physical.copy(), 0, 0, None
    if op == 'CI':
        result[s.r.PHY[arg]] = s.add(result[s.r.PHY[arg]], s.num(1))
        successor, overflow = s.r.inc(pc)
        extra = 1
    elif op == 'CD' and positive:
        result[s.r.PHY[arg]] = s.minus1(result[s.r.PHY[arg]])
        successor, overflow = s.r.inc(pc)
        delta = 1
    elif op in ('CD', 'CB'):
        successor, overflow = s.r.inc(s.r.strip(pc, '0', arg if op == 'CB' else 1))
    elif op == 'CC':
        successor = s.r.strip(pc, '1', arg)
    elif op == 'CH':
        successor = ''
    else:
        raise ValueError('Invalid source operation')
    state = s.State(96, [s.bit(1), s.BLANK],
                    [s.bit(int(b)) for b in pc]
                    + [s.run(0, s.add(s.var(1), s.num(64-len(pc)))), s.bit(1)]
                    + s.file_bits(physical))
    target = s.State(96, [s.bit(1), s.BLANK],
                     [s.bit(int(b)) for b in successor]
                     + [s.run(0, s.add(s.var(1), s.num(64+delta+overflow-len(successor)))), s.bit(1)]
                     + s.file_bits(result, extra))
    target_key = target.key()
    clock, motion, used, kinds = s.ZERO, s.ZERO, set(), {}
    for count in range(4000):
        key = state.key()
        if count and ((op == 'CH' and state.q == 254) or (op != 'CH' and key == target_key)):
            inv.require(s.nonnegative(clock) and clock[0] > 0, 'No positive instruction duration')
            if op != 'CH':
                inv.require(motion == s.num(-overflow), 'Incorrect final head displacement')
            return {'symbolic_steps': count, 'duration': clock, 'motion': motion,
                    'rows': used, 'kinds': kinds}
        clock, motion, event = state.step(table, lemmas, clock, motion)
        kinds[event[0]] = kinds.get(event[0], 0)+1
        if event[0] != 'list':
            used.add(event[1][:2])
    raise ValueError('The local symbolic certificate did not close within its proof-search cap')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine-dir', type=Path, required=True)
    parser.add_argument('--table', type=Path, required=True)
    parser.add_argument('--states', type=int, required=True)
    parser.add_argument('--sites', type=Path, required=True)
    parser.add_argument('--facts', type=Path, required=True)
    parser.add_argument('--summary', type=Path, required=True)
    parser.add_argument('--threshold', type=int, default=16)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    inv.require(__debug__ and not sys.flags.optimize, 'Assertions must be enabled')
    ordered, cfg, start, depth = inv.build_cfg(json.loads(args.sites.read_text()))
    facts = json.loads(args.facts.read_text())
    inherited_summary = json.loads(args.summary.read_text())
    invariant = inv.verify(ordered, cfg, start, facts, args.threshold)
    expectations = {'status': 'PASS_FINITE_PRODUCT_INVARIANT',
                    'source_sha256': digest(args.sites),
                    'initial_registers': list(inv.SEED),
                    'domain': list(range(args.threshold))+['large even', 'large odd'],
                    'instructions': len(cfg),
                    **{key: invariant[key] for key in ('forced_decrement_guards',
                            'unreachable_instructions', 'reachable_in_abstraction')}}
    for key, value in expectations.items():
        inv.require(inherited_summary.get(key) == value, f'Source summary mismatch: {key}')
    sys.path.insert(0, str(args.engine_dir.resolve()))
    s = importlib.import_module('symbolic_runtime')
    table = s.r.table(args.table)
    working = {q for q, _ in table}
    inv.require(len(working) == args.states and len(table) == 2*args.states, 'Incorrect table census')
    inv.require(set(table) == {(q,b) for q in working for b in (0,1)}, 'Incomplete binary table')
    inv.require(95 in working and 96 in working and 254 not in working, 'Incorrect fixed interfaces')
    inv.require({z for _,_,z in table.values()}-working == {254}, 'Incorrect halt outcome')
    lemmas, block_proofs = s.prove_blocks(table)
    terminal = {path: i for i, (path, _, _) in enumerate(ordered)}

    def locate(word):
        padded = word + '0'*depth
        for length in range(1, depth+1):
            if padded[:length] in terminal:
                inv.require('1' not in word[length:], 'Nonzero unused path tail')
                return terminal[padded[:length]]
        raise ValueError('No source target')

    # Explicitly connect the runtime helper's path arithmetic to the
    # independently built CFG used by the product-invariant proof.
    for i, (pc, op, arg) in enumerate(ordered):
        if op == 'CI':
            got = ('INC', arg, locate(s.r.inc(pc)[0]))
        elif op == 'CD':
            got = ('DEC', arg, locate(s.r.inc(pc)[0]), locate(s.r.inc(s.r.strip(pc, '0', 1))[0]))
        elif op == 'CB':
            got = ('JUMP', locate(s.r.inc(s.r.strip(pc, '0', arg))[0]))
        elif op == 'CC':
            got = ('JUMP', locate(s.r.strip(pc, '1', arg)))
        else:
            got = ('HALT',)
        inv.require(got == cfg[i], f'Runtime/source CFG disagreement at leaf {i}')

    args.output.parent.mkdir(parents=True, exist_ok=True)
    started, cases, used_rows = time.monotonic(), [], set()
    print('Independent source invariant, path interface, and four unbounded list schemas pass.', flush=True)
    for index, site in enumerate(ordered):
        if facts[index] is None:
            continue
        op, arg = site[1], site[2]
        guards = [False]
        if op == 'CD':
            guards = ([False] if facts[index][arg] & 1 else []) + ([True] if facts[index][arg] & ~1 else [])
        for positive in guards:
            masks = list(facts[index])
            if op == 'CD':
                masks[arg] = masks[arg] & ~1 if positive else 1
            families = [affine_family(mask, args.threshold) for mask in masks]
            try:
                answer = restricted_case(s, table, lemmas, site, positive, families)
            except (ValueError, AssertionError, KeyError) as error:
                failure = {'status': 'NOT_PROVED', 'site_index': index, 'site': site,
                           'positive': positive, 'families': families,
                           'prior_cases': len(cases), 'reason': str(error),
                           'seconds': time.monotonic()-started}
                args.output.write_text(json.dumps(failure, indent=2)+'\n')
                print(json.dumps(failure, indent=2), flush=True)
                raise SystemExit(1)
            used_rows.update(answer.pop('rows'))
            cases.append({'site_index': index, 'positive': positive,
                          'masks': masks, 'families': families, **answer})
            if len(cases) % 1000 == 0:
                print('proved', len(cases), 'restricted guards', round(time.monotonic()-started, 2), 'seconds', flush=True)
    expected_count = sum(0 if f is None else
                         int(bool(f[d[1]] & 1))+int(bool(f[d[1]] & ~1)) if d[0] == 'DEC' else 1
                         for f, d in zip(facts, cfg))
    # Parentheses avoid treating a bottom non-DEC node as an enabled case.
    expected_count = sum(0 if f is None else
                         (int(bool(f[d[1]] & 1))+int(bool(f[d[1]] & ~1)) if d[0] == 'DEC' else 1)
                         for f, d in zip(facts, cfg))
    inv.require(len(cases) == expected_count, 'Incomplete restricted case coverage')
    output = {'status': 'PASS_UNBOUNDED_SOURCE_RESTRICTED_RUNTIME',
              'working_states': args.states, 'transition_rows': len(table),
              'cases': len(cases), 'symbolic_steps': sum(c['symbolic_steps'] for c in cases),
              'minimum_actual_steps': min(c['duration'][0] for c in cases),
              'table_sha256': digest(args.table), 'source_sha256': digest(args.sites),
              'facts_sha256': digest(args.facts), 'source_summary_sha256': digest(args.summary),
              'checker_sha256': digest(Path(__file__)), 'invariant_checker_sha256': digest(Path(inv.__file__)),
              'engine_sha256': digest(Path(s.__file__)), 'helper_sha256': digest(Path(s.r.__file__)),
              'initial_leaf': start, 'source_cfg_sha256': inv.canonical_digest(cfg),
              'unreachable_source_leaves': invariant['unreachable_instructions'],
              'forced_decrement_guards': invariant['forced_decrement_guards'],
              'block_proofs': block_proofs,
              'directly_used_rows': sorted(used_rows),
              'seconds': time.monotonic()-started,
              'scope': 'Exact literal instruction contracts on affine families containing every certified per-leaf product fact, arbitrary gap and spare list, and exact whole-tape endpoints. Source invariant supplies induction between leaves. A complete calibrated blank initializer is a separate obligation. Ordinary mathematical checker, not a kernel theorem.'}
    args.output.write_text(json.dumps(output, indent=2)+'\n')
    args.output.with_name(args.output.stem+'_cases.json').write_text(json.dumps(cases, indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k not in ('block_proofs', 'directly_used_rows')}, indent=2), flush=True)


if __name__ == '__main__':
    main()
