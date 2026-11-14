#!/usr/bin/env python3
"""Search U208 aliases/one-row folds using harvested source-frame windows.

Discovery only: accepted results must be checked by complete fresh symbolic
runtime and blank initialization before any machine-correctness claim.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import time

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'sources208/U208_ConPA_Entry_Context_2026-10-29/u208_conpa_entry_context_2026-10-29'
spec = importlib.util.spec_from_file_location('discovery', PACKET / 'research/discover_folds.py')
d = importlib.util.module_from_spec(spec)
spec.loader.exec_module(d)


def fast_remove_subsumed(contexts):
    """The same exact cylinder union, using integer masks for subsumption."""
    unique = sorted(set(contexts), key=lambda c: (len(c), c))
    if not unique:
        return []
    positions = sorted({p for context in unique for p, bit in context})
    indices = {p: i for i, p in enumerate(positions)}
    encoded = []
    for context in unique:
        mask = value = 0
        for pos, bit in context:
            flag = 1 << indices[pos]
            mask |= flag
            if bit:
                value |= flag
        encoded.append((mask, value, context))
    known = {}
    result = []
    for mask, value, context in encoded:
        if any(other & mask == other and value & other in values
               for other, values in known.items()):
            continue
        result.append(context)
        known.setdefault(mask, set()).add(value)
    return result


d.remove_subsumed = fast_remove_subsumed


def compress_windows(values, radius):
    """Exact union of bit cylinders, simplified by one-variable absorption."""
    width = 2 * radius + 1
    full = (1 << width) - 1
    terms = {(full, value) for value in values}
    primes = set()
    while terms:
        combined, used = set(), set()
        for mask, value in terms:
            for shift in range(width):
                bit = 1 << shift
                if mask & bit and (mask, value ^ bit) in terms:
                    used.add((mask, value))
                    combined.add((mask ^ bit, value & ~bit))
        primes.update(terms - used)
        terms = combined
    # A greedy cover removes redundant primes but preserves exactly the union.
    remaining = set(values)
    selected = []
    while remaining:
        term = max(primes, key=lambda mv: sum((v & mv[0]) == mv[1] for v in remaining))
        selected.append(term)
        remaining = {v for v in remaining if (v & term[0]) != term[1]}
        primes.remove(term)
    contexts = []
    for mask, value in selected:
        context = {}
        for pos in range(-radius, radius + 1):
            shift = radius - pos
            if mask & (1 << shift):
                context[pos] = (value >> shift) & 1
        contexts.append(context)
    return contexts


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('contexts', type=Path)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--mode', choices=['aliases', 'folds'], default='folds')
    p.add_argument('--limit', type=int, default=31)
    p.add_argument('--history-depth', type=int, default=0)
    p.add_argument('--include-initial', action='store_true')
    args = p.parse_args()
    data = json.loads(args.contexts.read_text())
    table_path = ROOT / data['input_table']
    table = d.read_table(table_path)
    states = sorted({q for q, b in table})
    contexts = {int(q): compress_windows(values, data['radius'])
                for q, values in data['windows'].items()}
    if args.history_depth:
        histories = d.history_contexts(table, args.history_depth)
        for q in contexts:
            joint = []
            for source in contexts[q]:
                for history in histories[q]:
                    if any(pos in source and source[pos] != bit for pos, bit in history):
                        continue
                    joint.append(tuple(sorted((source | dict(history)).items())))
            contexts[q] = [dict(c) for c in d.remove_subsumed(joint)]
    compressed_path = args.output.with_suffix('.contexts.json')
    compressed_path.write_text(json.dumps(contexts, indent=2) + '\n')
    rng = random.Random(292110)
    started = time.monotonic()
    pairs = mutations = exact_checks = 0
    results = []
    for drop in states:
        if drop == 0:
            continue
        for keep in states:
            if keep == drop or (keep == 0 and not args.include_initial):
                continue
            def row_image(row):
                return row[:2] + (d.projected(row[2], drop, keep),)
            bits = [0] if args.mode == 'aliases' else (0, 1)
            for changed_bit in bits:
                if args.mode == 'folds' and row_image(table[drop, 1-changed_bit]) != row_image(table[keep, 1-changed_bit]):
                    continue
                pairs += 1
                inputs = [(state, bit, context)
                          for state in (drop, keep)
                          for bit in (changed_bit, 1-changed_bit)
                          for context in contexts[state]
                          if 0 not in context or context[0] == bit]
                if args.mode == 'aliases':
                    replacements = [(0, *table[keep, 0])]
                else:
                    replacements = [(changed_bit, write, direction, helper)
                                    for helper in states if helper != drop
                                    for direction in (-1, 1)
                                    for write in (changed_bit, 1-changed_bit)]
                for replacement in replacements:
                    mutations += 1
                    if not all(d.random_screen(table, state, bit, context, drop, keep,
                                               replacement, rng, args.limit, 254)
                               for state, bit, context in inputs
                               for _ in range(2)):
                        continue
                    exact_checks += 1
                    cases = []
                    for state, bit, context in inputs:
                        branches = d.exact_case(table, state, bit, context, drop, keep,
                                                replacement, args.limit, 254)
                        if branches is None:
                            break
                        cases.append({'old_state': state, 'read': bit,
                                      'context': context, 'branches': branches})
                    else:
                        hit = {'remove': drop, 'keep': keep,
                               'replacement': replacement, 'cases': cases}
                        results.append(hit)
                        print('FOUND', drop, keep, replacement, flush=True)
        if drop % 25 == 0:
            print('PROGRESS', drop, pairs, mutations, exact_checks,
                  len(results), round(time.monotonic() - started, 2), flush=True)
    report = {'scope': __doc__, 'context_file': str(args.contexts),
              'context_sha256': hashlib.sha256(args.contexts.read_bytes()).hexdigest(),
              'mode': args.mode, 'limit': args.limit,
              'history_depth_intersected': args.history_depth,
              'initial_keeper_included': args.include_initial,
              'pairs': pairs, 'mutations': mutations, 'exact_checks': exact_checks,
              'results': results, 'seconds': time.monotonic() - started,
              'cylinders': sum(map(len, contexts.values())),
              'input_sha256': hashlib.sha256(table_path.read_bytes()).hexdigest()}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'results'}, indent=2))


if __name__ == '__main__':
    main()
