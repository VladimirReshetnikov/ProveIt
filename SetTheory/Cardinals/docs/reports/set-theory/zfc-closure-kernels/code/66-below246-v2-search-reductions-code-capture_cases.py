#!/usr/bin/env python3
"""Generate exact finite source/target fixtures for transition-fold searches.

The literal instruction semantics are imported from the pinned context246
package. This driver is new. It does not infer that interval witnesses are
reachable; an optional inductive invariant is used only to choose admissible
finite test valuations. Generated fixtures are finite evidence, not a proof
of correctness for a modified machine.
"""
import argparse
from pathlib import Path
import hashlib
import json
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--baseline', type=Path, required=True,
                    help='Directory containing code/ and machine/ of context246')
    ap.add_argument('--intervals', type=Path,
                    help='Optional root interval-invariants.json')
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    base = args.baseline.resolve()
    sys.path.insert(0, str(base / 'code'))
    from check_literal_instructions import (read_table, program_sites,
                                           paint, expected, PHYSICAL)
    tablepath = base / 'machine/zfc_prefix246_old.tm'
    progpath = base / 'sources/Prog254.v'
    table = read_table(tablepath)
    sites = program_sites(progpath)
    intervals = None
    if args.intervals:
        intervals = json.loads(args.intervals.read_text())['invariants']
        assert len(intervals) == len(sites)
    first, full, metadata, seen = [], [], [], set()
    for idx, (pc, kind, reg) in enumerate(sites):
        iv = intervals[idx] if intervals is not None else None
        if intervals is not None and iv is None:
            continue
        guards = (False, True) if kind == 'CD' else (None,)
        for positive in guards:
            if iv is not None and kind == 'CD':
                if (not positive and iv[reg][0] > 0) or (positive and iv[reg][1] == 0):
                    continue
            regs = [(3*j) % 7 for j in range(9)]
            if iv is not None:
                regs = [0]*9
                for j, (lo, hi) in enumerate(iv):
                    regs[PHYSICAL[j]] = lo + (3*j) % 7 if hi == 9 else min(hi, lo+(3*j) % 7)
            if kind == 'CD':
                regs[PHYSICAL[reg]] = max(1, iv[reg][0] if iv is not None else 1) if positive else 0
            spares, span, head, state = [0], 40, 0, 96
            target = expected(pc, kind, reg, regs, spares, head, span)
            ones = paint(pc, span, regs, spares, head)
            initial = ones.copy()
            new, used = [], set()
            for steps in range(1, 10001):
                key = state, int(head in ones)
                used.add(state)
                if key not in seen:
                    seen.add(key)
                    new.append(dict(state=state, head=head, ones=sorted(ones),
                                    program_index=idx, guarded_fixture=len(full),
                                    source_step=steps-1, read=key[1]))
                write, direction, state = table[key]
                if write:
                    ones.add(head)
                else:
                    ones.discard(head)
                head += direction
                if state == 254 or (state == 96 and target and (head, ones) == target[:2]):
                    break
            else:
                raise RuntimeError(('Baseline failed to finish fixture', idx, positive))
            targetconf = dict(state=state, head=head, ones=sorted(ones))
            for config in new:
                first.append(dict(source=config, target=targetconf))
            full.append((96, 0, len(initial), *sorted(initial), state, head,
                         len(ones), *sorted(ones), len(used), *sorted(used)))
            metadata.append(dict(program_index=idx, pc=pc, instruction=kind,
                                 logical_register=reg, positive_guard=positive,
                                 physical_values=regs, spares=spares,
                                 header_distance=span, baseline_steps=steps))
    out = args.output
    out.mkdir(parents=True, exist_ok=True)
    with (out/'micro-contexts.txt').open('w') as stream:
        print(len(first), file=stream)
        for item in first:
            a, b = item['source'], item['target']
            print(a['state'], a['head'], len(a['ones']), *a['ones'],
                  b['state'], b['head'], len(b['ones']), *b['ones'], file=stream)
    with (out/'whole-instructions.txt').open('w') as stream:
        print(len(full), file=stream)
        for row in full:
            print(*row, file=stream)
    (out/'micro-contexts.json').write_text(json.dumps(first, separators=(',', ':'))+'\n')
    (out/'instruction-metadata.json').write_text(json.dumps(metadata, separators=(',', ':'))+'\n')
    result = dict(scope='finite baseline-derived test fixtures',
                  instructions=len(full), micro_contexts=len(first),
                  covered_transition_pairs=len(seen),
                  missing_pairs=sorted(set(table)-seen),
                  interval_filtered=intervals is not None,
                  table_sha256=hashlib.sha256(tablepath.read_bytes()).hexdigest(),
                  program_sha256=hashlib.sha256(progpath.read_bytes()).hexdigest())
    (out/'summary.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
