#!/usr/bin/env python3
"""Find certified safe root frames from every working-state blank start.

The first-write quotient is exact: every preceding write is zero, and tapes
are translated so the head after the first one-write is at coordinate zero.
Zero-write cycles are separately recorded. The subsequent runs are bounded
literal executions; failure to find a frame is not an eventual-nonreachability
claim. Positive frames include the whole infinite tape via finite one-support,
all spare blocks, a certificate from ProveIt's existing safe_seed254.py, and
an independent dense replay from the selected genuine blank start.

This search does not establish runtime simulation or the consistency theorem.
The default physical map and spare condition are those of routed245.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

PHYSICAL = (6, 2, 0, 4, 3, 7, 8, 5, 1)

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def read_table(path, halt):
    table, declared = {}, None
    for number, line in enumerate(Path(path).read_text().splitlines(), 1):
        line = line.strip()
        if not line:
            continue
        if line.startswith('#'):
            words = line.split()
            if len(words) == 3 and words[:2] == ['#!', 'start']:
                declared = int(words[2])
            continue
        q, b, w, direction, nxt = line.split()
        q, b, w, nxt = map(int, (q, b, w, nxt))
        if q < 0 or nxt < 0 or b not in (0, 1) or w not in (0, 1) or direction not in ('L', 'R'):
            raise ValueError(f'invalid row {number}')
        if (q, b) in table:
            raise ValueError(f'duplicate row {number}')
        table[q, b] = (w, 1 if direction == 'R' else -1, nxt)
    states = {q for q, b in table}
    if halt in states or set(table) != {(q, b) for q in states for b in (0, 1)}:
        raise ValueError('every working state needs both rows; halt must be separate')
    if {t for w, d, t in table.values()} - states != {halt}:
        raise ValueError('the sole external target must be the selected halt label')
    if declared is not None and declared not in states:
        raise ValueError('declared start is not a working state')
    return table, states, declared

def classes(table, states, halt, preferred):
    groups = defaultdict(list)
    order = sorted(states, key=lambda q: (q != preferred, q))
    for start in order:
        q, head, path, seen = start, 0, [], {}
        while q not in seen:
            if q == halt:
                key = ('blank_halt',)
                extra = {'final_head': head}
                break
            seen[q] = len(path)
            w, d, nxt = table[q, 0]
            path.append([q, head, w, d, nxt])
            head += d
            q = nxt
            if w:
                key = ('first_write', q, -d)
                extra = {'translation': head}
                break
        else:
            key = ('blank_cycle',)
            entry = seen[q]
            extra = {'cycle_start_index': entry,
                     'cycle_head_displacement': head - path[entry][1]}
        groups[key].append({'start': start, 'prefix_steps': len(path),
                            'literal_zero_read_path': path, **extra})
    return [{'kind': key[0], 'state': key[1] if len(key) > 1 else None,
             'one_offset': key[2] if len(key) > 2 else None,
             'members': members} for key, members in groups.items()]

def parse_frame(head, ones, physical, minimum_gap, minimum_spares, classify):
    if not ones or min(ones) != head - 1:
        return None
    right = sorted(x for x in ones if x >= head)
    if not right:
        return None
    header, maximum = right[0], right[-1]
    if header - head < minimum_gap:
        return None
    cursor, values = header + 1, []
    while cursor <= maximum:
        if cursor in ones or cursor + 1 not in ones:
            return None
        begin = cursor + 1
        cursor = begin
        while cursor in ones:
            cursor += 1
        values.append(cursor - begin - 1)
    if len(values) < 9 + minimum_spares:
        return None
    logical = [values[physical[i]] for i in range(9)]
    certificate = classify(logical)
    return {'head': head, 'marker': head - 1, 'header': header,
            'header_distance': header - head, 'pc': '',
            'physical_registers': values[:9], 'logical_registers': logical,
            'spare_values': values[9:], 'one_count': len(ones),
            'all_one_positions': sorted(ones), 'all_other_cells_zero': True,
            'logical_registers_after_index8_zero': True,
            'safe_certificate': certificate}

def literal(table, halt, dispatch, q, offset, physical, gap, spare, classify, limit):
    rows = [None] * (max(max(k[0] for k in table), halt) + 1)
    for state in {key[0] for key in table}:
        rows[state] = [table[state, 0], table[state, 1]]
    head, ones, rejected = 0, {offset}, 0
    for steps in range(limit + 1):
        if q == halt:
            return {'outcome': 'halt', 'steps_after_first_write': steps,
                    'head': head, 'unsafe_structural_frames': rejected}
        if q == dispatch:
            frame = parse_frame(head, ones, physical, gap, spare, classify)
            if frame is not None:
                if frame['safe_certificate'] is not None:
                    return {'outcome': 'safe_complete_frame',
                            'steps_after_first_write': steps, 'frame': frame,
                            'unsafe_structural_frames': rejected}
                rejected += 1
        if steps == limit:
            return {'outcome': 'fuel_limit', 'steps_after_first_write': steps,
                    'state': q, 'head': head, 'one_count': len(ones),
                    'unsafe_structural_frames': rejected,
                    'ones_sha256': hashlib.sha256(json.dumps(sorted(ones)).encode()).hexdigest()}
        w, d, q = rows[q][int(head in ones)]
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        head += d

def confirm_dense(table, start, steps, expected_state, expected_head, expected_ones):
    cells = bytearray(2 * steps + 3)
    origin = steps + 1
    q, head = start, origin
    for _ in range(steps):
        w, d, nxt = table[q, cells[head]]
        cells[head] = w
        head += d
        q = nxt
    actual = [i - origin for i, bit in enumerate(cells) if bit]
    if (q, head - origin, actual) != (expected_state, expected_head, expected_ones):
        raise AssertionError('independent dense replay disagrees')
    return {'status': 'PASS', 'blank_steps': steps, 'start': start,
            'state': q, 'head': head - origin, 'one_count': len(actual),
            'all_one_positions': actual, 'all_other_cells_zero': True}

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--safe-classifier', type=Path,
                    default=Path(__file__).with_name('safe_seed254.py'))
    ap.add_argument('--dispatcher', type=int, default=96)
    ap.add_argument('--halt', type=int, default=254)
    ap.add_argument('--physical', default=','.join(map(str, PHYSICAL)))
    ap.add_argument('--minimum-gap', type=int, default=64)
    ap.add_argument('--minimum-spares', type=int, default=1)
    ap.add_argument('--limit', type=int, default=2_000_000,
                    help='literal steps per normalized first-write class')
    ap.add_argument('--stop-after-first', action='store_true')
    args = ap.parse_args()
    if args.limit < 1 or args.minimum_gap < 1 or args.minimum_spares < 1:
        ap.error('positive fuel, gap, and spare suffix length required')
    physical = tuple(int(x) for x in args.physical.split(','))
    if sorted(physical) != list(range(9)):
        ap.error('physical map must be a permutation of 0,...,8')
    table, states, preferred = read_table(args.table, args.halt)
    if args.dispatcher not in states:
        ap.error('dispatcher must be a working state')
    spec = importlib.util.spec_from_file_location('safe_seed_source', args.safe_classifier)
    classifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(classifier)
    groups = classes(table, states, args.halt, preferred)
    start = time.monotonic()
    report = {'status': 'RUNNING', 'table_sha256': sha(args.table),
              'driver_sha256': sha(__file__), 'safe_classifier_sha256': sha(args.safe_classifier),
              'working_states': len(states), 'rows': len(table),
              'declared_start': preferred, 'dispatcher': args.dispatcher, 'halt': args.halt,
              'physical_of_logical': physical, 'minimum_gap': args.minimum_gap,
              'minimum_spares': args.minimum_spares, 'normalized_step_limit': args.limit,
              'first_write_classes': groups, 'cases': [], 'winners': [],
              'scope': 'Exact first-write quotient, bounded literal search, existing proof-producing Safe grammar, complete nonempty-spare frames, and independent exact dense confirmation. Runtime and consistency proofs are separate.'}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    def save():
        report['seconds'] = time.monotonic() - start
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    save()
    pending = [g for g in groups if g['kind'] == 'first_write']
    for group in pending:
        representative = group['members'][0]
        result = literal(table, args.halt, args.dispatcher, group['state'], group['one_offset'],
                         physical, args.minimum_gap, args.minimum_spares,
                         classifier.state, args.limit)
        entry = {'normalized_state': group['state'], 'one_offset': group['one_offset'],
                 'representative_start': representative['start'],
                 'equivalent_blank_start_count': len(group['members']), 'run': result}
        report['cases'].append(entry)
        if result['outcome'] == 'safe_complete_frame':
            steps = representative['prefix_steps'] + result['steps_after_first_write']
            shift, frame = representative['translation'], result['frame']
            absolute = dict(frame)
            for key in ('head', 'marker', 'header'):
                absolute[key] += shift
            absolute['all_one_positions'] = [x + shift for x in frame['all_one_positions']]
            exact = confirm_dense(table, representative['start'], steps,
                                  args.dispatcher, absolute['head'], absolute['all_one_positions'])
            target = args.output.with_name(args.output.stem + f'-start{representative["start"]}.tm')
            target.write_text(f'#! start {representative["start"]}\n' + ''.join(
                f'{q} {b} {w} {"R" if d == 1 else "L"} {nxt}\n'
                for (q, b), (w, d, nxt) in sorted(table.items())))
            report['winners'].append({'start': representative['start'], 'blank_steps': steps,
                                      'frame': absolute, 'dense_replay': exact,
                                      'table': target.name, 'table_sha256': sha(target)})
        save()
        print(f'Class {len(report["cases"])}/{len(pending)}: start '
              f'{representative["start"]}, {result["outcome"]}, '
              f'{result["steps_after_first_write"]} steps', flush=True)
        if args.stop_after_first and report['winners']:
            break
    report['complete_all_classes'] = len(report['cases']) == len(pending)
    report['status'] = 'FOUND_SAFE_FRAME' if report['winners'] else 'NO_SAFE_FRAME_WITHIN_BOUND'
    report['outcome_counts'] = dict(Counter(c['run']['outcome'] for c in report['cases']))
    report['exact_blank_cycle_start_count'] = sum(len(g['members']) for g in groups if g['kind'] == 'blank_cycle')
    report['exact_blank_halt_start_count'] = sum(len(g['members']) for g in groups if g['kind'] == 'blank_halt')
    save()
    print(json.dumps({key: report[key] for key in ('status', 'complete_all_classes', 'outcome_counts', 'seconds')}))

if __name__ == '__main__':
    main()
