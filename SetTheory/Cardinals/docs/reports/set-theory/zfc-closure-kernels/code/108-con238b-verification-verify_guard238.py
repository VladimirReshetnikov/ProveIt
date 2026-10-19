#!/usr/bin/env python3
"""Certify Boundary239's next-one guard needed for the 239 -> 238 fold.

The supplied affine/list engine is imported unchanged and pinned by hash.
This wrapper adds assertions before its literal step; it adds no execution
rule.  It uses the Boundary239 source and table rather than assuming the
previous Rotation240 guard survives a changed selector program.

The finite input validation here is deliberately separate from the old
engine's Rotation240-specific source validator.  The instruction semantics,
whole-tape endpoints, symbolic parameters, and positive clocks are unchanged.
Source equivalence with the calibrated ZFC program is a separate premise.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import importlib.util
import json
import sys
import time

BASE_SHA = 'd061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719'
SITES_SHA = '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
ENGINE_SHA = 'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145'
HELPER_SHA = '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'
BOOT_STEPS = 409691


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(table, sites):
    states = {q for q, _ in table}
    assert len(states) == 239 and len(table) == 478
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert 95 in states and 96 in states and 254 not in states
    assert {z for _, _, z in table.values()} - states == {254}
    assert all(w in (0, 1) and d in (-1, 1) for w, d, z in table.values())
    assert isinstance(sites, list) and len(sites) == 6455
    leaves, prefixes = set(), set()
    for row in sites:
        assert isinstance(row, list) and len(row) == 3
        pc, op, arg = row
        assert isinstance(pc, str) and 0 < len(pc) <= 64 and set(pc) <= {'0', '1'}
        assert pc not in leaves
        assert op in ('CI', 'CD', 'CB', 'CC', 'CH')
        if op == 'CH':
            assert arg is None
        elif op in ('CI', 'CD'):
            assert type(arg) is int and 0 <= arg < 9
        else:
            assert type(arg) is int and arg >= 1
        leaves.add(pc)
        prefixes.update(pc[:i] for i in range(len(pc)))
    assert not leaves & prefixes
    assert len(prefixes) == len(leaves) - 1
    assert all(p + b in leaves | prefixes for p in prefixes for b in '01')
    assert sum(2 if op == 'CD' else 1 for _, op, _ in sites) == 8386
    return {'working_states': len(states), 'transition_rows': len(table),
            'leaf_count': len(leaves), 'complete_binary_tree': True,
            'maximum_depth': max(map(len, leaves)),
            'source_calibration': 'Established separately by Boundary239 source equivalence.'}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--sites', type=Path, required=True)
    ap.add_argument('--engine', type=Path, required=True)
    ap.add_argument('--output-dir', type=Path, required=True)
    a = ap.parse_args()
    assert __debug__ and not sys.flags.optimize
    assert digest(a.table) == BASE_SHA
    assert digest(a.sites) == SITES_SHA
    assert digest(a.engine) == ENGINE_SHA
    helper = a.engine.resolve().parent / 'independent_runtime.py'
    assert digest(helper) == HELPER_SHA
    sys.path.insert(0, str(a.engine.resolve().parent))
    spec = importlib.util.spec_from_file_location('boundary238_guard_engine', a.engine)
    s = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(s)
    assert digest(Path(s.__file__)) == ENGINE_SHA
    assert digest(Path(s.r.__file__)) == HELPER_SHA
    table = s.r.table(a.table)
    sites = json.loads(a.sites.read_text())
    facts = validate(table, sites)
    lemmas, blocks = s.prove_blocks(table)

    # Every list induction is founded on an explicit one-block proof. No
    # state169 visit may be hidden inside such an induction. The only other
    # accelerated primitive is a same-state unary loop, absent at state169.
    assert all(q != 169 for q, _, _, _ in lemmas)
    for block in blocks:
        for event in block['trace']:
            assert event[0] in ('literal', 'unary')
            assert event[1][0] != 169 and event[1][4] != 169
    assert all(table[169, b][2] != 169 for b in (0, 1))

    boot_events = []
    q, h, ones = 95, 0, set()
    for tick in range(BOOT_STEPS):
        b = int(h in ones)
        if q == 169 and b == 1:
            assert h + 1 in ones, ('Blank guard failure', tick, h)
            boot_events.append([tick, h])
        w, d, q = table[q, b]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += d
    assert (q, h, len(ones)) == (96, -5, 351)

    visits, records, used = [], [], set()
    index = positive = None
    ordinary_step = s.State.step

    def guarded_step(state, current_table, current_lemmas, clock, motion):
        state.key()
        if state.q == 169:
            assert state.direction == 1, ('Wrong orientation', index, positive)
            assert state.right, ('Missing scan side', index, positive)
            atom = state.right[0]
            assert atom[0] == 'run' and atom[2][0] >= 1
            assert s.nonnegative(atom[2])
            if atom[1] == 1:
                assert atom[2][0] >= 2, ('Next-one guard unproved', index, positive, state.key())
                visits.append({'site_index': index, 'site': sites[index],
                               'positive': positive, 'right_one_run_length': atom[2],
                               'clock': clock, 'head_motion': motion})
        return ordinary_step(state, current_table, current_lemmas, clock, motion)

    started = time.monotonic()
    s.State.step = guarded_step
    try:
        for index, site in enumerate(sites):
            for positive in ((False, True) if site[1] == 'CD' else (False,)):
                before = len(visits)
                answer = s.case(table, lemmas, site, positive)
                used.update(answer['rows'])
                records.append({'site_index': index, 'positive': positive,
                                'symbolic_steps': answer['symbolic_steps'],
                                'duration': answer['duration'], 'motion': answer['motion'],
                                'guard_visits': len(visits) - before})
                if len(records) % 1000 == 0:
                    print('guarded', len(records), 'cases;', len(visits),
                          'next-one visits;', round(time.monotonic() - started, 2), 'seconds',
                          flush=True)
    finally:
        s.State.step = ordinary_step
    assert len(records) == 8386 and len(used) == 478
    assert visits
    result = {
        'status': 'BOUNDARY239_UNBOUNDED_NEXT_ONE_GUARD_PASS',
        'guard': 'q=169 and tape[h]=1 implies tape[h+1]=1',
        'baseline_sha256': BASE_SHA, 'sites_sha256': SITES_SHA,
        'engine_sha256': ENGINE_SHA, 'helper_sha256': HELPER_SHA,
        'instrument_sha256': digest(Path(__file__)),
        'input_validation': facts,
        'complete_cases': len(records),
        'symbolic_rules': sum(r['symbolic_steps'] for r in records),
        'minimum_actual_instruction_duration': min(r['duration'][0] for r in records),
        'all_used_rows': len(used),
        'runtime_guard_events': len(visits),
        'minimum_right_one_run_constant': min(v['right_one_run_length'][0] for v in visits),
        'maximum_right_one_run_constant': max(v['right_one_run_length'][0] for v in visits),
        'one_run_affine_families': sorted(set(tuple(v['right_one_run_length']) for v in visits)),
        'no_summarized_169_visits': True,
        'four_block_schemas': blocks,
        'boot': {'steps': BOOT_STEPS, 'guard_events': boot_events,
                 'state': q, 'head': h, 'one_count': len(ones)},
        'seconds': time.monotonic() - started,
        'scope': 'All nine independent natural primary register values, arbitrary additional gap and first spare value, and an arbitrary finite remaining spare list. Exact whole-tape endpoints and positive instruction duration are rechecked. Source equivalence and zero-padded joins are separate source obligations.',
        'proof_status': 'Executable ordinary mathematical proof, not a Lean/Rocq kernel endpoint.',
        'rule_cap_scope': 'The 4000-rule cap bounds proof construction, not TM duration, register values, gap, or spare-list length.',
    }
    a.output_dir.mkdir(parents=True, exist_ok=True)
    for filename, data in [('guard238_receipt.json', result),
                           ('guard238_cases.json', records),
                           ('guard238_visits.json', visits)]:
        (a.output_dir / filename).write_text(json.dumps(data, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'four_block_schemas'}, indent=2))


if __name__ == '__main__':
    main()
