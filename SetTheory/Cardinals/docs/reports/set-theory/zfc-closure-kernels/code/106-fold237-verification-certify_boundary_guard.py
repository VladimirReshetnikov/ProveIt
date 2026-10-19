#!/usr/bin/env python3
"""Prove the 169/read-1 right-neighbor guard on the exact boundary239 source.

The unchanged inherited affine/list engine is supplied explicitly as --engine-dir.
This fresh instrumentation checks that every concrete symbolic visit is exposed,
and that neither unary nor finite-list induction hides a visit to state 169.
It proves the entire instruction contract as well as the extra guard.
No natural-register bound or finite spare-list bound is introduced.
"""
from pathlib import Path
import argparse
from collections import Counter
import hashlib
import importlib
import json
import sys
import time

TABLE_SHA = 'd061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719'
SITES_SHA = '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
ENGINE_SHA = '9ff1b7c487036744206976aa45c16c3b8d6eeb8d4e7cad81f41dae8ebab66c5e'
HELPER_SHA = '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'

def require(condition, message):
    if not condition:
        raise AssertionError(message)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--sites', type=Path, required=True)
    ap.add_argument('--engine-dir', type=Path, required=True)
    ap.add_argument('--output-dir', type=Path, required=True)
    a = ap.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Assertions must be enabled.')
    require(digest(a.table) == TABLE_SHA, 'Wrong boundary239 bytes.')
    require(digest(a.sites) == SITES_SHA, 'Wrong boundary source bytes.')
    require(digest(a.engine_dir/'symbolic_runtime.py') == ENGINE_SHA, 'Changed engine.')
    require(digest(a.engine_dir/'independent_runtime.py') == HELPER_SHA, 'Changed helper.')
    sys.path.insert(0, str(a.engine_dir.resolve()))
    s = importlib.import_module('symbolic_runtime')
    t = s.r.table(a.table)
    sites = json.loads(a.sites.read_text())
    working = {q for q, _ in t}
    require(len(working) == 239 and len(t) == 478, 'Wrong state census.')
    require(set(t) == {(q,b) for q in working for b in (0,1)}, 'Incomplete table.')
    require({v[2] for v in t.values()} - working == {254}, 'Wrong halt.')
    require(len(sites) == 6455, 'Wrong leaf census.')
    lemmas, blocks = s.prove_blocks(t)
    for proof in blocks:
        require(all(event[1][0] != 169 for event in proof['trace']
                    if event[0] in ('literal','unary')), 'Block induction hides 169.')
    require(all(key[0] != 169 for key in lemmas), 'List induction starts at 169.')
    require(all(t[169,b][2] != 169 for b in (0,1)), 'Unary induction at 169.')
    original_step = s.State.step
    visits, records, used = [], [], set()
    current_index, current_positive = None, None

    def inspected_step(state, table, checked_lemmas, clock, motion):
        state.key()
        if state.q == 169:
            require(state.direction == 1, ('Orientation', current_index, current_positive))
            atom = state.right[0]
            require(atom[0] == 'run' and atom[2][0] >= 1, 'Head bit is not explicit.')
            if atom[1] == 1:
                require(atom[2][0] >= 2,
                        ('Right-neighbor guard not proved', current_index,
                         current_positive, state.key()))
                visits.append({'site_index': current_index, 'positive': current_positive,
                               'one_run_length': atom[2], 'clock': clock})
        return original_step(state, table, checked_lemmas, clock, motion)

    start = time.monotonic()
    s.State.step = inspected_step
    try:
        for index, site in enumerate(sites):
            for positive in ((False,True) if site[1] == 'CD' else (False,)):
                current_index, current_positive = index, positive
                before = len(visits)
                result = s.case(t, lemmas, site, positive)
                used.update(result.pop('rows'))
                result.pop('trace')
                records.append({'site_index': index, 'positive': positive,
                                'guard_visits': len(visits)-before, **result})
                if len(records) % 1000 == 0:
                    print('proved', len(records), 'guards;', len(visits),
                          '169/read-1 visits;', round(time.monotonic()-start, 2),
                          'seconds', flush=True)
    finally:
        s.State.step = original_step
    require(len(records) == 8386 and len(used) == 478, 'Incomplete coverage.')
    require(visits, 'Vacuous guard proof.')
    # The same predicate during the finite prefix. This is a calculation,
    # separately identified from the all-register/list proof above.
    q, h, ones, counts = 95, 0, set(), Counter()
    for tick in range(409691):
        b = int(h in ones)
        if q == 169:
            counts[f'169/{b}'] += 1
            if b:
                require(h+1 in ones, ('Startup right-neighbor guard', tick))
        w, d, q = t[q,b]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += d
    require((q,h,len(ones)) == (96,-5,351), 'Wrong startup endpoint.')
    record = {
        'status': 'PASS_UNIVERSAL_RUNTIME_AND_EXACT_BOOT_GUARD',
        'table_sha256': TABLE_SHA, 'sites_sha256': SITES_SHA,
        'instrument_sha256': digest(Path(__file__)),
        'engine_sha256': ENGINE_SHA, 'helper_sha256': HELPER_SHA,
        'cases': len(records), 'symbolic_rules': sum(c['symbolic_steps'] for c in records),
        'minimum_instruction_duration_constant': min(c['duration'][0] for c in records),
        'transition_rows_covered': len(used),
        'explicit_guard_visits': len(visits),
        'minimum_certified_one_run_constant': min(v['one_run_length'][0] for v in visits),
        'no_induction_hides_state169': True, 'blocks': blocks,
        'bootstrap': {'steps':409691, 'state':q, 'head':h, 'ones':sorted(ones),
                      'all_other_cells_zero':True, 'guard_visits':dict(counts)},
        'seconds': time.monotonic()-start,
        'scope': 'All nine arbitrary natural registers, arbitrary natural gap, first spare, and arbitrary finite spare tail; exact whole-tape source contracts. Ordinary mathematical proof with a finite executable certificate, not a kernel theorem.'
    }
    a.output_dir.mkdir(parents=True, exist_ok=True)
    for name, obj in [('boundary_guard.json',record),('boundary_guard_cases.json',records),
                      ('boundary_guard_visits.json',visits)]:
        (a.output_dir/name).write_text(json.dumps(obj, indent=2)+'\n')
    print(json.dumps({k:v for k,v in record.items() if k not in ('blocks','bootstrap')}, indent=2), flush=True)

if __name__ == '__main__':
    main()
