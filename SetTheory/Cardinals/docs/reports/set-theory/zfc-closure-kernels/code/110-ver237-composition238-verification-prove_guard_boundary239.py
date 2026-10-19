#!/usr/bin/env python3
"""Reprove the delayed169 selector guard for the boundary239 predecessor.

This is a new application of the inherited unbounded runtime rules to the
boundary source and exact boundary239 table. A guard fact from rotation240
is not transferred merely because the locally inspected rows coincide.

The instrumented step adds no execution shortcut. It checks every169/read1
visit, and also checks that no unary or list macro can hide such a visit.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = ROOT / 'sources/incoming/ZFC_239_State_Construction_2026-10-19/zfc239-research-20261019'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checker', type=Path, default=BASE / 'validation/symbolic_runtime.py')
    parser.add_argument('--table', type=Path, default=BASE / 'candidate239/zfc_boundary239_old.tm')
    parser.add_argument('--sites', type=Path, default=HERE / 'sites_logical.json')
    parser.add_argument('--blank-prefix', type=Path, default=BASE / 'candidate239/blank_prefix.json')
    parser.add_argument('--output', type=Path, default=HERE / 'boundary239_selector_guard_portable.json')
    args = parser.parse_args()
    assert __debug__ and not sys.flags.optimize
    assert sha(args.table) == 'd061770f487937f9da652919c9bc9bb79bc9bf137ca41dd7a08eb5ecda8e7719'
    assert sha(args.sites) == '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
    sys.path.insert(0, str(args.checker.resolve().parent))
    spec = importlib.util.spec_from_file_location('boundary_guard_engine', args.checker)
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    table = engine.r.table(args.table)
    sites = json.loads(args.sites.read_text())
    states = {q for q, _ in table}
    assert len(states) == 239 and len(table) == 478
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {q for _, _, q in table.values()} - states == {254}
    assert len(sites) == 6455
    leaves = set()
    prefixes = set()
    for pc, op, arg in sites:
        assert isinstance(pc, str) and 0 < len(pc) <= 64 and set(pc) <= {'0', '1'}
        assert pc not in leaves
        assert op in ('CI', 'CD', 'CB', 'CC', 'CH')
        assert (arg is None) if op == 'CH' else (isinstance(arg, int) and (0 <= arg < 9 if op in ('CI', 'CD') else arg >= 1))
        leaves.add(pc)
        prefixes.update(pc[:i] for i in range(len(pc)))
    assert not leaves.intersection(prefixes)
    assert all(p + b in leaves or p + b in prefixes for p in prefixes for b in ('0', '1'))
    assert len(prefixes) == len(leaves) - 1

    q, head, ones = 95, 0, set()
    boot_events = []
    for tick in range(409691):
        bit = int(head in ones)
        if q == 169 and bit == 1:
            assert head + 1 in ones, ('Boot selector-guard failure', tick, head)
            boot_events.append({'time': tick, 'head': head})
        write, direction, q = table[q, bit]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += direction
    assert (q, head, len(ones)) == (96, -5, 351)
    assert ones == set(json.loads(args.blank_prefix.read_text())['all_one_positions'])

    context = None
    guard_events = []
    actual_step = engine.State.step

    def guarded_step(self, current_table, lemmas, clock, motion):
        self.key()
        src = self.right if self.direction == 1 else self.left
        if self.q == 169:
            assert src and src[0][0] == 'run', ('Unexpected opaque169 entry', context, self.key())
            assert self.direction == 1, ('Unexpected169 direction', context, self.key())
            assert current_table[169, src[0][1]][2] != 169
            if src[0][1] == 1:
                length = src[0][2]
                assert engine.nonnegative(length) and length[0] >= 2, ('Missing right-one guard', context, self.key())
                guard_events.append({'context': context, 'right_one_run_length': length, 'uniform_minimum': length[0]})
        return actual_step(self, current_table, lemmas, clock, motion)

    engine.State.step = guarded_step
    started = time.monotonic()
    lemmas, blocks = engine.prove_blocks(table)
    assert all(key[0] != 169 for key in lemmas)
    for certificate in blocks:
        for event in certificate['trace']:
            assert event[0] in ('literal', 'unary')
            assert event[1][0] != 169
    cases = symbolic_steps = 0
    for index, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            context = {'site_index': index, 'site': site, 'positive': positive}
            result = engine.case(table, lemmas, site, positive)
            cases += 1
            symbolic_steps += result['symbolic_steps']
            if cases % 1000 == 0:
                print('Proved', cases, 'guarded source cases;', len(guard_events), '169/read1 events.', flush=True)
    assert cases == 8386 and guard_events
    receipt = {
        'status': 'BOUNDARY239_UNBOUNDED_SELECTOR_GUARD_PASS',
        'guard': 'At every reachable predecessor configuration, state169 reading1 has a1 immediately right of the head.',
        'predecessor_working_states': 239,
        'baseline_sha256': sha(args.table),
        'sites_sha256': sha(args.sites),
        'blank_prefix_sha256': sha(args.blank_prefix),
        'engine_sha256': sha(args.checker),
        'helper_sha256': sha(Path(engine.r.__file__)),
        'wrapper_sha256': sha(Path(__file__)),
        'boot_steps': 409691,
        'boot_endpoint': {'state': q, 'head': head, 'one_cells': len(ones)},
        'boot_guard_events': boot_events,
        'complete_cases': cases,
        'symbolic_steps': symbolic_steps,
        'runtime_guard_events': guard_events,
        'minimum_right_one_run': min(event['uniform_minimum'] for event in guard_events),
        'one_block_schemas_rederived': blocks,
        'no169_hidden_in_list_schemas': True,
        'no169_self_loop': True,
        'maximum_source_depth': max(map(len, leaves)),
        'seconds': time.monotonic() - started,
        'proof_scope': 'Exact blank startup and every arbitrary-value/gap/spare-list source case of the boundary239 predecessor. Unary induction only skips repeated self-loop state visits;169 is not a self-loop. Every finite-list schema was derived without169. Therefore no macro hides a169/read1 visit. Source calibration and dispatch joins are proved separately; this is executable ordinary mathematics, not a kernel certificate.'
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({key: value for key, value in receipt.items() if key not in ('runtime_guard_events', 'boot_guard_events', 'one_block_schemas_rederived')}, indent=2))


if __name__ == '__main__':
    main()
