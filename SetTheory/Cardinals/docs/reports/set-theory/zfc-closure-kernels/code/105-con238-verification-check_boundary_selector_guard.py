#!/usr/bin/env python3
"""Fresh selector guard for boundary239's changed source, with no new rewrite rule.

The imported engine is the attributed prior literal/unary/list mathematical
checker. This wrapper strengthens the prior guard wrapper by requiring every
state169 symbolic entry to expose a literal run or the known zero exterior.
It checks that no list lemma or unary skip can hide another visit.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys
import time


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--checker', type=Path, required=True)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--sites', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--boot-steps', type=int, default=409691)
    args = ap.parse_args()
    assert __debug__ and not sys.flags.optimize
    sys.path.insert(0, str(args.checker.resolve().parent))
    spec = importlib.util.spec_from_file_location('audited_guard_engine', args.checker)
    engine = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(engine)
    tab = engine.r.table(args.table)
    sites = json.loads(args.sites.read_text())
    # The engine's convenience validator pins the predecessor source. Here the
    # new boundary source is pinned explicitly and its tree shape is checked.
    source_digest = hashlib.sha256(args.sites.read_bytes()).hexdigest()
    assert source_digest == '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'
    working = {q for q, _ in tab}
    assert set(tab) == {(q, b) for q in working for b in (0, 1)}
    assert {r for _, _, r in tab.values()} - working == {254}
    assert 95 in working and 96 in working and 254 not in working
    assert len(sites) == 6455
    leaves, prefixes = set(), set()
    for pc, op, arg in sites:
        assert 0 < len(pc) <= 64 and set(pc) <= {'0', '1'}
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
    assert all(p + b in leaves or p + b in prefixes for p in prefixes for b in ('0', '1'))
    assert len(prefixes) == len(leaves) - 1
    facts = {'working_states': len(working), 'complete_binary_tree': True,
             'leaves': len(leaves), 'maximum_depth': max(map(len, leaves)),
             'exact_boundary_source_pin': source_digest,
             'source_semantic_calibration': 'Checked separately by the source audit.'}
    assert len(tab) == 478 and 169 in {q for q, _ in tab}
    assert 218 not in {q for q, _ in tab}
    assert all(tab[169, b][2] != 169 for b in (0, 1))

    # Check the entire literal blank prefix and record all selector entries.
    q, h, ones = 95, 0, set()
    boot_events = []
    for tick in range(args.boot_steps):
        b = int(h in ones)
        if q == 169:
            assert h - 1 not in ones
            if b:
                assert h + 1 in ones, ('boot guard violation', tick, h)
            boot_events.append({'tick': tick, 'head': h, 'read': b,
                                'right_bit': int(h + 1 in ones)})
        w, d, q = tab[q, b]
        if w:
            ones.add(h)
        else:
            ones.discard(h)
        h += d
    assert (q, h, len(ones)) == (96, -5, 351)

    active_case = None
    entries = []
    original_step = engine.State.step

    def guarded_step(self, table, lemmas, clock, motion):
        self.key()
        src = self.right if self.direction == 1 else self.left
        if self.q == 169:
            assert self.direction == 1, ('state169 entered in unexpected orientation', self.key())
            assert src and (src[0][0] == 'run' or src[0] == engine.BLANK), (
                'state169 hidden behind list/opaque word', self.key())
            if src[0] == engine.BLANK:
                entries.append({'case': active_case, 'read': 0, 'right_word': 'zero exterior'})
            else:
                b, length = src[0][1:]
                assert engine.nonnegative(length) and length[0] >= 1
                if b:
                    assert length[0] >= 2, ('following1 guard failed', active_case, length)
                entries.append({'case': active_case, 'read': b, 'right_run_length': length})
        return original_step(self, table, lemmas, clock, motion)

    engine.State.step = guarded_step
    started = time.monotonic()
    lemmas, blocks = engine.prove_blocks(tab)
    for block in blocks:
        for event in block['trace']:
            if event[0] in ('literal', 'unary'):
                assert event[1][0] != 169, 'list lemma hides state169 visit'
    assert not entries, 'generic list block unexpectedly visits169'
    completed = 0
    symbolic_steps = 0
    min_duration = None
    for i, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            active_case = {'index': i, 'site': site, 'positive': positive}
            result = engine.case(tab, lemmas, site, positive)
            completed += 1
            symbolic_steps += result['symbolic_steps']
            if completed % 1000 == 0:
                print('Guard cases:', completed, 'Selector entries:', len(entries), flush=True)
    expected_cases = sum(2 if s[1] == 'CD' else 1 for s in sites)
    assert completed == expected_cases == 8386
    positive_entries = [x for x in entries if x['read'] == 1]
    assert positive_entries
    minimum = min(e['right_run_length'][0] for e in positive_entries)
    receipt = {
        'status': 'FRESH_BOUNDARY239_UNBOUNDED_SELECTOR_GUARD_PASS',
        'guard': 'q=169 and tape[h]=1 implies tape[h+1]=1',
        'working_states': 239, 'transition_rows': 478,
        'table_sha256': hashlib.sha256(args.table.read_bytes()).hexdigest(),
        'sites_sha256': hashlib.sha256(args.sites.read_bytes()).hexdigest(),
        'engine_sha256': hashlib.sha256(args.checker.read_bytes()).hexdigest(),
        'wrapper_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'input_validation': facts,
        'boot_steps': args.boot_steps,
        'boot_endpoint': {'state': q, 'head': h, 'one_cells': len(ones)},
        'boot_selector_entries': boot_events,
        'complete_cases': completed, 'symbolic_steps': symbolic_steps,
        'runtime_selector_entries': entries,
        'positive_runtime_entries': len(positive_entries),
        'minimum_right_one_run': minimum,
        'four_list_schemas_rederived_without_selector_visits': True,
        'no_self_loop_at169': True,
        'seconds': time.monotonic() - started,
        'scope': 'Exact boundary239 blank prefix plus every unbounded source instruction case.',
        'formalization_status': 'Ordinary inductive mathematical proof, not a Lean kernel certificate.',
    }
    args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k not in
                     ('input_validation', 'runtime_selector_entries', 'boot_selector_entries')}, indent=2))


if __name__ == '__main__':
    main()
