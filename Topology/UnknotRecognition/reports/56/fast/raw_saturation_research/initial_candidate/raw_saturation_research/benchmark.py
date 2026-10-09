"""Paired complete-call measurements for optional raw singleton saturation.

Run from fast/:
  python raw_saturation_research/benchmark.py --mode stage --output results/raw_stage.json
The default baseline path is ../baseline/fast; --baseline accepts a pinned checkout.
Every measured group call includes fresh PD validation, source reconstruction,
search and independent verification. Pipeline calls retain the default filters.
Resource-limited outcomes remain censored and are never speedup denominators.
"""
import argparse
from copy import deepcopy
import hashlib
import importlib
import importlib.util
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot import Diagram, recognize
from fastunknot.group_certificate import group_decide, verify_group_certificate
from fastunknot.compressed_words import CompressedLimit, WordArena
from fastunknot.compressed_search import _search
from fastunknot.raw_saturation import find_rank_one_plan
from fastunknot.elimination_batch import apply_batch, plan_batch
from fastunknot.elimination_batch_verify import replay_compressed_batch
from fastunknot.primitive_projection import rank_one_zero

EVENT_SINK = lambda event: None


def load_baseline(path):
    package = path / 'fastunknot'
    spec = importlib.util.spec_from_file_location(
        'saturation_baseline', package / '__init__.py',
        submodule_search_locations=[str(package)])
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    group = importlib.import_module(spec.name + '.group_certificate')
    return module, group


def hashes(path):
    return {str(p.relative_to(path)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted((path / 'fastunknot').rglob('*.py'))
            if p.name != 'orbit_index.py'}


def corpus():
    from hard_unknots import SURVIVORS
    from fastunknot.simplify import simplify
    rows = []
    for i, (_, strands, word) in enumerate(SURVIVORS):
        diagram, _ = simplify(Diagram.from_braid(strands, word), r3=True)
        rows.append((f'survivor-{i:02d}', diagram.pd, 'surviving unknot diagram'))
    for name in ('trefoil', 'conway', 'kinoshita_terasaka', 'hard_unknot_8',
                 'grid_determinant_one_knot', 'unknot_braid40', 'stress_braid5_36'):
        diagram = Diagram.from_json(json.loads((ROOT / 'examples' / (name + '.json')).read_text()))
        rows.append((name, diagram.pd, 'repository named fixture'))
    for name in ('monster', 'gst', 'gordian'):
        diagram = Diagram.from_json(json.loads((ROOT / 'normal_research' / (name + '.json')).read_text()))
        rows.append((name, diagram.pd, 'repository normal-research fixture'))
    return rows


def small_audit_cases():
    rng = random.Random(2026100902)
    cases = []
    while len(cases) < 80:
        strands = rng.randrange(2, 6)
        word = [rng.choice((-1, 1)) * rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 15))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        cases.append((f'heldout-{len(cases):02d}', diagram.pd, 'seeded braid closure'))
    return cases


def call(arm, pd, mode, base, old_group):
    enabled = arm == 'saturation'
    old = arm == 'baseline'
    module = base if old else sys.modules['fastunknot']
    start = perf_counter()
    diagram = module.Diagram.from_pd(pd)
    if mode == 'stage':
        options = dict(seconds=None, max_work=10_000_000, compressed_search=True,
                       relator_moves=True)
        if not old:
            options['raw_saturation'] = enabled
        result = (old_group.group_decide if old else group_decide)(diagram, **options)
    else:
        options = dict(seconds=1.0, max_objects=50000, use_group=True,
                       group_seconds=0.15, group_compressed_search=True,
                       group_relators=True)
        if not old:
            options['group_raw_saturation'] = enabled
        result_object = module.recognize(diagram, **options)
        result = result_object.to_json()
    elapsed = perf_counter() - start
    return dict(seconds=elapsed, result=result)


def paired(mode, cases, rounds, base, old_group):
    rng = random.Random(2026100903)
    rows = []
    for name, pd, family in cases:
        samples = []
        warmup = None
        for repetition in range(rounds + 1):
            order = ['baseline', 'control', 'saturation']
            rng.shuffle(order)
            records = {}
            for arm in order:
                records[arm] = call(arm, pd, mode, base, old_group)
                EVENT_SINK(dict(mode=mode, name=name, repetition=repetition,
                                warmup=repetition == 0, arm=arm, record=records[arm]))
            conclusive = {r['result']['status'] for r in records.values()
                          if r['result']['status'] not in ('INCONCLUSIVE', 'UNKNOWN')}
            assert len(conclusive) <= 1, (name, conclusive)
            if repetition:
                samples.append(dict(order=order, arms=records))
            else:
                warmup = dict(order=order, arms=records)
        observed = {arm: median(s['arms'][arm]['seconds'] for s in samples)
                    for arm in order}
        complete = {arm: [s['arms'][arm]['seconds'] for s in samples
                          if s['arms'][arm]['result']['status'] not in
                          ('INCONCLUSIVE', 'UNKNOWN')] for arm in order}
        medians = {arm: median(values) if values else None
                   for arm, values in complete.items()}
        ratios = {}
        for arm in ('control', 'saturation'):
            values = [s['arms']['baseline']['seconds'] / s['arms'][arm]['seconds']
                      for s in samples
                      if s['arms']['baseline']['result']['status'] == s['arms'][arm]['result']['status']
                      and s['arms'][arm]['result']['status'] not in ('INCONCLUSIVE', 'UNKNOWN')]
            ratios[arm] = median(values) if len(values) == rounds else None
        row = dict(name=name, family=family, crossings=len(pd), pd=pd,
                   median_seconds=medians, median_observed_seconds=observed,
                   completion_counts={arm: len(values) for arm, values in complete.items()},
                   paired_ratios=ratios, warmup=warmup,
                   outcomes={arm: [s['arms'][arm]['result']['status'] for s in samples]
                             for arm in order}, samples=samples)
        rows.append(row)
        print(name, {a: None if t is None else round(t, 6) for a, t in medians.items()},
              ratios, row['completion_counts'], flush=True)
    return rows


def audit(base, old_group):
    rows = []
    for name, pd, family in small_audit_cases() + corpus():
        old = old_group.group_decide(base.Diagram.from_pd(pd), seconds=None,
                                    max_work=2_000_000, compressed_search=True,
                                    relator_moves=True)
        control = group_decide(Diagram.from_pd(pd), seconds=None, max_work=2_000_000,
                               compressed_search=True, relator_moves=True)
        explicit_false = group_decide(Diagram.from_pd(pd), seconds=None,
                                     max_work=2_000_000, compressed_search=True,
                                     relator_moves=True, raw_saturation=False)
        new = group_decide(Diagram.from_pd(pd), seconds=None, max_work=2_000_000,
                           raw_saturation=True, relator_moves=True)
        assert old['status'] == control['status'], name
        assert old.get('certificate') == control.get('certificate'), name
        assert explicit_false['status'] == control['status'], name
        assert explicit_false.get('certificate') == control.get('certificate'), name
        assert explicit_false['search_stats'] == control['search_stats'], name
        replayed = []
        for arm, result in [('baseline', old), ('saturation', new)]:
            if result['status'] != 'UNKNOT':
                continue
            proof = result['certificate']
            assert verify_group_certificate(Diagram.from_pd(pd), proof, compressed=True,
                                            max_work=10_000_000), name
            assert old_group.verify_group_certificate(base.Diagram.from_pd(pd), proof,
                                                      compressed=True,
                                                      max_work=10_000_000), name
            # Literal replay may legitimately exceed the expansion allowance.
            if len(pd) <= 16:
                assert verify_group_certificate(Diagram.from_pd(pd), proof,
                                                max_work=10_000_000,
                                                max_letters=2_000_000), name
                assert old_group.verify_group_certificate(base.Diagram.from_pd(pd), proof,
                                                          max_work=10_000_000,
                                                          max_letters=2_000_000), name
            altered = deepcopy(proof)
            altered['input_pd'].append([0, 0, 0, 0])
            assert not verify_group_certificate(Diagram.from_pd(pd), altered,
                                                compressed=True), name
            assert not old_group.verify_group_certificate(base.Diagram.from_pd(pd),
                                                          altered, compressed=True), name
            replayed.append(arm)
        rows.append(dict(name=name, family=family, pd=pd, baseline=old, control=control,
                         explicit_false=explicit_false, saturation=new,
                         replayed=replayed, source_binding_rejections=2*len(replayed)))
        EVENT_SINK(dict(mode='audit', row=rows[-1]))
        print('audit', name, old['status'], new['status'], replayed, flush=True)
    return rows


def adversarial(bits):
    arena = WordArena(max_nodes=2_000_000, max_work=100_000_000)
    power = 1 << bits
    roots = [arena.from_word([1, 2, 3]),
             arena.from_word([1, 3] + [4] * 10),
             arena.from_word([1] + [4] * 10),
             arena.power(arena.letter(3), power),
             arena.power(arena.from_word([2] + [-4] * 10), power)]
    return arena, roots, {1, 2, 3, 4}


def kernels(rounds, search_allowance):
    rng = random.Random(2026100904)
    rows = []
    for bits in (8, 64, 512, 2048, 4096):
        samples = []
        warmup = None
        for repetition in range(rounds + 1):
            order = ['ordinary', 'control', 'saturation']
            rng.shuffle(order)
            records = {}
            for arm in order:
                arena, roots, alive = adversarial(bits)
                initial_nodes = len(arena.rules) - 1
                initial_work = arena.stats['work']
                arena.left = search_allowance
                moves, terminal = [], {}
                start = perf_counter()
                reason = None
                try:
                    result = _search(arena, roots, alive, moves, primitive_terminal=terminal,
                                     rank_two_terminal=False, raw_saturation=arm == 'saturation')
                except CompressedLimit as exc:
                    result = False
                    reason = str(exc)
                elapsed = perf_counter() - start
                search_stats = deepcopy(arena.stats)
                if result:
                    assert len(alive) == 1, (bits, arm, alive)
                    assert rank_one_zero(arena, roots, alive)
                records[arm] = dict(seconds=elapsed, source_nodes=initial_nodes,
                                    status='COMPLETE' if result else 'INCONCLUSIVE',
                                    reason=reason or (None if result else 'search stalled'),
                                    surviving_generators=sorted(alive),
                                    source_work=initial_work,
                                    search_work=search_stats['work'] - initial_work,
                                    nodes=len(arena.rules) - 1, stats=search_stats,
                                    moves=moves, terminal=terminal)
                EVENT_SINK(dict(mode='kernels', bits=bits, repetition=repetition,
                                warmup=repetition == 0, arm=arm, record=records[arm]))
            if repetition:
                samples.append(dict(order=order, arms=records))
            else:
                warmup = dict(order=order, arms=records)
        complete = {arm: [s['arms'][arm]['seconds'] for s in samples
                          if s['arms'][arm]['status'] == 'COMPLETE'] for arm in order}
        ratios = {}
        for arm in ('control', 'saturation'):
            pairs = [s['arms']['ordinary']['seconds']/s['arms'][arm]['seconds']
                     for s in samples if s['arms']['ordinary']['status'] ==
                     s['arms'][arm]['status'] == 'COMPLETE']
            ratios[arm] = median(pairs) if len(pairs) == rounds else None
        rows.append(dict(bits=bits, family='abstract redundant cyclic presentation',
                         median_seconds={a: median(v) if v else None
                                         for a, v in complete.items()},
                         median_observed_seconds={a: median(s['arms'][a]['seconds']
                                                           for s in samples) for a in order},
                         completion_counts={a: len(v) for a, v in complete.items()},
                         paired_ratio=ratios['saturation'], control_ratio=ratios['control'],
                         warmup=warmup, samples=samples))
        print('kernel', bits, rows[-1]['median_seconds'], rows[-1]['paired_ratio'],
              rows[-1]['completion_counts'], flush=True)
    return rows


def main():
    global EVENT_SINK
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, default=ROOT.parent / 'baseline' / 'fast')
    parser.add_argument('--mode', choices=('audit', 'stage', 'pipeline', 'kernels'), required=True)
    parser.add_argument('--rounds', type=int, default=5)
    parser.add_argument('--kernel-work', type=int, default=2_000_000)
    parser.add_argument('--candidate-label', default='candidate')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('--rounds must be positive')
    if args.kernel_work < 1:
        parser.error('--kernel-work must be positive')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    journal = args.output.with_suffix('.journal.jsonl')
    journal.write_text('')
    def record_event(event):
        with journal.open('a') as stream:
            stream.write(json.dumps(event, separators=(',', ':')) + '\n')
    EVENT_SINK = record_event
    base, old_group = load_baseline(args.baseline.resolve())
    before = dict(baseline=hashes(args.baseline), current=hashes(ROOT))
    driver_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    start = perf_counter()
    if args.mode == 'audit':
        rows = audit(base, old_group)
    elif args.mode == 'kernels':
        rows = kernels(args.rounds, args.kernel_work)
    else:
        cases = corpus()
        if args.mode == 'stage':
            cases = [(f'circle-{n-1}', Diagram.from_braid(n, list(range(1, n))).pd,
                      'elementary unknot closure; mechanism control')
                     for n in (16, 32, 64, 128, 256, 512)] + cases
        rows = paired(args.mode, cases, args.rounds, base, old_group)
    after = dict(baseline=hashes(args.baseline), current=hashes(ROOT))
    assert before == after, 'measured source changed during run'
    assert hashlib.sha256(Path(__file__).read_bytes()).hexdigest() == driver_hash
    output = dict(mode=args.mode, baseline_commit='fdeb5b1a20b84b93cb150e0232031837bb7d30cb',
                  candidate_label=args.candidate_label,
                  python=sys.version, platform=platform.platform(), rounds=args.rounds,
                  warmup_rounds=1 if args.mode != 'audit' else 0,
                  elapsed_seconds=perf_counter() - start, source_hashes=before,
                  driver_sha256=driver_hash,
                  excluded_hash_paths={'fastunknot/orbit_index.py':
                                       'unrelated rank/select implementation concurrently developed'},
                  kernel_search_allowance=args.kernel_work if args.mode == 'kernels' else None,
                  journal_file=journal.name,
                  timing='fresh complete calls; see script for exact contracts',
                  censoring='INCONCLUSIVE and UNKNOWN are never completion-time ratios', rows=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, indent=2) + '\n')
    print('saved', args.output, flush=True)


if __name__ == '__main__':
    main()
