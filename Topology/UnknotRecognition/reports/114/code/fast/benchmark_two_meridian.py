"""Pinned whole-recognition audit of the optional two-meridian stage.

Fresh PD validation, filters, seed search, arithmetic, certificate replay and
fallback are timed together. Compare the previous recognizer twice (A/A), the
current disabled stage and the current enabled stage, under both the ordinary
pipeline and the stronger optional compressed-group incumbent. Keep censored
runs, but never include them in completed-time medians or paired speedups.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
from time import perf_counter
import types

from fastunknot import Diagram, recognize
from fastunknot.two_meridian import two_meridian_decide
from benchmark_compressed_words import cases as hard_cases

ROOT = Path(__file__).resolve().parent
BASELINE = '7c45c41bc2712e954572cf72fbc222dbf711a0ee'
SEED = 26100897
ARMS = ('baseline', 'control', 'disabled', 'enabled')


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def source_hashes():
    paths = list((ROOT/'fastunknot').glob('*.py')) + [ROOT/'benchmark_two_meridian.py',
        ROOT/'benchmark_compressed_words.py', ROOT/'hard_unknots.py',
        ROOT/'normal_research/gordian.json']
    paths += list((ROOT/'examples').glob('*.json'))
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}


def archived_recognize():
    source = subprocess.check_output(['git', 'show', BASELINE+
        ':Topology/UnknotRecognition/fast/fastunknot/recognize.py'], cwd=ROOT)
    module = types.ModuleType('fastunknot._two_meridian_baseline')
    sys.modules[module.__name__] = module
    exec(compile(source, '<'+BASELINE+':recognize>', 'exec'), module.__dict__)
    return module.recognize, sha256(source).hexdigest()


def cases():
    yield from ((name, d, 'UNKNOT') for name, d in hard_cases())
    for name, expected in [('trefoil','KNOTTED'), ('figure_eight','KNOTTED'),
                           ('hard_unknot_8','UNKNOT'), ('conway','KNOTTED'),
                           ('kinoshita_terasaka','KNOTTED')]:
        d = Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text()))
        yield name, d, expected


def probes(evidence):
    out = []
    for key, value in evidence.items():
        if key == 'two_meridian':
            out.append(value)
        elif isinstance(value, dict):
            out.extend(probes(value))
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, dict):
                    out.extend(probes(item))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=5)
    args = parser.parse_args()
    if args.rounds < 1:
        parser.error('rounds must be positive')
    old, baseline_hash = archived_recognize()
    frozen, rng, rows, certificates = source_hashes(), random.Random(SEED), [], {}
    configs = {'ordinary': dict(seconds=3, max_objects=50000),
        'compressed_group': dict(seconds=18, max_objects=50000, use_group=True,
            group_compressed_search=True, group_relators=True, group_seconds=15,
            group_max_work=20_000_000)}
    for name, diagram, expected in cases():
        start = perf_counter()
        raw = two_meridian_decide(Diagram.from_pd(diagram.pd), seconds=None,
                                 max_work=2_000_000, max_attempts=10000)
        raw_time = perf_counter()-start
        if raw['status'] != 'INCONCLUSIVE':
            assert raw['status'] == expected, (name, raw)
        row = dict(name=name, pd=diagram.pd, crossings=diagram.crossings,
                   expected=expected, raw_stage=dict(seconds=raw_time, result=raw), modes={})
        for mode, options in configs.items():
            samples, warmups = [], []
            for repetition in range(args.rounds+1):
                order = list(ARMS)
                rng.shuffle(order)
                measurements = {}
                for arm in order:
                    fn = old if arm in ('baseline','control') else recognize
                    extra = dict(use_two_meridian=arm == 'enabled') if arm in ('disabled','enabled') else {}
                    start = perf_counter()
                    result = fn(Diagram.from_pd(diagram.pd), **options, **extra)
                    elapsed = perf_counter()-start
                    completed = result.status in ('UNKNOT','KNOTTED')
                    if completed:
                        assert result.status == expected, (name, mode, arm, result)
                    stages = []
                    for stage in probes(result.evidence):
                        item = {k: stage[k] for k in ('status','reason','statistics') if k in stage}
                        if 'certificate' in stage:
                            key = digest(stage['certificate'])
                            certificates[key] = stage['certificate']
                            item['certificate_sha256'] = key
                        stages.append(item)
                    measurements[arm] = dict(seconds=elapsed, status=result.status,
                        method=result.method, completed=completed, stages=stages,
                        reason=result.evidence.get('reason'))
                sample = dict(order=order, measurements=measurements)
                (samples if repetition else warmups).append(sample)
            medians = {}
            for arm in ARMS:
                completed = [s['measurements'][arm]['seconds'] for s in samples
                             if s['measurements'][arm]['completed']]
                medians[arm] = median(completed) if completed else None
            ratios = {}
            for a,b in [('baseline','control'),('baseline','disabled'),('disabled','enabled')]:
                both = [s['measurements'][a]['seconds']/s['measurements'][b]['seconds']
                        for s in samples if s['measurements'][a]['completed']
                        and s['measurements'][b]['completed']]
                ratios[a+'/'+b] = dict(count=len(both), median=median(both) if both else None)
            row['modes'][mode] = dict(warmups=warmups, samples=samples,
                completed_median_seconds=medians, paired_ratios=ratios)
            print(name, mode, medians, flush=True)
        rows.append(row)
    assert source_hashes() == frozen, 'source changed during measurement'
    data = dict(baseline=BASELINE, baseline_recognize_sha256=baseline_hash,
        source_sha256=frozen, source_hashes_unchanged=True, seed=SEED,
        python=sys.version, platform=platform.platform(), measured_rounds=args.rounds,
        excluded_warmups_per_case_mode_arm=1, configurations=configs,
        stage_defaults=dict(seconds=.05,max_work=2_000_000,max_attempts=10000),
        raw_stage_scope='fresh PD validation plus standalone producer and replay; no time cap, work and attempt caps retained',
        query_scope='fresh PD validation plus whole recognition, all filters, optional group and fallback retained; imports and hard-corpus preparation excluded',
        provenance='15 previous hard-unknot benchmark cases, plus 5 standard named controls; expected labels precede this stage',
        censoring='UNKNOWN/INCONCLUSIVE recorded, excluded from completed medians and pairs; each pair includes only two completed queries',
        rows=rows,certificates=certificates)
    args.output.write_text(json.dumps(data,indent=2)+'\n')


if __name__ == '__main__':
    main()
