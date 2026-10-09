"""Frozen A/A, mechanism ablations and whole-pipeline seed-search measurements.

An exhaustive failed seed search completes a diagram-class query, while still
returning INCONCLUSIVE for knot recognition. These two notions of completion
are recorded separately. Pipeline timeouts remain censored.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter
import types

from fastunknot import Diagram, recognize
import fastunknot.two_meridian as maintained


ROOT = Path(__file__).resolve().parent
BASELINE_COMMIT = '2b93767bd3cf7ea7c1995acd66f50c72858a30c5'
BASELINE_SHA256 = '5eb36230e9b9114df0f42c089ab716bfd6473ba4baf1621182170ef1a30e7b0d'
SEED = 2610081249
EXHAUSTIVE_REASON = 'no complete derivation from one or two seed meridians'
STANDALONE_ARMS = ('baseline', 'control', 'stamped', 'candidate_only', 'optimized')
PIPELINE_ARMS = ('baseline', 'control', 'optimized', 'disabled')


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def load_module(name, source):
    module = types.ModuleType('fastunknot._seed_benchmark_' + name)
    sys.modules[module.__name__] = module
    exec(compile(source, '<seed-search-' + name + '>', 'exec'), module.__dict__)
    return module


def variants():
    baseline_path = ROOT/'two_meridian_research/baseline_two_meridian.py'
    original = baseline_path.read_text()
    assert sha256(baseline_path.read_bytes()).hexdigest() == BASELINE_SHA256
    current = (ROOT/'fastunknot/two_meridian.py').read_text()
    assignment = 'candidates = _ProductivePairs.build(n, rules, budget)'
    pruning = 'candidates.exclude_closed(closures, index, budget)'
    assert current.count(assignment) == current.count(pruning) == 1
    sources = dict(baseline=original,
        stamped=current.replace(assignment, 'candidates = None'),
        candidate_only=current.replace(pruning, 'pass'), optimized=current)
    functions = {name: load_module(name, source).two_meridian_decide
                 for name, source in sources.items()}
    functions['control'] = functions['baseline']
    return functions, {name: sha256(source.encode()).hexdigest()
                       for name, source in sources.items()}


def summarize(samples, arms):
    medians, counts, ratios = {}, {}, {}
    for arm in arms:
        complete = [s['measurements'][arm]['seconds'] for s in samples
                    if s['measurements'][arm]['completed']]
        counts[arm] = len(complete)
        medians[arm] = median(complete) if complete else None
    for a, b in [('baseline', 'control'), ('baseline', 'optimized')]:
        pairs = [s['measurements'][a]['seconds']/s['measurements'][b]['seconds']
                 for s in samples if s['measurements'][a]['completed']
                 and s['measurements'][b]['completed']]
        ratios[a + '/' + b] = dict(count=len(pairs), median=median(pairs) if pairs else None)
    return dict(completed_counts=counts, completed_median_seconds=medians, paired_ratios=ratios)


def stage_record(result, certificates):
    record = {key: result[key] for key in ('status', 'reason', 'statistics') if key in result}
    if 'certificate' in result:
        key = digest(result['certificate'])
        certificates[key] = result['certificate']
        record['certificate_sha256'] = key
    return record


def find_stages(value, certificates):
    out = []
    if isinstance(value, dict):
        for key, item in value.items():
            if key == 'two_meridian':
                out.append(stage_record(item, certificates))
            elif isinstance(item, (dict, list)):
                out.extend(find_stages(item, certificates))
    elif isinstance(value, list):
        for item in value:
            out.extend(find_stages(item, certificates))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--rounds', type=int, default=9)
    parser.add_argument('--pipeline-rounds', type=int, default=5)
    parser.add_argument('--skip-pipeline', action='store_true')
    args = parser.parse_args()
    if min(args.rounds, args.pipeline_rounds) < 1:
        parser.error('round counts must be positive')
    functions, variant_hashes = variants()
    paths = sorted((ROOT/'fastunknot').rglob('*.py')) + [Path(__file__),
        ROOT/'two_meridian_research/baseline_two_meridian.py',
        ROOT/'two_meridian_research/corpus.json']

    def source_hashes():
        return {str(path.relative_to(ROOT)): sha256(path.read_bytes()).hexdigest() for path in paths}

    frozen = source_hashes()
    corpus = json.loads((ROOT/'two_meridian_research/corpus.json').read_text())
    rng, rows, certificates = random.Random(SEED), [], {}
    configurations = dict(ordinary=dict(seconds=3, max_objects=50000),
        compressed_group=dict(seconds=18, max_objects=50000, use_group=True,
            group_compressed_search=True, group_relators=True, group_seconds=15,
            group_max_work=20_000_000))
    for case in corpus['cases']:
        row = dict(case)
        samples, warmups = [], []
        for repetition in range(args.rounds + 1):
            order, measurements = list(STANDALONE_ARMS), {}
            rng.shuffle(order)
            for arm in order:
                start = perf_counter()
                result = functions[arm](Diagram.from_pd(case['pd']), seconds=None,
                                        max_work=None, max_attempts=None)
                elapsed = perf_counter() - start
                conclusive = result['status'] in ('UNKNOT', 'KNOTTED')
                completed = conclusive or result.get('reason') == EXHAUSTIVE_REASON
                assert completed, (case['name'], arm, result)
                if conclusive:
                    assert result['status'] == case['expected']
                measurements[arm] = dict(seconds=elapsed, completed=completed,
                    recognition_conclusive=conclusive, **stage_record(result, certificates))
            assert len({m.get('certificate_sha256') for m in measurements.values()}) == 1
            sample = dict(order=order, measurements=measurements)
            (samples if repetition else warmups).append(sample)
        row['standalone'] = dict(warmups=warmups, samples=samples,
                                 **summarize(samples, STANDALONE_ARMS))
        row['work_capped_probe'] = {}
        for arm in ('baseline', 'optimized'):
            result = functions[arm](Diagram.from_pd(case['pd']), seconds=None,
                                    max_work=2_000_000, max_attempts=10000)
            row['work_capped_probe'][arm] = stage_record(result, certificates)
        row['pipeline'] = {}
        if not args.skip_pipeline:
            for mode, options in configurations.items():
                samples, warmups = [], []
                for repetition in range(args.pipeline_rounds + 1):
                    order, measurements = list(PIPELINE_ARMS), {}
                    rng.shuffle(order)
                    for arm in order:
                        saved = maintained.two_meridian_decide
                        maintained.two_meridian_decide = functions.get(arm, functions['optimized'])
                        try:
                            start = perf_counter()
                            result = recognize(Diagram.from_pd(case['pd']),
                                use_two_meridian=arm != 'disabled', **options)
                            elapsed = perf_counter() - start
                        finally:
                            maintained.two_meridian_decide = saved
                        completed = result.status in ('UNKNOT', 'KNOTTED')
                        if completed:
                            assert result.status == case['expected'], (case['name'], mode, arm, result)
                        measurements[arm] = dict(seconds=elapsed, completed=completed,
                            status=result.status, method=result.method,
                            stages=find_stages(result.evidence, certificates),
                            reason=result.evidence.get('reason'))
                    sample = dict(order=order, measurements=measurements)
                    (samples if repetition else warmups).append(sample)
                row['pipeline'][mode] = dict(warmups=warmups, samples=samples,
                                            **summarize(samples, PIPELINE_ARMS))
        rows.append(row)
        print(case['name'], row['standalone']['completed_median_seconds'], flush=True)
    # Other research modules may be edited concurrently. They cannot affect
    # this experiment unless imported; every actually loaded dependency must
    # have existed and matched the before-run snapshot. Variant modules are
    # compiled from the separately frozen source strings above.
    after = source_hashes()
    used = {str(path.relative_to(ROOT)) for path in paths
            if path.parent != ROOT/'fastunknot' and 'fastunknot' not in path.parts}
    for name, module in list(sys.modules.items()):
        filename = getattr(module, '__file__', None)
        if name.startswith('fastunknot.') and filename:
            path = Path(filename).resolve()
            if path.is_relative_to(ROOT) and path.suffix == '.py':
                key = str(path.relative_to(ROOT))
                assert key in frozen, 'newly created dependency was imported: ' + key
                used.add(key)
    assert all(after[key] == frozen[key] for key in used), 'used source changed during measurements'
    data = dict(baseline_commit=BASELINE_COMMIT, baseline_sha256=BASELINE_SHA256,
        variant_sha256=variant_hashes, source_sha256={key: frozen[key] for key in sorted(used)},
        source_hashes_unchanged=True,
        source_audit_scope='every imported fastunknot dependency plus benchmark, frozen baseline and corpus; unrelated unimported modules excluded',
        python=sys.version, platform=platform.platform(), seed=SEED,
        standalone_measured_rounds=args.rounds, pipeline_measured_rounds=args.pipeline_rounds,
        excluded_warmups_per_case_mode_arm=1, configurations=configurations,
        pipeline_stage_caps=dict(seconds=.05, max_work=2_000_000, max_attempts=10000),
        standalone_scope='fresh PD validation, exact exhaustive seed search, representation arithmetic and replay',
        standalone_completion='a verdict OR exhaustive failure completes the seed-class query; INCONCLUSIVE is never a knot verdict',
        pipeline_scope='fresh PD validation and whole recognition including all incumbent filters, optional seed stage, replay and fallback',
        ablations='stamped: candidate construction disabled; candidate_only: closed-set pruning disabled; exact frozen source substitutions recorded by hash',
        timing_exclusions='imports, loading the previously published corpus and cloning variant modules excluded',
        censoring='pipeline UNKNOWN excluded from completed-time medians and paired ratios, retained in raw samples',
        rows=rows, certificates=certificates)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(data, indent=2) + '\n')


if __name__ == '__main__':
    main()
