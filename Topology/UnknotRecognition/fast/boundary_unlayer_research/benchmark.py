"""Predeclared paired full-reduction timings; no Regina within timed calls."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
from statistics import median
import sys
from time import monotonic, perf_counter

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_crushing_chain import verify_crushing_chain
from .audit import supplied_reduction
from .common import (BENCHMARK_PROTOCOL, benchmark_bindings, normalized_result,
                     source_hashes, digest, diagram_options)
from .replay import replay, replay_reduction


def complete_outcome(kind, result):
    if kind == 'supplied':
        value = result['outcome']
        return value if value != 'INCONCLUSIVE' else None
    value = result['result']['status']
    return value if value != 'INCONCLUSIVE' else None


def run_sample(case, peel):
    started = perf_counter()
    if case['kind'] == 'supplied':
        result = supplied_reduction(case['source'], peel=peel,
                                    seconds=BENCHMARK_PROTOCOL['discovery_limit_seconds'], method='dfs')
        assert replay_reduction(result)
    else:
        options = diagram_options(peel=peel)
        diagram = case['diagram']
        deadline = monotonic()+BENCHMARK_PROTOCOL['discovery_limit_seconds']

        def check():
            if monotonic() >= deadline:
                raise TimeoutError('benchmark diagram discovery wall limit exhausted')

        try:
            answer = recognize_by_crushing(diagram, **options, check=check)
        except TimeoutError as error:
            answer = dict(status='INCONCLUSIVE', reason=str(error),
                          unreturned_recognition=True, work_complete=False)
            result = dict(options=options, result=answer,
                          final_boundary_faces=None, independent_chain_replay=False)
        else:
            if answer['status'] == 'INCONCLUSIVE':
                chain = answer['partial_chain']
            else:
                assert verify_crushing_recognition(diagram, answer['certificate'])
                chain = answer['certificate']['chain']
            assert verify_crushing_chain(diagram, chain)
            final = chain['triangulation']
            faces = [] if final is None else [[t, f] for t, row in enumerate(final['tetrahedra']) for f, r in enumerate(row) if r is None]
            result = dict(options=options, result=answer, final_boundary_faces=faces,
                          independent_chain_replay=True)
    # Serialize the complete proof result and hash it before stopping the
    # clock. Diagnostic discovery_seconds is the sole normalized field.
    normalized = normalized_result(result)
    payload = json.dumps(normalized, sort_keys=True, separators=(',', ':')).encode()
    checksum = sha256(payload).hexdigest()
    elapsed = perf_counter()-started
    expected = digest(normalized_result(case['arms']['peel' if peel else 'baseline']))
    outcome = complete_outcome(case['kind'], result)
    return dict(peel=peel, result=result, outcome=outcome, seconds=elapsed,
                serialized_bytes=len(payload), result_sha256=checksum,
                expected_audit_sha256=expected, matches_audit=checksum == expected)


def summarize(record):
    paired = record['paired']
    eligible = all(all(s['outcome'] is not None and s['matches_audit'] for s in pair['samples'].values())
                   and pair['samples']['baseline']['outcome'] == pair['samples']['peel']['outcome']
                   for pair in paired)
    ratios = [p['samples']['baseline']['seconds']/p['samples']['peel']['seconds'] for p in paired] if eligible else []
    return dict(eligible_complete_comparison=eligible,
                median_paired_baseline_over_peel=median(ratios) if ratios else None,
                paired_ratios=ratios,
                aa_ratio=record['aa']['samples'][0]['seconds']/record['aa']['samples'][1]['seconds'],
                scope='Supplied-source conditional workload only; no knot-recognition speedup claim.' if record['kind'] == 'supplied'
                      else 'Genuine diagram recognition, including independent proof replay and serialization.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    raw = args.audit.read_bytes()
    audit = json.loads(raw)
    replay(audit)
    pins = source_hashes()
    output = dict(schema='boundary-unlayer-benchmark-v1', passed=False,
                  source_sha256=pins, audit_sha256=sha256(raw).hexdigest(),
                  protocol=BENCHMARK_PROTOCOL, python=sys.version, platform=platform.platform(),
                  timing_scope='Fresh full reduction/recognition, independent replay, canonical JSON serialization and result hashing; no Regina inside timed calls.',
                  records=[])

    def save():
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(output, indent=2)+'\n')

    for index, case in enumerate(benchmark_bindings(audit)):
        if case['kind'] == 'diagram':
            case['diagram'] = Diagram.from_pd(case['input_pd'])
        record = dict(kind=case['kind'], id=case['id'], warmups=[], paired=[], aa={})
        output['records'].append(record)
        for peel in (False, True):
            record['warmups'].append(run_sample(case, peel))
            save()
        for round_index in range(BENCHMARK_PROTOCOL['paired_rounds']):
            order = ['baseline', 'peel'] if (index+round_index) % 2 == 0 else ['peel', 'baseline']
            pair = dict(round=round_index, order=order, samples={})
            record['paired'].append(pair)
            for arm in order:
                pair['samples'][arm] = run_sample(case, arm == 'peel')
                save()
        record['aa'] = dict(order=['baseline_a', 'baseline_b'], samples=[run_sample(case, False), run_sample(case, False)])
        record['summary'] = summarize(record)
        save()
        print(case['kind'], case['id'], record['summary'], flush=True)
    assert source_hashes() == pins
    # Partial outcomes are retained, but a complete output must be exactly
    # the source/method-specific result independently checked by the audit.
    for record in output['records']:
        samples = record['warmups']+[s for p in record['paired'] for s in p['samples'].values()]+record['aa']['samples']
        assert all(s['matches_audit'] for s in samples if s['outcome'] is not None)
    output['passed'] = True
    save()
    print('PASSED', flush=True)


if __name__ == '__main__':
    main()
