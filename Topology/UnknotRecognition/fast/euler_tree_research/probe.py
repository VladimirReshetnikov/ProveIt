"""Bounded trefoil and figure-eight profiles with flat sectors and Euler trees, retaining partial proof chains and failures.

Run from fast/: python -B -m euler_tree_research.probe --output PATH
These are single exploratory runs, not repeated timings or complete-recognition
runtime claims. A cooperative cancellation returns no partial result; it is
recorded explicitly and cannot be interpreted as a knottedness verdict.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import sys
from time import monotonic, perf_counter_ns

from fastunknot.diagram import Diagram
from .benchmark import (arm_configs, baseline_pin, encode_result, load_baseline,
                        run_query, source_hashes, verify_result)


class _ProbeCeiling(TimeoutError):
    pass


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--seconds', type=float, default=30)
    args = parser.parse_args()
    if not 0 < args.seconds < float('inf'):
        parser.error('seconds must be finite and positive')
    baseline = load_baseline()
    configs = arm_configs(bounded=True)
    output = dict(passed=False, source_sha256=source_hashes(), baseline=baseline_pin(),
        python=sys.version, platform=platform.platform(),
        scope='eight single bounded trefoil and figure-eight profiles; incomplete outcomes are not knot verdicts or complete-recognition timings',
        timing_scope='native construction, search, internal replay and serialization; separate independent replay is outside timing',
        records=[])
    target = Path(args.output)

    def save():
        target.write_text(json.dumps(output, indent=2)+'\n')

    cases = [('trefoil', Diagram.from_braid(2, [1, 1, 1])),
             ('figure_eight', Diagram.from_braid(3, [1, -2, 1, -2]))]
    for name, diagram, arm in ((name, diagram, arm) for name, diagram in cases
            for arm in ('prior_vertex_q', 'prior_vertex_lp', 'tree_restricted', 'tree_source')):
        start_seconds = monotonic()
        start_ns = perf_counter_ns()

        def check():
            if monotonic()-start_seconds > args.seconds:
                raise _ProbeCeiling(f'{args.seconds:g}-second cooperative exploration ceiling')

        try:
            result = run_query(diagram, arm, baseline, configs[arm], check=check)
        except _ProbeCeiling as exc:
            result = dict(status='CANCELLED', reason=str(exc))
        encoded = encode_result(result)
        elapsed_ns = perf_counter_ns()-start_ns
        record = dict(id=name, input_pd=[list(row) for row in diagram.pd], arm=arm, config=configs[arm], cancellation_seconds=args.seconds,
                      elapsed_ns=elapsed_ns, result=result, result_bytes=len(encoded),
                      output_sha256=sha256(encoded).hexdigest())
        if result['status'] == 'CANCELLED':
            record.update(independent_replay=None, partial_result_returned=False,
                          limitation='caller cancellation loses the in-progress partial result; no chain or verdict is asserted')
        else:
            replay_start = perf_counter_ns()
            record['independent_replay'] = verify_result(diagram, result, arm)
            record['independent_replay_ns'] = perf_counter_ns()-replay_start
            record['partial_result_returned'] = result['status'] == 'INCONCLUSIVE'
        output['records'].append(record)
        save()
        print(name, arm, result['status'], result.get('stats'), flush=True)
    if output['source_sha256'] != source_hashes():
        raise AssertionError('probed source changed during the run')
    output['passed'] = True
    save()


if __name__ == '__main__':
    main()
