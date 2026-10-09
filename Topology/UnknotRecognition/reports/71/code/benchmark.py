"""Paired complete-grammar measurements; no native knot-recognizer claims."""
import argparse
import json
import platform
import statistics
import time
from pathlib import Path
from envelope_kernel import Candidate, Envelope, disk_compatible, reduce_family
from fixtures import restricted_grammar
from grammar import compile_envelopes, solve
from checker import check_run
from surface_replay import replay_witness


def run(repeats=5):
    output = {'environment': {'python': platform.python_version(), 'platform': platform.platform()},
              'repeats': repeats, 'timing_scope': 'Includes envelope compilation, validation, identical viability filtering, transitions, deduplication, weighted reduction, and pruning certificate production. Excludes fixture creation and separate checker/mesh replay in all modes.',
              'fixtures': []}
    for r, lam, depth in [(6, 2, 12), (7, 2, 12), (8, 2, 12), (6, 5, 4)]:
        g = restricted_grammar(r, lam, depth)
        samples = {mode: [] for mode in ('exact', 'root', 'cycle')}
        results = {}
        for iteration in range(repeats):
            modes = ('exact','root','cycle') if iteration % 2 == 0 else ('cycle','root','exact')
            for mode in modes:
                start = time.perf_counter()
                answer = solve(g, mode)
                samples[mode].append(time.perf_counter() - start)
                results[mode] = answer
        assert len({(a['status'], a['cost_hex']) for a in results.values()}) == 1
        checks = {}
        for mode, answer in results.items():
            start = time.perf_counter()
            valid, why = check_run(g, answer)
            checks[mode] = time.perf_counter() - start
            assert valid, why
            if answer['witness']:
                assert replay_witness(g, answer['witness'])['disk']
        entry = {'r': r, 'lambda': lam, 'depth': depth, 'initial_candidates': len(g.initial),
                 'options_per_layer': len(g.layers[0]), 'status': results['cycle']['status'],
                 'cost_hex': results['cycle']['cost_hex'], 'seconds': samples,
                 'median_seconds': {k: statistics.median(v) for k,v in samples.items()},
                 'separate_checker_seconds': checks,
                 'retained_by_stage': {m: [s['retained'] for s in a['statistics']] for m,a in results.items()},
                 'generated_total': {m: sum(s['generated'] for s in a['statistics']) for m,a in results.items()}}
        output['fixtures'].append(entry)
        print(json.dumps({'fixture': [r,lam,depth], 'seconds': entry['median_seconds'],
                          'retained': {m: max(v) for m,v in entry['retained_by_stage'].items()}}), flush=True)
    # One supplied cap, with no continuation amortization: direct scan is the right baseline.
    g = restricted_grammar(8, 2, 0)
    sigma, rho = compile_envelopes(g)
    samples = {m: [] for m in ('direct', 'root', 'cycle')}
    for iteration in range(repeats):
        for mode in (('direct','root','cycle') if iteration % 2 == 0 else ('cycle','root','direct')):
            start = time.perf_counter()
            items = g.initial
            if mode != 'direct':
                env = Envelope(sigma[0], rho[0])
                reduced = reduce_family(items, env, mode=mode)
                items = [items[i] for i in reduced.retained]
            answer = min(c.cost for c in items if disk_compatible(c.partition, g.caps[0].partition))
            samples[mode].append(time.perf_counter() - start)
    output['single_cap_control'] = {'r':8, 'lambda':2, 'candidates':len(g.initial),
        'seconds':samples, 'median_seconds':{m:statistics.median(v) for m,v in samples.items()}}
    return output

if __name__ == '__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--output',type=Path,default=Path('results/benchmark.json'))
    args=parser.parse_args()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(run(args.repeats),indent=2)+'\n')
