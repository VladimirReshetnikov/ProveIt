"""Pinned A/A/B audit of exact donor-length pruning, including full replay."""
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import statistics
import subprocess
from time import perf_counter
from types import ModuleType

import residual_bridge as bridge
from residual_bridge import FAST, REPO, load_delivery
from benchmark_residual import incumbent
from fastunknot import relator_overlap
from fastunknot.group_certificate import _Budget

BASELINE = '875c8565dac728aab298507cad46910966c614a5'
SOURCE = 'Topology/UnknotRecognition/fast/fastunknot/relator_overlap.py'


def main():
    baseline = ModuleType('pinned_overlap')
    blob = subprocess.check_output(['git', 'show', BASELINE + ':' + SOURCE], cwd=REPO)
    exec(compile(blob, BASELINE + ':' + SOURCE, 'exec'), baseline.__dict__)
    current = relator_overlap.overlap_move
    functions = dict(baseline=baseline.overlap_move, control=baseline.overlap_move, pruned=current)
    paths = [*sorted((FAST/'fastunknot').glob('*.py')),
             *sorted((FAST/'exposure_research').glob('*.py')), FAST/'normal_research/gordian.json']
    hashes = {str(p.relative_to(REPO)): sha256(p.read_bytes()).hexdigest() for p in paths}
    rng = random.Random(261008114)
    # Check the complete witness, including ties, signs and rotation positions.
    for _ in range(2000):
        words = [[rng.choice((-3,-2,-1,1,2,3)) for _ in range(rng.randrange(18))]
                 for _ in range(rng.randrange(9))]
        a = baseline.overlap_move(words, _Budget(lambda: None, 1000000, 10000000))
        b = current(words, _Budget(lambda: None, 1000000, 10000000))
        assert a == b, (words, a, b)
    pd = json.loads((FAST/'normal_research/gordian.json').read_text())['pd']
    cases = {
        'repeated_16x128': [list(range(1,129)) for _ in range(16)],
        'repeated_128x128': [list(range(1,129)) for _ in range(128)],
        'disjoint_16x128': [list(range(128*i+1,128*i+129)) for i in range(16)],
        'later_longer': [[1,2],[1,2],[3,4,5,6],[6,3,4,5]],
        'native_explicit': None,
        'native_exposure_overlap': None,
    }
    samples = []
    expected = {}
    try:
        with load_delivery():
            for round_number in range(6):
                jobs = [(name,arm) for name in cases for arm in functions]
                rng.shuffle(jobs)
                for name,arm in jobs:
                    fn = functions[arm]
                    relator_overlap.overlap_move = bridge.overlap_move = fn
                    budget = _Budget(lambda: None, 1000000, 100000000)
                    start = perf_counter()
                    if name == 'native_explicit':
                        result = incumbent(pd, 'explicit')
                    elif name == 'native_exposure_overlap':
                        result = bridge.residual_probe(pd)
                    else:
                        result = dict(move=fn(cases[name], budget))
                    elapsed = perf_counter()-start
                    if cases[name] is None:
                        assert result['status'] == 'UNKNOT', result
                        witness = result.pop('certificate')
                        result.pop('seconds', None)
                        work = result['stats'].get('search_work')
                    else:
                        witness = result['move']
                        work = 100000000-budget.left
                    digest = sha256(json.dumps(witness, sort_keys=True, separators=(',',':')).encode()).hexdigest()
                    if name in expected: assert digest == expected[name]
                    expected[name] = digest
                    samples.append(dict(case=name,arm=arm,round=round_number,warmup=round_number==0,
                                        seconds=elapsed,work=work,witness_sha256=digest,result=result))
                print('completed round',round_number,flush=True)
    finally:
        relator_overlap.overlap_move = bridge.overlap_move = current
    for p in paths: assert sha256(p.read_bytes()).hexdigest() == hashes[str(p.relative_to(REPO))]
    summary = {}
    for name in cases:
        summary[name] = {}
        for arm in functions:
            rows = [s for s in samples if s['case']==name and s['arm']==arm and not s['warmup']]
            ratios = [next(s['seconds'] for s in samples if s['case']==name and s['arm']=='baseline'
                           and s['round']==row['round'])/row['seconds'] for row in rows]
            summary[name][arm] = dict(median_seconds=statistics.median(r['seconds'] for r in rows),
                                     paired_baseline_ratio=statistics.median(ratios),work=rows[0]['work'])
    out = dict(baseline=BASELINE,baseline_source_sha256=sha256(blob).hexdigest(),
               source_sha256=hashes,python=platform.python_version(),seed=261008114,
               differential_witness_checks=2000,measured=90,warmups=18,
               scope='Only overlap_move is swapped; baseline/control use the identical pinned old function. '
                     'Kernels time one query, without copying inputs. Native arms include fresh PD, complete '
                     'search and explicit plus compressed full replay, with the same budgets as benchmark_residual. '
                     'Random audit, archive import and serialization are outside timed intervals.',
               summary=summary,samples=samples)
    (FAST/'results/overlap_bounds_20261008.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__ == '__main__': main()
