"""Paired production disk-transfer comparisons, with A/A and adverse controls.

Synthetic coefficient blocks are not asserted to be actual knot complexes.
Their generation is outside timing; diagram timings include order selection.
Normal recognition keeps all default prefilters. Seven shuffled rounds.
"""
import argparse
import json
from pathlib import Path
import platform
import random
import statistics
import sys
from time import perf_counter

sys.path.insert(0, str(Path(__file__).resolve().parent / 'tests'))
from disk_oracles import regular_representation_homology
from test_disk_scan import synthetic_scan
from fastunknot import Diagram, khovanov_rank, recognize
from fastunknot.radical_transfer import snapshot
from fastunknot.residue import AdaptiveScan
from fastunknot.scan_fast import FastScan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rng = random.Random(2026100821)
    records = []
    specifications = [('dense3_12',3,12,False),('dense3_24',3,24,False),
                      ('dense3_40',3,40,False),('dense4_24',4,24,False),
                      ('sparse4_40',4,40,True)]
    for name,b,m,sparse in specifications:
        expected_scan = synthetic_scan(b,m,sparse)
        expected = regular_representation_homology(snapshot(expected_scan),expected_scan.algebra)
        arms = ('standard','control','adaptive','disk-adaptive')
        samples = []
        for _ in range(7):
            order = list(arms); rng.shuffle(order); timings = {}; results = {}
            for mode in order:
                scan = synthetic_scan(b,m,sparse)
                start = perf_counter()
                if mode in ('standard','control'):
                    FastScan.eliminate(scan)
                elif mode == 'adaptive':
                    # Bind the old policy to its own class: its virtual residue
                    # shortcut must not accidentally invoke the disk extension.
                    scan.__class__ = AdaptiveScan
                    scan.eliminate()
                else:
                    scan.eliminate()
                timings[mode] = perf_counter()-start
                results[mode] = dict(stats=scan.stats,objects=scan.live,nonzero_maps=any(scan.out))
                assert regular_representation_homology(snapshot(scan),scan.algebra)==expected
            samples.append(dict(order=order,seconds=timings,results=results))
        rows = dict(name=name,kind='synthetic',b=b,m=m,sparse=sparse,samples=samples,
                    expected_homology=expected)
        records.append(rows)
    for name in ('conway','kinoshita_terasaka','stress_braid5_36','hard_unknot_8'):
        source = json.loads((Path(__file__).parent/'examples'/(name+'.json')).read_text())
        diagram = Diagram.from_json(source)
        samples = []
        for _ in range(7):
            order = ['standard','control','adaptive','disk-adaptive']; rng.shuffle(order)
            times, results = {}, {}
            for mode in order:
                start=perf_counter()
                result=khovanov_rank(diagram.pd,reduction='standard' if mode=='control' else mode)
                times[mode]=perf_counter()-start;results[mode]=result
            assert all(r['by_degree']==results['standard']['by_degree'] for r in results.values())
            pipeline_times,pipeline_results={},{}
            for mode in ('standard','disk-adaptive') if rng.randrange(2) else ('disk-adaptive','standard'):
                start=perf_counter();pipeline_results[mode]=recognize(Diagram.from_json(source),reduction=mode).to_json()
                pipeline_times[mode]=perf_counter()-start
            assert pipeline_results['standard']['status']==pipeline_results['disk-adaptive']['status']
            samples.append(dict(order=order,seconds=times,results=results,
                                pipeline_seconds=pipeline_times,pipeline_results=pipeline_results))
        records.append(dict(name=name,kind='diagram',source=source,samples=samples))
    for row in records:
        row['median_standard_over']={arm:statistics.median(s['seconds']['standard']/s['seconds'][arm]
            for s in row['samples']) for arm in ('control','adaptive','disk-adaptive')}
        print(row['name'],row['median_standard_over'],
              {key:row['samples'][0]['results']['disk-adaptive']['stats'][key]
               for key in ('disk_attempts','disk_transfers','disk_budget_fallbacks','disk_declines')},flush=True)
    args.output.write_text(json.dumps(dict(python=platform.python_version(),seed=2026100821,
                                          rounds=7,scope=__doc__,cases=records),indent=2)+'\n')


if __name__=='__main__':
    main()
