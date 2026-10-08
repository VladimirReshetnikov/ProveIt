"""Paired full-query comparison of Whitehead, overlap and normal-surface search."""
import argparse
from importlib.metadata import version
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter
from fastunknot import Diagram, recognize
from fastunknot.simplify import simplify
from hard_unknots import SURVIVORS

ROOT = Path(__file__).resolve().parent


def cases():
    for i, (_, strands, word) in enumerate(SURVIVORS):
        d, _ = simplify(Diagram.from_braid(strands, word), r3=True)
        yield f'survivor-{i:02d}', d.pd
        yield f'mirror-{i:02d}', d.mirror().pd
    for name in ('conway', 'hard_unknot_8'):
        yield name, Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text())).pd
    for name in ('monster', 'gst', 'gordian'):
        yield name, Diagram.from_json(json.loads((ROOT/'normal_research'/(name+'.json')).read_text())).pd


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rng, rows = random.Random(2673), []
    for name, pd in cases():
        samples = []
        for repetition in range(6):
            sequence = ['default', 'whitehead', 'overlap', 'regina']
            rng.shuffle(sequence)
            measurements = {}
            for arm in sequence:
                start = perf_counter()
                d = Diagram.from_pd(pd)
                result = recognize(d, seconds=4, max_objects=50000,
                    use_group=arm in ('whitehead', 'overlap'), group_relators=arm == 'overlap',
                    group_seconds=2, group_max_work=10000000, use_regina=arm == 'regina')
                measurements[arm] = dict(seconds=perf_counter()-start, status=result.status,
                    method=result.method, group=result.evidence.get('group'), regina=result.evidence.get('regina'))
            conclusive = {r['status'] for r in measurements.values() if r['status'] != 'UNKNOWN'}
            assert len(conclusive) <= 1
            if repetition:
                samples.append(dict(order=sequence, results=measurements))
        row = dict(name=name, crossings=len(pd), pd=pd, samples=samples,
            median_seconds={arm: median(s['results'][arm]['seconds'] for s in samples) for arm in sequence},
            completed={arm: sum(s['results'][arm]['status'] != 'UNKNOWN' for s in samples) for arm in sequence})
        rows.append(row)
        print(name, row['median_seconds'], row['completed'], flush=True)
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        regina_distribution=version('regina'), seed=2673, measured_rounds=5, excluded_warmups=1,
        global_seconds=4, group_seconds=2, group_max_work=10000000, normal_seconds=2, max_objects=50000,
        timing='fresh validated PD plus entire query, including independent group replay or native startup',
        censoring='UNKNOWN means the query did not finish under its resource limits', rows=rows), indent=2)+'\n')


if __name__ == '__main__':
    main()
