"""Whole-query A/A/B audit of independently replayed group certificates."""
import argparse
import json
from pathlib import Path
import platform
import random
from statistics import median
import sys
from time import perf_counter
from fastunknot import Diagram, recognize
from fastunknot.group_certificate import group_decide
from fastunknot.simplify import simplify
from hard_unknots import SURVIVORS

ROOT = Path(__file__).resolve().parent


def cases():
    for i, (_, strands, word) in enumerate(SURVIVORS):
        d, _ = simplify(Diagram.from_braid(strands, word), r3=True)
        yield f'survivor-{i:02d}', d.pd
    for name in ('trefoil', 'conway', 'kinoshita_terasaka', 'hard_unknot_8',
                 'grid_determinant_one_knot', 'unknot_braid40'):
        d = Diagram.from_json(json.loads((ROOT/'examples'/(name+'.json')).read_text()))
        yield name, d.pd
    for name in ('monster', 'gst', 'gordian'):
        d = Diagram.from_json(json.loads((ROOT/'normal_research'/(name+'.json')).read_text()))
        yield name, d.pd


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rng, rows = random.Random(2662), []
    for name, pd in cases():
        samples = []
        for repetition in range(8):
            sequence = ['default', 'control', 'group']
            rng.shuffle(sequence)
            measurements = {}
            for arm in sequence:
                start = perf_counter()
                d = Diagram.from_pd(pd)
                result = recognize(d, seconds=0.25, max_objects=50000, use_group=arm == 'group')
                measurements[arm] = dict(seconds=perf_counter()-start,
                    status=result.status, method=result.method, group=result.evidence.get('group'))
            conclusive = {r['status'] for r in measurements.values() if r['status'] != 'UNKNOWN'}
            assert len(conclusive) <= 1
            if repetition:
                samples.append(dict(order=sequence, results=measurements))
        row = dict(name=name, crossings=len(pd), pd=pd, samples=samples,
            median_seconds={arm: median(s['results'][arm]['seconds'] for s in samples)
                            for arm in sequence},
            completed={arm: sum(s['results'][arm]['status'] != 'UNKNOWN' for s in samples)
                       for arm in sequence})
        rows.append(row)
        print(name, row['median_seconds'], row['completed'], flush=True)
    standalone = []
    for name, pd in cases():
        standalone.append(dict(name=name, result=group_decide(Diagram.from_pd(pd))))
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        seed=2662, measured_rounds=7, excluded_warmups=1, global_seconds=0.25,
        group_seconds=0.05, max_objects=50000,
        timing='fresh PD validation plus whole query; group includes independent replay',
        censoring='UNKNOWN is resource-limited, never a measured completion time',
        rows=rows, standalone=standalone), indent=2)+'\n')


if __name__ == '__main__':
    main()
