"""Whole-query normal-surface portfolio audit; run with the normal extra installed."""
import argparse
from importlib.metadata import version
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
from fastunknot.normal_surface import regina_decide


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    rng, rows = random.Random(2650), []
    for name, path in [('monster', ROOT/'normal_research/monster.json'),
                       ('gst', ROOT/'normal_research/gst.json'),
                       ('gordian', ROOT/'normal_research/gordian.json'),
                       ('conway', ROOT/'examples/conway.json')]:
        pd = Diagram.from_json(json.loads(path.read_text())).pd
        samples = []
        for repetition in range(6):
            sequence = ['default', 'control', 'portfolio']
            rng.shuffle(sequence)
            measurements = {}
            for arm in sequence:
                start = perf_counter()
                d = Diagram.from_pd(pd)
                result = recognize(d, seconds=4, max_objects=50000, use_regina=arm == 'portfolio')
                measurements[arm] = dict(seconds=perf_counter()-start,
                    status=result.status, method=result.method, regina=result.evidence.get('regina'))
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
    # Native calls include a new interpreter, import, conversion and cleanup.
    native = []
    for name in ('monster', 'gordian', 'gst'):
        d = Diagram.from_json(json.loads((ROOT/'normal_research'/(name+'.json')).read_text()))
        native.append(dict(name=name, result=regina_decide(d, seconds=3)))
    args.output.write_text(json.dumps(dict(python=sys.version, platform=platform.platform(),
        regina_distribution=version('regina'), seed=2650, measured_rounds=5,
        excluded_warmups=1, global_seconds=4, native_seconds=2, max_objects=50000,
        timing='fresh PD validation plus whole query; every native attempt starts a fresh child',
        censoring='UNKNOWN is a resource-limited outcome, never a measured completion time',
        rows=rows, standalone_native=native), indent=2)+'\n')


if __name__ == '__main__':
    main()
