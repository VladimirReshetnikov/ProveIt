"""Literal Regina cut oracle, isolated per case with explicit expansion caps."""

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


def worker(corpus, index):
    import regina
    from fastunknot.integer_codec import encoded_integer
    from normal_orbit_research.fixtures import regina_surface, regina_triangulation
    case = json.loads(Path(corpus).read_text())['cases'][index]
    rows = [[encoded_integer(x) for x in row] for row in case['coordinates']]
    triangulation = regina_triangulation(case['triangulation'])
    surface = regina_surface(triangulation, rows)
    started = time.perf_counter()
    cut = surface.cutAlong()
    genera = [component.recogniseHandlebody() for component in cut.triangulateComponents()]
    counter = Counter(genera)
    print(json.dumps(dict(status='COMPLETE', regina_version=regina.versionString(),
        explicit_tetrahedra=cut.size(), elapsed_seconds=time.perf_counter()-started,
        histogram=[dict(genus=g, multiplicity=n) for g, n in sorted(counter.items())])))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--corpus', required=True)
    parser.add_argument('--output')
    parser.add_argument('--worker', type=int)
    parser.add_argument('--cap', type=int, default=4096)
    parser.add_argument('--timeout', type=float, default=25)
    args = parser.parse_args()
    if args.worker is not None:
        worker(args.corpus, args.worker)
        return
    from fastunknot.integer_codec import encoded_integer
    corpus = Path(args.corpus).resolve()
    records = []
    report = dict(corpus_sha256=hashlib.sha256(corpus.read_bytes()).hexdigest(),
                  expansion_cap=args.cap, per_case_timeout=args.timeout, records=records)
    for index, case in enumerate(json.loads(corpus.read_text())['cases']):
        weight = sum(encoded_integer(x) for row in case['coordinates'] for x in row)
        record = dict(index=index, id=case['id'], normal_weight_bits=weight.bit_length())
        if weight > args.cap:
            record['status'] = 'NOT_ATTEMPTED_EXPANSION_CAP'
        else:
            try:
                run = subprocess.run([sys.executable, str(Path(__file__).resolve()),
                    '--corpus', str(corpus), '--worker', str(index)],
                    capture_output=True, text=True, timeout=args.timeout, check=False)
                if run.returncode:
                    record.update(status='ERROR', stderr=run.stderr[-3000:])
                else:
                    record.update(json.loads(run.stdout))
            except subprocess.TimeoutExpired:
                record['status'] = 'TIMEOUT'
        records.append(record)
        report['counts'] = dict(Counter(r['status'] for r in records))
        Path(args.output).write_text(json.dumps(report, indent=2)+'\n')
        print(json.dumps(record), flush=True)


if __name__ == '__main__':
    main()
