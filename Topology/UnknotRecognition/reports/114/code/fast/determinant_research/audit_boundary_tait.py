"""Compare boundary-only completion queries with independently rebuilt diagrams."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

from boundary_tait import BoundaryTait, coloring, ROOT
from fastunknot import Diagram
from fastunknot.scan_fast import FastScan
from detshadow.diagram import complete_matching


def matchings(labels):
    if not labels:
        yield ()
        return
    for i in range(1, len(labels)):
        for rest in matchings(labels[1:i]+labels[i+1:]):
            yield ((labels[0], labels[i]),)+rest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    source = ROOT/'synthesis/data/determinant-terminal-geometry-audit.json'
    inputs = json.loads(source.read_text())['inputs']
    totals = dict(diagrams=len(inputs), stages=0, queries=0, disconnected=0,
                  singular_kernels=0, max_terminals=0, max_nullity=0,
                  arbitrary_pairings=0, arbitrary_accepted=0,
                  declined_classical=0, rejected_nonclassical=0)
    for number, row in enumerate(inputs):
        diagram = Diagram.from_braid(row['strands'], row['word'])
        order = row['order']
        palette = coloring(diagram.pd)
        scan = FastScan(shape_cache=False)
        for stage, index in enumerate(order):
            engine = BoundaryTait(diagram.pd, order, stage, palette)
            engine.prepare_kernel(verify=True)
            totals['stages'] += 1
            totals['singular_kernels'] += int(engine.kernel.nullity > 0)
            totals['max_nullity'] = max(totals['max_nullity'], engine.kernel.nullity)
            totals['max_terminals'] = max(totals['max_terminals'], len(engine.terminals))
            for m in set(scan.mid)-{None}:
                pairs = scan.algebra.pairs[m]
                reference = complete_matching([diagram.pd[i] for i in order[stage:]], pairs)
                value, data = engine.evaluate(pairs)
                assert value == reference.euler_i(), (row, stage, pairs, value)
                assert data['unreduced_euler'] == 2*reference.euler_one()
                assert data['shadow_components'] == reference.shadow_components()
                assert data['zero_circles'] == len(reference.state_circles(0))
                assert data['link_components'] == reference.orientation_data()[0]
                totals['queries'] += 1
                totals['disconnected'] += int(data['shadow_components'] > 1)
            if number < 20 and 4 <= len(engine.labels) <= 8:
                for pairs in matchings(engine.labels):
                    totals['arbitrary_pairings'] += 1
                    try:
                        reference = complete_matching([diagram.pd[i] for i in order[stage:]], pairs)
                    except ValueError:
                        reference = None
                    try:
                        value, data = engine.evaluate(pairs)
                    except ValueError:
                        totals['rejected_nonclassical' if reference is None else 'declined_classical'] += 1
                    else:
                        assert reference is not None, (row, stage, pairs)
                        assert value == reference.euler_i()
                        assert data['unreduced_euler'] == 2*reference.euler_one()
                        totals['arbitrary_accepted'] += 1
            scan.add_crossing(diagram.pd[index])
    files = [Path(__file__), Path(__file__).with_name('boundary_tait.py'), source,
             ROOT/'fast/fastunknot/boundary_connectivity.py',
             ROOT/'reports/26/detshadow/diagram.py', ROOT/'reports/26/detshadow/linalg.py']
    out = dict(scope=__doc__, arbitrary_scope='All pairings at boundaries of size 4 through 8 in the first 20 input diagrams',
               totals=totals, inputs=inputs,
               sources={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(totals))


if __name__ == '__main__':
    main()
