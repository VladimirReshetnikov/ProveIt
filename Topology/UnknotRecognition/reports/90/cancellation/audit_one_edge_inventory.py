"""Independent dense-row audit proving the fixture has cancellation radius two.

This does not call the cluster producer or its hyperplane builder.  The
incoming local normal-coordinate decoder and maintained source/coordinate
validators are reused.  All possible one-edge critical offsets are checked;
their Euler characteristics exclude vertex meridians without an orbit query.
"""
import bootstrap
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
import json
from math import gcd
from types import SimpleNamespace

from fastunknot.normal_cocycle import _rank_one_cocycle_seed_details
from fastunknot.normal_weight_defect import local_coordinates_from_weights
from fastunknot.normal_surface_geometry import _coordinates, _edge, NormalOrbitError
from fastunknot.normal_vertex_gate import verify_vertex_disc_certificate


def dense_hyperplanes(context):
    edges = context.edges
    index = {e: i for i, e in enumerate(edges)}
    m = len(edges)
    equations = set()

    def add(terms):
        row = [0]*m
        for e, value in terms:
            row[index[e]] += value
        common = 0
        for value in row:
            common = gcd(common, abs(value))
        if common:
            sign = 1 if next(value for value in row if value) > 0 else -1
            equations.add(tuple(sign*value//common for value in row))

    for e in edges:
        add([(e, 1)])
    for t in range(len(context.baseline_rows)):
        roots = context.prepared['edge_roots'][6*t:6*t+6]
        opposite = [(roots[0], roots[5]), (roots[1], roots[4]), (roots[2], roots[3])]
        for a, b in combinations(range(3), 2):
            add([(e, 1) for e in opposite[a]] + [(e, -1) for e in opposite[b]])
        for v in range(4):
            for a, b in combinations([j for j in range(4) if j != v], 2):
                add([(context.prepared['edge_roots'][_edge(t, v, a)], 1),
                     (context.prepared['edge_roots'][_edge(t, v, b)], 1),
                     (context.prepared['edge_roots'][_edge(t, a, b)], -1)])
    return sorted(equations)


def main():
    saved = json.loads((bootstrap.HERE/'artifacts/disconnected_disc.json').read_text())
    raw = saved['triangulation']
    seed, prepared = _rank_one_cocycle_seed_details(raw)
    assert prepared['vertices'] == 1
    data = _coordinates(prepared, seed['coordinates'], lambda: None)
    context = SimpleNamespace(prepared=prepared, baseline_rows=seed['coordinates'],
        edges=tuple(sorted(data['weights'])), baseline=data['weights'],
        baseline_euler=data['euler_characteristic'])
    assert sum(bool(value) for value in context.baseline.values()) >= 2
    equations = dense_hyperplanes(context)
    baseline = [context.baseline[e] for e in context.edges]
    offsets = set()
    incidence_count = 0
    for row in equations:
        constant = sum(a*b for a, b in zip(row, baseline))
        for j, coefficient in enumerate(row):
            if not coefficient:
                continue
            incidence_count += 1
            delta = Fraction(-constant, coefficient)
            if delta > 0 and delta.denominator == 1 and int(delta) % 2 == 0:
                offsets.add((context.edges[j], int(delta)))
    valid = []
    invalid = []
    for e, delta in sorted(offsets):
        weights = dict(context.baseline)
        weights[e] += delta
        rows = []
        try:
            for t in range(len(context.baseline_rows)):
                values = local_coordinates_from_weights([
                    weights[edge] for edge in context.prepared['edge_roots'][6*t:6*t+6]])
                assert all(value.denominator == 1 for value in values)
                rows.append(list(map(int, values)))
        except NormalOrbitError:
            invalid.append(dict(edge=e, increment=delta))
            continue
        data = _coordinates(context.prepared, rows, lambda: None)
        valid.append(dict(edge=e, increment=delta, coordinates=rows,
                          euler_characteristic=data['euler_characteristic'],
                          pieces=sum(map(sum, rows))))
    assert context.baseline_euler <= 0
    assert all(profile['euler_characteristic'] <= 0 for profile in valid)
    assert verify_vertex_disc_certificate(raw, saved['coordinates'], saved['certificate'])
    known = _coordinates(context.prepared, saved['coordinates'], lambda: None)
    defect = [known['weights'][e]-context.baseline[e] for e in context.edges]
    assert all(value >= 0 and value % 2 == 0 for value in defect)
    assert sum(value > 0 for value in defect) == 2
    result = dict(source_sha256=sha256(json.dumps(raw,sort_keys=True).encode()).hexdigest(),
        tetrahedra=len(context.baseline_rows), baseline_euler=context.baseline_euler,
        hyperplanes=len(equations), row_edge_incidences=incidence_count,
        positive_even_offsets=len(offsets), valid_profiles=valid,
        invalid_offsets=invalid, minimum_vertex_cancellation_support=2,
        proof='Every one-edge vertex meridian must occur at an active-hyperplane '
              'offset. All admissible positive even offsets listed here have '
              'nonpositive Euler characteristic, and the coherent vector does too. '
              'An independently certified two-edge meridian supplies the upper bound.',
        scope='Exact finite algebraic audit of the one-edge class in this source; '
              'no conclusion about arbitrary cancellation-component budgets.')
    (bootstrap.HERE/'artifacts/one_edge_inventory.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ('hyperplanes','row_edge_incidences',
          'positive_even_offsets','minimum_vertex_cancellation_support')}))
    print([(x['edge'],x['increment'],x['euler_characteristic']) for x in valid])


if __name__ == '__main__':
    main()
