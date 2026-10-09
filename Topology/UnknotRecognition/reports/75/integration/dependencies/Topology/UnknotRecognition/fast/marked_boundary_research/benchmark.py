"""Native normal-boundary marked-order experiment; no explicit huge curve.

Run from fast/: python -m marked_boundary_research.benchmark --output PATH
The literal baseline walks every arc of one primitive normal meridian.  It
uses the same native interval graph, preserves half-edge identities, and is
run only below a stated point cap.  This is not an unknot recognizer benchmark.
"""

import argparse
import json
import platform
from pathlib import Path
from statistics import median
from time import perf_counter

from fastunknot.integer_codec import json_safe
from fastunknot.marked_boundary import marked_boundary_order, normal_marked_boundary_order
from fastunknot.marked_boundary_verify import verify_marked_boundary_certificate
from fastunknot.normal_surface_geometry import normal_arc_pairings
from normal_orbit_research.fixtures import boundary_cap, layered_torus


def first_half_edge(pairs, point):
    candidates = []
    for index, pair in enumerate(pairs):
        if pair.a <= point <= pair.b:
            candidates.append((index, point, 0))
        if pair.c <= point <= pair.d:
            source = pair.a + pair.d - point if pair.reverse else point - pair.c + pair.a
            candidates.append((index, source, 1))
    return min(candidates)


def literal_cycle(size, pairs, marks, initial):
    """Constant-space literal arc walk for the one chosen native component."""
    by_point = {point: index for index, point in enumerate(marks)}
    current, order, gaps, gap, visited = initial, [], [], 0, 0
    while True:
        row, source, side = current
        pair = pairs[row]
        target = pair.image(source)
        vertex = source if side == 0 else target
        if vertex in by_point:
            order.append(by_point[vertex])
        other = target if side == 0 else source
        arrival = (row, source, 1 - side)
        if other in by_point:
            gaps.append(gap)
            gap = 0
        else:
            gap += 1
        successors = []
        for index, candidate in enumerate(pairs):
            if candidate.a <= other <= candidate.b:
                successors.append((index, other, 0))
            if candidate.c <= other <= candidate.d:
                preimage = (candidate.a + candidate.d - other if candidate.reverse
                            else other - candidate.c + candidate.a)
                successors.append((index, preimage, 1))
        successors.remove(arrival)
        if len(successors) != 1:
            raise ArithmeticError('the literal boundary graph does not have degree two')
        current = successors[0]
        visited += 1
        if current == initial:
            break
        if visited >= size:
            raise ArithmeticError('literal boundary traversal did not close')
    return dict(marks=order, gaps=gaps, vertices=visited)


def timed(call, repeats):
    elapsed, result = [], None
    for _ in range(repeats):
        before = perf_counter()
        result = call()
        elapsed.append(perf_counter() - before)
    return median(elapsed), result


def small_controls(repeats=101):
    """Interleave tiny dimension controls to reduce warm-up and drift effects."""
    results = []
    for tetrahedra in (4, 64):
        raw, coordinates = layered_torus(tetrahedra)
        size, pairs = normal_arc_pairings(raw, coordinates, boundary=True)
        for marks in ([], [0]):
            samples = {encoding: dict(producer=[], replay=[])
                       for encoding in ('moments', 'one_hot')}
            for repetition in range(repeats):
                encodings = ('moments', 'one_hot') if repetition % 2 else ('one_hot', 'moments')
                for encoding in encodings:
                    start = perf_counter()
                    answer = marked_boundary_order(size, pairs, marks,
                        weight_encoding=encoding, record_certificate=True)
                    samples[encoding]['producer'].append(perf_counter() - start)
                    start = perf_counter()
                    accepted = verify_marked_boundary_certificate(size, pairs, marks,
                        answer['certificate'], weight_encoding=encoding)
                    samples[encoding]['replay'].append(perf_counter() - start)
                    if not accepted:
                        raise ArithmeticError('small encoding control failed replay')
            results.append(dict(tetrahedra=tetrahedra, points=size, marks=len(marks),
                repeats=repeats, alternating_order=True,
                medians={encoding: {name + '_seconds': median(values)
                    for name, values in parts.items()} for encoding, parts in samples.items()}))
    return results


def experiment(tetrahedra, bits=0, mark_count=8, caps=0, repeats=3, literal_cap=200000,
               weight_encoding='moments'):
    raw, primitive = layered_torus(tetrahedra)
    for _ in range(caps):
        raw, primitive = boundary_cap(raw, primitive)
    scale = 1 << bits
    coordinates = [[value * scale for value in row] for row in primitive]
    geometry_seconds, (size, pairs) = timed(
        lambda: normal_arc_pairings(raw, coordinates, boundary=True), repeats)
    if bits:
        candidates = [0, scale - 1, scale, scale + 1, 2 * scale - 1,
                      2 * scale, size // 2, size - 1]
        marks = list(dict.fromkeys(point for point in candidates if 0 <= point < size))
    else:
        marks = [index * size // min(size, mark_count)
                 for index in range(min(size, mark_count))]
    direction = first_half_edge(pairs, marks[0]) if marks else None
    kernel_seconds, answer = timed(lambda: marked_boundary_order(
        size, pairs, marks, start_half_edge=direction, weight_encoding=weight_encoding,
        record_certificate=True), repeats)
    if answer['status'] != 'COMPLETE' or answer['component_count'] != scale:
        raise ArithmeticError('native meridian multiplicity was not recovered')
    replay_seconds, verified = timed(lambda: verify_marked_boundary_certificate(
        size, pairs, marks, answer['certificate'], start_half_edge=direction,
        weight_encoding=weight_encoding), repeats)
    if not verified:
        raise ArithmeticError('independent certificate replay failed')
    native_seconds, native = timed(lambda: normal_marked_boundary_order(
        raw, coordinates, marks, start_half_edge=direction, weight_encoding=weight_encoding,
        record_certificate=True), repeats)
    if native['cycles'] != answer['cycles']:
        raise ArithmeticError('native reconstruction changed the marked order')
    literal_seconds, literal_verified = None, False
    if scale == 1 and marks and size <= literal_cap:
        literal_seconds, literal = timed(lambda: literal_cycle(size, pairs, marks, direction), 1)
        cycle = answer['cycles'][0]
        literal_verified = literal == {key: cycle[key] for key in literal}
        if not literal_verified:
            raise ArithmeticError('literal normal boundary order differs')
    proof = answer['certificate']['weighted_proof']
    record = dict(tetrahedra=len(raw['tetrahedra']), base_tetrahedra=tetrahedra,
                  boundary_caps=caps, scale_bits=bits, points=size,
                  point_bits=size.bit_length(), marks=len(marks), input_pairings=len(pairs),
                  residual_pairings=answer['stats']['residual_pairings'],
                  component_count=answer['component_count'],
                  marked_components=len(answer['cycles']),
                  weight_encoding=weight_encoding,
                  weight_dimension=answer['stats']['weight_dimension'],
                  geometry_seconds=geometry_seconds, kernel_seconds=kernel_seconds,
                  replay_seconds=replay_seconds, native_seconds=native_seconds,
                  literal_seconds=literal_seconds, literal_verified=literal_verified,
                  certificate_bytes=len(json.dumps(json_safe(answer['certificate']),
                                                   separators=(',', ':')).encode()),
                  trace_events=len(proof['orbit_proof']['operations']),
                  weighted_stats=answer['stats']['weighted_stats'])
    print(json.dumps({key: record[key] for key in (
        'tetrahedra', 'scale_bits', 'point_bits', 'marks', 'input_pairings',
        'weight_encoding', 'kernel_seconds', 'replay_seconds', 'literal_seconds')},
        sort_keys=True), flush=True)
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', default='marked_boundary_research/measurements.json')
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--literal-cap', type=int, default=200000)
    options = parser.parse_args()
    rows = []
    for tetrahedra in (4, 8, 12, 16, 20, 22, 24, 32, 48, 64, 96, 128):
        rows.append(experiment(tetrahedra, repeats=options.repeats, literal_cap=options.literal_cap))
    for bits in (64, 1024, 4096, 20000):
        rows.append(experiment(24, bits=bits, repeats=options.repeats,
                               literal_cap=options.literal_cap))
    for caps in (1, 4, 12):
        rows.append(experiment(20, caps=caps, repeats=options.repeats,
                               literal_cap=options.literal_cap))
    for marks in (0, 1, 32, 128):
        rows.append(experiment(64, mark_count=marks, repeats=options.repeats,
                               literal_cap=options.literal_cap))
    # Same native graph and same marks; only the exact endpoint encoding changes.
    # Small controls deliberately include dimensions 1 and 3 below the four-
    # moment dimension; the specialized optimization can cost more there.
    for marks in (0, 1, 8, 32, 128):
        rows.append(experiment(64, mark_count=marks, repeats=options.repeats,
                               literal_cap=options.literal_cap, weight_encoding='one_hot'))
    body = dict(schema='native-marked-boundary-benchmark-v1', repeats=options.repeats,
                statistic='median except a single capped literal walk',
                literal_point_cap=options.literal_cap,
                scope='Supplied normal-boundary reconstruction and marked order; not unknot recognition',
                rows=rows, small_controls=small_controls(),
                environment=dict(python=platform.python_version(), platform=platform.platform()))
    path = Path(options.output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(json_safe(body), indent=2) + '\n')


if __name__ == '__main__':
    main()
