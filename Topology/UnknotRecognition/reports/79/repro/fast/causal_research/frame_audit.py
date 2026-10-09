"""Audit every formal frame on two dependent 3--2 steps of a genuine descent.

Run this file from any working directory.  Its default fixture and result
paths are relative to this file, not to the invocation directory.  The
fixture is an independently checked three-event trace in a finite solid
torus: one upward move, followed by two dependent downward moves.

The 144 input variants are constructed by explicit cell and vertex
renaming of the fixed certificates.  No move or search producer constructs
the audit inputs.  The maintained independent endpoint checker accepts
each input, then checks the extracted output.  Exact endpoint geometry and
normalized marking are compared as well.
"""
from argparse import ArgumentParser
from copy import deepcopy
from hashlib import sha256
from itertools import permutations, product
import json
from pathlib import Path
import sys


DIRECTORY = Path(__file__).resolve().parent
FAST = DIRECTORY.parent
if str(FAST) not in sys.path:
    sys.path.insert(0, str(FAST))

from fastunknot.pachner_causality import extract_local_descent
from fastunknot.pachner_commitments_verify import inspect_pachner_endpoint


_DOWN_OUTPUTS = ((0, 1, 2, 3), (0, 1, 2, 4))


def _require(condition, message):
    if not condition:
        raise AssertionError(message)


def _rename_triangulation(raw, row_map, vertex_maps):
    """Conjugate every attaching permutation by explicit local renamings."""
    rows = [[None] * 4 for _ in raw['tetrahedra']]
    for old_row, faces in enumerate(raw['tetrahedra']):
        local = vertex_maps[old_row]
        inverse = [local.index(vertex) for vertex in range(4)]
        for old_face, entry in enumerate(faces):
            if entry is None:
                continue
            partner = entry['tetrahedron']
            gluing = entry['permutation']
            rows[row_map[old_row]][local[old_face]] = dict(
                tetrahedron=row_map[partner],
                permutation=[vertex_maps[partner][gluing[inverse[vertex]]]
                             for vertex in range(4)])
    return dict(tetrahedra=rows)


def _rename_heights(heights, row_map, vertex_maps):
    rows = [None] * len(heights)
    for old_row, heights_row in enumerate(heights):
        renamed = [0] * 4
        for vertex, value in enumerate(heights_row):
            renamed[vertex_maps[old_row][vertex]] = value
        rows[row_map[old_row]] = [value - renamed[0] for value in renamed]
    return rows


def _coherent_coordinates(heights):
    """Count the constant normal type on every interval between vertex levels."""
    quadrilateral = {
        frozenset((0, 1)): 4,
        frozenset((0, 2)): 5,
        frozenset((0, 3)): 6,
    }
    result = []
    for row in heights:
        coordinates = [0] * 7
        levels = sorted(set(row))
        for lower, upper in zip(levels, levels[1:]):
            low = frozenset(vertex for vertex in range(4) if row[vertex] <= lower)
            if len(low) == 1:
                coordinate = next(iter(low))
            elif len(low) == 3:
                coordinate = next(vertex for vertex in range(4) if vertex not in low)
            else:
                pair = low if 0 in low else frozenset(range(4)) - low
                coordinate = quadrilateral[pair]
            coordinates[coordinate] += upper - lower
        result.append(coordinates)
    return result


def _renamed_step(step, move, row_map, vertex_maps, five=None):
    transport = deepcopy(step['transport'])
    transport['move'] = move
    heights = _rename_heights(transport['heights'], row_map, vertex_maps)
    transport['heights'] = heights
    transport['coordinates'] = _coherent_coordinates(heights)
    if five is not None:
        transport['bipyramid_heights'] = five
    # The Euler and normal-disc jumps are invariant under these isomorphisms.
    return dict(triangulation=_rename_triangulation(
                    step['triangulation'], row_map, vertex_maps),
                transport=transport)


def reframe_down(step, formal_permutation):
    """Change a down move's formal labels and its two output local frames."""
    move = deepcopy(step['transport']['move'])
    _require(move['schema'] == 'pachner-32-v1', 'a downward step is required')
    for item in move['region']:
        item['vertices'] = [formal_permutation[label] for label in item['vertices']]

    count = len(step['triangulation']['tetrahedra'])
    start = count - 2
    row_map = list(range(count))
    vertex_maps = [list(range(4)) for _ in range(count)]
    for slot, labels in enumerate(_DOWN_OUTPUTS):
        changed = tuple(formal_permutation[label] for label in labels)
        target = next(index for index, output in enumerate(_DOWN_OUTPUTS)
                      if set(output) == set(changed))
        row_map[start + slot] = start + target
        vertex_maps[start + slot] = [_DOWN_OUTPUTS[target].index(label)
                                    for label in changed]

    old_five = step['transport']['bipyramid_heights']
    inverse = [formal_permutation.index(label) for label in range(5)]
    offset = old_five[inverse[0]]
    five = [old_five[inverse[label]] - offset for label in range(5)]
    return (_renamed_step(step, move, row_map, vertex_maps, five),
            row_map, vertex_maps)


def transport_down_source_frame(step, source_rows, source_vertices):
    """Transport a later down certificate through a renaming of its input.

    The declared formal labels stay fixed.  Survivor cells inherit the input
    renaming, while this move's two outputs keep their standard declared
    frames.  This construction uses only the supplied certificate data.
    """
    old_move = step['transport']['move']
    _require(old_move['schema'] == 'pachner-32-v1', 'a downward step is required')
    old_selected = {item['tetrahedron'] for item in old_move['region']}
    region = []
    for item in old_move['region']:
        old_row = item['tetrahedron']
        labels = [None] * 4
        for vertex, label in enumerate(item['vertices']):
            labels[source_vertices[old_row][vertex]] = label
        region.append(dict(tetrahedron=source_rows[old_row], vertices=labels))
    move = dict(schema='pachner-32-v1',
                region=sorted(region, key=lambda item: item['tetrahedron']))

    source_count = len(source_rows)
    old_survivors = [row for row in range(source_count) if row not in old_selected]
    new_selected = {source_rows[row] for row in old_selected}
    new_survivors = [row for row in range(source_count) if row not in new_selected]
    positions = {row: index for index, row in enumerate(new_survivors)}
    count = source_count - 1
    row_map = list(range(count))
    vertex_maps = [list(range(4)) for _ in range(count)]
    for old_output, old_source in enumerate(old_survivors):
        row_map[old_output] = positions[source_rows[old_source]]
        vertex_maps[old_output] = source_vertices[old_source]
    return _renamed_step(step, move, row_map, vertex_maps)


def audit_frames(fixture_path):
    """Independently validate and extract all 12-by-12 formal-frame variants."""
    fixture_bytes = fixture_path.read_bytes()
    fixture = json.loads(fixture_bytes)
    raw, heights, proof = (fixture[key] for key in
                            ('triangulation', 'heights', 'certificate'))
    baseline = inspect_pachner_endpoint(raw, heights, proof)
    _require(baseline is not None, 'the fixed source trace did not verify')
    _require((baseline['upward_moves'], baseline['downward_moves']) == (1, 2),
             'the fixture must have one up and two down events')
    _require(len(proof['moves']) == 3, 'the fixed source must have three events')

    first = deepcopy(proof['moves'][0])
    frames = [list(belt) + list(apices)
              for belt, apices in product(permutations(range(3)),
                                          permutations((3, 4)))]
    combinations_checked = child_seeded_last_moves = 0
    for first_frame in frames:
        second, row_map, vertex_maps = reframe_down(proof['moves'][1], first_frame)
        third_in_new_source = transport_down_source_frame(
            proof['moves'][2], row_map, vertex_maps)
        for last_frame in frames:
            third, _, _ = reframe_down(third_in_new_source, last_frame)
            changed = deepcopy(proof)
            changed['moves'] = [first, second, third]
            changed['coordinates'] = third['transport']['coordinates']
            changed['disc_certificate'] = None
            marker = (first_frame, last_frame)
            accepted = inspect_pachner_endpoint(raw, heights, changed)
            _require(accepted is not None, ('input frame did not verify', marker))

            seed = next(item for item in third['transport']['move']['region']
                        if 2 not in item['vertices'])
            prior_count = len(second['triangulation']['tetrahedra'])
            child_seeded_last_moves += seed['tetrahedron'] >= prior_count - 2

            extracted = extract_local_descent(raw, heights, changed)
            _require(extracted['selected_events'] == [0, 1, 2],
                     ('the full dependent first descent should be retained', marker))
            observed = inspect_pachner_endpoint(raw, heights, extracted['certificate'])
            _require(observed is not None, ('extracted output did not verify', marker))
            _require(observed['triangulation'] == accepted['triangulation'],
                     ('exact output frame differs', marker))
            _require(observed['heights'] == accepted['heights'],
                     ('normalized output marking differs', marker))
            _require(observed['coordinates'] == accepted['coordinates'],
                     ('coherent output coordinates differ', marker))
            combinations_checked += 1

    _require(combinations_checked == 144, 'the full product of formal frames is required')
    _require(child_seeded_last_moves == 48, 'all child-seeded frame choices are required')
    return dict(schema='pachner-causal-frame-audit-v1',
                fixture=fixture_path.name, fixture_sha256=sha256(fixture_bytes).hexdigest(),
                initial_tetrahedra=len(raw['tetrahedra']),
                final_tetrahedra=len(baseline['triangulation']['tetrahedra']),
                upward_moves=1, downward_moves=2, belt_permutations=6,
                apex_permutations=2, dependent_down_steps=2,
                valid_frame_combinations=combinations_checked,
                child_seeded_last_moves=child_seeded_last_moves,
                independently_verified_inputs=combinations_checked,
                independently_verified_outputs=combinations_checked,
                all_exact_final_frames_equal=True,
                all_exact_final_markings_equal=True,
                input_generation='fixed certificates and explicit isomorphism conjugation')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', type=Path,
                        default=DIRECTORY / 'data' / 'dependent_descent.json')
    parser.add_argument('--output', type=Path,
                        default=DIRECTORY / 'results' / 'frame_audit.json')
    arguments = parser.parse_args()
    result = audit_frames(arguments.fixture)
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
