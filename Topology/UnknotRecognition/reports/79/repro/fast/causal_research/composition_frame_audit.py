"""Audit noncanonical down frames after a nonempty disjoint trace.

The fixed source has two disjoint three-event descents.  This audit changes
both downward formal frames in the second trace, then composes it after the
first trace has changed the row positions.  The twelve paired frame choices
exercise every belt/apex permutation in each position; they are a focused
interaction check, not all 144 possible pairs.  Inputs are obtained from
fixed certificates by explicit relabeling, without a move or search producer.

Run from any working directory; default paths are relative to this file.
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

from causal_research.frame_audit import reframe_down, transport_down_source_frame
from fastunknot.pachner_causality import compose_disjoint_traces
from fastunknot.pachner_commitments_verify import inspect_pachner_endpoint


def _require(condition, message):
    if not condition:
        raise AssertionError(message)


def audit_composition_frames(fixture_path):
    fixture_bytes = fixture_path.read_bytes()
    fixture = json.loads(fixture_bytes)
    raw, heights = fixture['triangulation'], fixture['heights']
    left, right = fixture['certificates']
    _require(len(raw['tetrahedra']) == 13, 'the fixed source must have thirteen cells')
    for proof, support in ((left, list(range(1, 7))), (right, list(range(7, 13)))):
        endpoint = inspect_pachner_endpoint(raw, heights, proof)
        _require(endpoint is not None, 'a fixed source trace failed independent replay')
        _require((endpoint['upward_moves'], endpoint['downward_moves']) == (1, 2),
                 'each fixed trace must contain one upward and two downward events')
        _require(endpoint['consumed_initial_tetrahedra'] == support,
                 'the fixture must have the two declared disjoint actual footprints')

    frames = [list(belt) + list(apices)
              for belt, apices in product(permutations(range(3)),
                                          permutations((3, 4)))]
    tested = []
    for index, first_frame in enumerate(frames):
        last_frame = frames[-1-index]
        altered = deepcopy(right)
        second, row_map, vertex_maps = reframe_down(altered['moves'][1], first_frame)
        third = transport_down_source_frame(altered['moves'][2], row_map, vertex_maps)
        third, _, _ = reframe_down(third, last_frame)
        altered['moves'] = [altered['moves'][0], second, third]
        altered['coordinates'] = third['transport']['coordinates']
        altered['disc_certificate'] = None
        marker = (first_frame, last_frame)
        _require(inspect_pachner_endpoint(raw, heights, altered) is not None,
                 ('a relabeled source trace did not independently verify', marker))

        composed = compose_disjoint_traces(raw, heights, [left, altered])
        endpoint = inspect_pachner_endpoint(raw, heights, composed['certificate'])
        _require(endpoint is not None, ('a composed endpoint failed replay', marker))
        summary = composed['summary']
        _require((summary['upward_moves'], summary['downward_moves'],
                  summary['final_tetrahedra'], summary['loss']) == (2, 4, 11, 2),
                 ('the additive event census changed', marker))
        _require(summary['consumed_initial_tetrahedra'] == list(range(1, 13)),
                 ('the actual footprint union changed', marker))
        _require(composed['replayed_events'] == [[i, j] for i in range(2) for j in range(3)],
                 ('private event namespaces were not preserved', marker))
        tested.append(dict(first_down_frame=first_frame, last_down_frame=last_frame))

    _require(len(tested) == 12, 'all twelve paired frame choices are required')
    return dict(schema='pachner-disjoint-frame-audit-v1',
        fixture=fixture_path.name, fixture_sha256=sha256(fixture_bytes).hexdigest(),
        initial_tetrahedra=13, final_tetrahedra=11, upward_moves=2, downward_moves=4,
        consumed_initial_tetrahedra=list(range(1, 13)),
        paired_frame_cases=12, second_trace_follows_nonempty_first_trace=True,
        all_relabeled_inputs_independently_verified=True,
        all_composed_outputs_independently_verified=True,
        all_additive_counts_and_event_namespaces_verified=True,
        tested_frame_pairs=tested,
        input_generation='fixed certificates and explicit isomorphism conjugation')


def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument('--fixture', type=Path,
                        default=DIRECTORY / 'data' / 'disjoint_descents.json')
    parser.add_argument('--output', type=Path,
                        default=DIRECTORY / 'results' / 'composition_frame_audit.json')
    arguments = parser.parse_args()
    result = audit_composition_frames(arguments.fixture)
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
