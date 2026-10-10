"""Generate or independently replay the genuine two-gadget composed descent."""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from fastunknot.pachner_causality import compose_disjoint_traces
from fastunknot.pachner_commitments_verify import inspect_pachner_endpoint


FAST = Path(__file__).resolve().parents[1]
SOURCE = 'shared_cover_research/results/exhaustion.json'


def run():
    source_path = FAST/SOURCE
    case = json.loads(source_path.read_text())['cases'][1]
    raw, heights = case['source']['triangulation'], case['source']['heights']
    indices = [5, 32]
    proofs = [case['retained_shared_endpoints'][i] for i in indices]
    result = compose_disjoint_traces(raw, heights, proofs)
    summary = result['summary']
    if (summary['initial_tetrahedra'], summary['final_tetrahedra'],
            summary['upward_moves'], summary['downward_moves']) != (13, 11, 2, 4):
        raise AssertionError('unexpected two-gadget composition counts')
    return dict(schema='pachner-disjoint-composition-audit-v1',
        source_artifact=SOURCE, source_artifact_sha256=sha256(source_path.read_bytes()).hexdigest(),
        source_case=1, endpoint_indices=indices,
        triangulation=raw, heights=heights, input_certificates=proofs,
        composition=result,
        source_sha256={name: sha256((FAST/name).read_bytes()).hexdigest() for name in (
            'fastunknot/pachner_causality.py', 'fastunknot/pachner_commitments_verify.py',
            'causal_research/composition_audit.py')})


def replay(path):
    data = json.loads(Path(path).read_text())
    raw, heights = data['triangulation'], data['heights']
    occupied = set()
    upward = downward = 0
    for proof in data['input_certificates']:
        endpoint = inspect_pachner_endpoint(raw, heights, proof)
        if endpoint is None:
            raise AssertionError('stored input trace failed source replay')
        support = set(endpoint['consumed_initial_tetrahedra'])
        if occupied & support:
            raise AssertionError('stored input traces have overlapping actual supports')
        occupied.update(support)
        upward += endpoint['upward_moves']
        downward += endpoint['downward_moves']
    endpoint = inspect_pachner_endpoint(raw, heights, data['composition']['certificate'])
    if (endpoint is None or endpoint['upward_moves'] != upward
            or endpoint['downward_moves'] != downward
            or endpoint['consumed_initial_tetrahedra'] != sorted(occupied)
            or len(endpoint['triangulation']['tetrahedra']) != len(raw['tetrahedra'])+upward-downward):
        raise AssertionError('stored composed trace failed independent additive replay')
    return dict(input=str(path), accepted=True,
        input_endpoint_replays=len(data['input_certificates']), composed_endpoint_replays=1,
        initial_tetrahedra=len(raw['tetrahedra']),
        final_tetrahedra=len(endpoint['triangulation']['tetrahedra']),
        upward_moves=upward, downward_moves=downward, loss=downward-upward,
        consumed_initial_tetrahedra=sorted(occupied))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--replay')
    arguments = parser.parse_args()
    result = replay(arguments.replay) if arguments.replay else run()
    target = Path(arguments.output)
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(json.dumps(result, indent=2)+'\n')
    print(target)


if __name__ == '__main__':
    main()
