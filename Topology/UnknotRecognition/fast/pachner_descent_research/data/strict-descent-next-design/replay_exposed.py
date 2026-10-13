"""Original STANDARD replay of already exposed rays; no discovery calls."""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
sys.path.insert(0, str(ROOT/'fast'))
from conflict_composition_research.standard import observation


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('name')
    args = parser.parse_args()
    path = HERE/(args.name+'-query.json');raw = path.read_bytes()
    data = json.loads(raw);record = data['record'];source = record['source']
    assert data['passed'] is True
    pins = {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
            for p in sorted((ROOT/'fast/fastunknot').rglob('*.py'))}
    representatives = {}
    for index, point in enumerate(record['exposed_positive_points']):
        rows = point['result']['coordinates']
        key = json.dumps(rows, sort_keys=True, separators=(',', ':'))
        representatives.setdefault(key, (index, point))
    checked = []
    for index, point in representatives.values():
        rows = point['result']['coordinates']
        result, rank = observation(source, rows)
        assert result['canonical_euler'] == point['result']['euler_characteristic'] > 0
        assert result['conflicts'] == point['result']['conflicts']
        assert result['conflicts']
        checked.append(dict(captured_index=index, coordinates=rows, observation=result, rank=rank))
    edges = [set(r['observation']['conflicts']) for r in checked]
    tested = []; total = 0; exhausted_through = -1
    witness = None
    for k in range(len(source['tetrahedra'])+1):
        count = 0
        limited = False
        for B in combinations(range(len(source['tetrahedra'])), k):
            if total == 10000:
                limited = True
                break
            count += 1
            total += 1
            if all(set(B).intersection(edge) for edge in edges):
                witness = list(B)
                break
        exhausted = witness is None and not limited
        if exhausted:
            exhausted_through = k
        tested.append(dict(size=k, subsets_tested=count, exhausted=exhausted))
        if witness is not None or limited:
            break
    tau = len(witness) if witness is not None else None
    lower = exhausted_through+1
    output = dict(passed=True, source_sha256=record['source_sha256'], native_sha256=pins,
        query_sha256=sha256(raw).hexdigest(), script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
        standard_checker_sha256=sha256((ROOT/'fast/conflict_composition_research/standard.py').read_bytes()).hexdigest(),
        original_matching_replayed=True, unique_exposed_rays=checked,
        retained_hypergraph_tau=tau, retained_hypergraph_hitting_set=witness,
        global_h_lower_bound=lower, combination_counts=tested, max_hitting_subsets=10000,
        discovery_used=False, global_h_upper_bound=record['replay'].get('h_upper_bound'),
        exact_h=(lower if record['replay'].get('h_upper_bound') == lower else None))
    assert pins == {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
                    for p in sorted((ROOT/'fast/fastunknot').rglob('*.py'))}
    (HERE/(args.name+'-exposed-replay.json')).write_text(json.dumps(output,sort_keys=True,separators=(',', ':'))+'\n')
    print(json.dumps({k:output[k] for k in ('passed','retained_hypergraph_tau','global_h_lower_bound','global_h_upper_bound','exact_h','combination_counts')}))


if __name__ == '__main__':
    main()
