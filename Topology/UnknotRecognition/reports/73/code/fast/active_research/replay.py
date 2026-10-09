"""Replay all saved active-cone and normal-source proofs without an LP solver."""

from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from fastunknot.normal_active_verify import (
    _normal_source, verify_active_cone_certificate, verify_active_normal_certificate,
)


def main():
    source = Path(__file__).with_name('sources.json')
    corpus = json.loads(source.read_text())
    path = Path(__file__).with_name('results')/'audit.json'
    audit = json.loads(path.read_text())
    assert audit['corpus_sha256'] == sha256(source.read_bytes()).hexdigest()
    cases = {case['name']: case for case in corpus['cases']}
    count = positive_pairs = skipped_negative = 0
    for record in audit['paired_support']:
        case = cases[record['name']]
        _, matrix, euler, groups = _normal_source(case['triangulation'], lambda: None)
        anchors = case['anchors'] or [group[0] for group in groups]
        assert anchors == record['anchors']
        forbidden = set(anchors)
        for t in range(record['fixed_prefix']):
            coordinates = case['positive_coordinates']
            selected = next((q for q in range(3)
                             if coordinates and coordinates[t][4+q]), 0)
            forbidden.update(7*t+4+q for q in range(3) if q != selected)
        columns = [j for j in range(len(euler)) if j not in forbidden]
        assert columns == record['columns']
        a = [[row[j] for j in columns] for row in matrix]
        c = [euler[j] for j in columns]
        active = {}
        for algorithm in ('unary', 'batch'):
            result = record[algorithm]
            if 'certificate' in result:
                assert verify_active_cone_certificate(a, c, result['certificate'])
                count += 1
                if result['status'] == 'ACTIVE_POSITIVE':
                    support = [j for j, pair in enumerate(result['certificate']['x'])
                               if Fraction(*pair) > 0]
                    assert support == result['active']
                    active[algorithm] = support
        if record['batch']['status'] == 'SKIPPED_AFTER_NEGATIVE_PRECHECK':
            assert record['unary']['status'] == 'NONPOSITIVE'
            assert record['equivalent'] is True
            skipped_negative += 1
        elif len(active) == 2:
            assert active['unary'] == active['batch']
            assert record['equivalent'] is True
            positive_pairs += 1
    normal_count = 0
    for record in audit['normal_searches']:
        result = record['answer']
        if 'certificate' in result:
            assert verify_active_normal_certificate(
                cases[record['name']]['triangulation'], result['certificate'])
            normal_count += 1
    summary = dict(schema='active-normal-replay-v1',
                   audit_sha256=sha256(path.read_bytes()).hexdigest(),
                   support_certificates_verified=count,
                   equivalent_positive_support_pairs=positive_pairs,
                   negative_precheck_controls=skipped_negative,
                   normal_search_certificates_verified=normal_count,
                   solver_used=False)
    output = path.with_name('replay.json')
    output.write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
