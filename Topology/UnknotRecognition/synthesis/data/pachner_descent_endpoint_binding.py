"""Bind fresh returned sources to the exact staged h-evidence sources.

Run alongside pachner_descent_research.check_evidence: that checker independently
replays the full native proofs; this additional check compares all twelve
noncircle endpoint tables and validates their finite one-vertex geometry.
It performs no search, LP, or timing. Historical pins remain historical.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
sys.path.insert(0, str(ROOT/'fast'))
from fastunknot.normal_surface_geometry import _prepare
from pachner_descent_research.common import ARMS, cases, configs, digest, load_archive, source_hashes


def _same(actual, expected):
    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        return actual.keys() == expected.keys() and all(_same(actual[k], v) for k, v in expected.items())
    if type(expected) in (list, tuple):
        return len(actual) == len(expected) and all(_same(a, b) for a, b in zip(actual, expected))
    return actual == expected


def _endpoint(result):
    assert type(result) is dict and type(result['status']) is str
    if result['status'] == 'INCONCLUSIVE':
        assert set(result) == {'status', 'reason', 'stats', 'partial_chain'}
        chain = result['partial_chain']
        assert chain['status'] == 'REDUCED'
    else:
        assert result['status'] == 'KNOTTED'
        assert set(result) == {'status', 'certificate', 'stats'}
        assert result['certificate']['status'] == 'KNOTTED'
        chain = result['certificate']['chain']
    source = chain['triangulation']
    assert type(source) is dict and source['tetrahedra']
    return source


def check_endpoint_bindings(audit):
    """Check endpoint identity, not a substitute for full native proof replay."""
    assert __debug__, 'endpoint binding requires assertions enabled'
    pins = source_hashes()
    assert audit['schema'] == 'pachner-descent-audit-v1' and audit['passed'] is True
    assert _same(audit['source_sha256'], pins)
    assert _same(audit['config'], {arm: configs(arm) for arm in ARMS})
    assert _same(audit['coverage'], dict(ordinary_calls_expected=14, ordinary_calls_completed=14))
    assert audit['failures'] == audit['unreturned_calls'] == [] and audit['active_call'] is None
    definitions = cases()
    assert _same(audit['case_order'], [case['id'] for case in definitions])
    assert type(audit['records']) is list and len(audit['records']) == len(definitions) == 7
    staged, staged_bytes = load_archive('fixed-u1-staged-audit', 'audit.json')
    assert staged['passed'] is True and type(staged['calls_completed']) is int and staged['calls_completed'] == 20
    assert staged['failures'] == staged['unreturned_calls'] == [] and staged['active_call'] is None
    assert [r['id'] for r in staged['records']] == ['T', 'F', 'TT', 'T25', 'T27', 'W34']
    staged_map = {{'T': 'trefoil', 'F': 'figure_eight'}.get(r['id'], r['id']): r for r in staged['records']}
    bindings = []
    for fresh, case in zip(audit['records'], definitions):
        assert all(_same(fresh[key], value) for key, value in case.items())
        assert fresh['input_pd_sha256'] == digest(case['input_pd'])
        assert set(fresh['arms']) == set(ARMS)
        if case['id'] == 'circle':
            continue
        old = staged_map[case['id']]
        assert _same(old['input_pd'], case['input_pd']) and _same(old['braid'], case['braid'])
        assert set(old['preprocessing']) == set(ARMS)
        for arm in ARMS:
            entry = fresh['arms'][arm]
            assert set(entry) == {'result', 'replay'}
            historical = old['preprocessing'][arm]
            assert _same(historical['config'], dict(configs(arm), max_tree_nodes=0))
            assert historical['result']['status'] == 'INCONCLUSIVE'
            source, expected = _endpoint(entry['result']), _endpoint(historical['result'])
            assert _same(source, expected), (case['id'], arm, 'fresh/staged endpoint differs')
            prepared = _prepare(source, lambda: None)
            assert prepared['vertices'] == 1 and len(prepared['boundary_faces']) == 2
            bindings.append(dict(id=case['id'], arm=arm, source_sha256=digest(source),
                tetrahedra=len(source['tetrahedra']), vertices=1, boundary_faces=2,
                exact_typed_equality=True))
    assert len(bindings) == 12 and source_hashes() == pins
    return dict(passed=True, endpoint_bindings=12, source_sha256=pins,
        staged_audit_sha256=sha256(staged_bytes).hexdigest(), records=bindings,
        discovery_used=False, native_proof_replay_scope='Separate package checker replays every complete/partial native proof.',
        scope='Exact fresh/staged labelled-source identity; no transport of h between different sources.',
        general_quasipolynomial=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, default=DATA/'pachner-descent-audit.json')
    parser.add_argument('--output', type=Path, default=DATA/'pachner-descent-endpoint-bindings.json')
    args = parser.parse_args()
    raw = args.audit.read_bytes()
    result = check_endpoint_bindings(json.loads(raw))
    result.update(audit_sha256=sha256(raw).hexdigest(), script_sha256=sha256(Path(__file__).read_bytes()).hexdigest())
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n')
    print(json.dumps(dict(passed=True, endpoint_bindings=result['endpoint_bindings'], discovery_used=False), sort_keys=True))


if __name__ == '__main__':
    main()
