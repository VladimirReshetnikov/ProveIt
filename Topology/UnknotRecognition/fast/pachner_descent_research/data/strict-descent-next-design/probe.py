"""Scratch supplied-source experiments; no maintained file modifications."""
import argparse
from copy import deepcopy
import gzip
from hashlib import sha256
import json
from pathlib import Path
import sys
from unittest.mock import patch

ROOT = Path('/home/codex/.codex/worktrees/cc5b/Proofs/Topology/UnknotRecognition')
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'fast'))
from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_search import recognize_by_crushing, verify_crushing_recognition
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_surface_geometry import _prepare, _coordinates
from fastunknot.normal_pachner32 import reduce_pachner32_once
from fastunknot.boundary_unlayer import unlayer_boundary_once
from fastunknot.normal_euler_transversal import search_euler_transversal
from fastunknot.normal_euler_tree import _EulerMaskOracle
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.pachner_cover_search import find_pachner_descent
from fastunknot.pachner_cover_verify import inspect_pachner_descent

SPECS = {'T25': (2, [1]*5), 'T27': (2, [1]*7), 'W34': (3, [1, -2]*4)}
QUERY = dict(strategy='envelope', candidate_policy='conflicts', max_nodes=256,
    max_pivots=10000, max_anchors=10000, max_hitting_subsets=10000,
    lp_policy='polynomial', lp_fast_path_pivots=None,
    max_ellipsoid_iterations=10000, max_feasibility_calls=10000)
DESCENT = dict(max_upward=1, max_nodes=256, max_regions=10000,
    max_work=200000, max_oracle_states=10000, method='sleep')


def pins():
    return {str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
            for p in sorted((ROOT/'fast/fastunknot').rglob('*.py'))}


def digest(x):
    return sha256(json.dumps(x, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def save(path, x):
    path.write_text(json.dumps(x, sort_keys=True, separators=(',', ':'))+'\n')


def preprocess(name):
    strands, word = SPECS[name]
    diagram = Diagram.from_braid(strands, word)
    options = dict(max_sectors=256, max_bases=10000, max_crushes=None,
        sector_order='diversified', sector_quantum=64, sector_method='transversal',
        max_pivots=10000, max_anchors=10000, lp_strategy='envelope',
        reduce_vertices=True, unlayer_boundary=True, reduce_pachner32=True,
        max_tree_nodes=0, tree_model='source', max_hitting_subsets=10000,
        transversal_candidate_policy='conflicts', lp_policy='polynomial',
        lp_fast_path_pivots=None, max_ellipsoid_iterations=10000,
        max_feasibility_calls=10000)
    result = recognize_by_crushing(diagram, **options)
    assert result['status'] == 'INCONCLUSIVE'
    chain = result['partial_chain']
    assert verify_crushing_chain(diagram, chain)
    assert result['stats']['nodes_attempted'] == result['stats']['lp_calls'] == 0
    source = chain['triangulation'];p = _prepare(source, lambda: None)
    reduction = reduce_pachner32_once(source)
    unlayer = unlayer_boundary_once(source)
    assert reduction['status'] == unlayer['status'] == 'UNCHANGED'
    assert reduction['stats']['scan_complete'] is True and p['vertices'] == 1
    return dict(id=name, braid=dict(strands=strands, word=word),
        input_pd=[list(row) for row in diagram.pd], config=options, result=result,
        source=source, source_sha256=digest(source), vertices=p['vertices'],
        boundary_faces=p['boundary_faces'], pachner32_terminal=reduction,
        unlayer_terminal=unlayer, chain_verified=True)


def query(name):
    previous = json.loads((HERE/(name+'-preprocess.json')).read_bytes())
    source = previous['record']['source']; captures = []
    original = _EulerMaskOracle.attempt

    def capture(self, mask):
        answer = original(self, mask)
        if answer['status'] == 'POSITIVE':
            captures.append(dict(mask=[list(pair) for pair in mask], result=deepcopy(answer)))
        return answer

    with patch.object(_EulerMaskOracle, 'attempt', capture):
        result = search_euler_transversal(source, **QUERY)
    replay = dict(status=result['status'])
    if result['status'] == 'NO_POSITIVE_EULER':
        proof = result['certificate']
        assert proof['allowed_types'] == [[t, q] for t in range(len(source['tetrahedra'])) for q in range(3)]
        assert verify_euler_branch_tree(source, proof)
        split = sorted({node['tetrahedron'] for node in proof['nodes'] if node['kind'] == 'split'})
        assert set(split) <= set(result['resolving_set'])
        replay.update(full_root_negative_verified=True, splitting_set=split,
                      h_upper_bound=len(split))
    elif result['status'] == 'POSITIVE_EULER':
        analysed = _coordinates(_prepare(source, lambda: None), result['coordinates'], lambda: None)
        assert analysed['euler_characteristic'] == result['euler_characteristic'] > 0
        replay['admissible_positive_verified'] = True
    else:
        assert result['status'] == 'INCONCLUSIVE'
        replay['no_negative_claim'] = True
    return dict(id=name, source=source, source_sha256=digest(source), config=QUERY,
        result=result, replay=replay, exposed_positive_points=captures,
        preprocessing_file_sha256=sha256((HERE/(name+'-preprocess.json')).read_bytes()).hexdigest())


def descent(name):
    archived = ROOT/'fast/strict_pachner32_research/data/generation/euler-queries.json.gz'
    data = json.loads(gzip.decompress(archived.read_bytes()))
    selection = {'T8': 0, 'F12': 1, 'TT17': 2}[name]
    source = data['records'][selection]['source']
    heights = [[0]*4 for _ in source['tetrahedra']]
    result = find_pachner_descent(source, heights, **DESCENT)
    replay = dict(status=result['status'])
    if result['status'] == 'DESCENT_FOUND':
        checked = inspect_pachner_descent(source, heights, result['certificate'], max_upward=1)
        assert checked is not None and checked['final_tetrahedra'] < len(source['tetrahedra'])
        assert all(not any(row) for row in checked['heights'])
        replay.update(verified=True, summary=checked)
    else:
        assert result['status'] in ('INCONCLUSIVE', 'COMPLETE_BOUNDED_DESCENT')
        replay['no_knot_verdict'] = True
    return dict(id=name, source=source, source_sha256=digest(source), heights=heights,
        config=DESCENT, result=result, replay=replay,
        historical_source_archive_sha256=sha256(archived.read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('phase', choices=('preprocess', 'query', 'descent'))
    parser.add_argument('name')
    args = parser.parse_args();before = pins()
    output = dict(schema='strict-descent-next-scratch-v1', passed=False,
        phase=args.phase, id=args.name, native_sha256=before,
        script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), record=None)
    path = HERE/(args.name+'-'+args.phase+'.json');save(path, output)
    try:
        output['record'] = globals()[args.phase](args.name)
    except BaseException as error:
        output['unreturned_call'] = dict(error_type=type(error).__name__, message=str(error))
        save(path, output)
        raise
    assert pins() == before
    output['passed'] = True;save(path, output)
    r = output['record']
    print(json.dumps(dict(id=args.name, phase=args.phase, passed=True,
        tetrahedra=len(r['source']['tetrahedra']), status=r['result']['status'],
        stats=r['result']['stats'], replay=r.get('replay'))), flush=True)


if __name__ == '__main__':
    main()
