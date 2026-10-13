"""Independent replay of whole calls, historical source proofs and saved timings.

No discovery is called. Counters are validated as recorded bounds and against
retained moves, not as independently reconstructed solver operation traces.
Historical generation pins are retained without asserting current freshness.
"""
import argparse
import gzip
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path
from statistics import median

from fastunknot.diagram import Diagram
from fastunknot.normal_crushing_chain import verify_crushing_chain
from fastunknot.normal_crushing_search import verify_crushing_recognition
from fastunknot.normal_euler_tree_verify import verify_euler_branch_tree
from fastunknot.normal_pachner_descent_verify import verify_normal_pachner_descent
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.pachner_cover_verify import inspect_pachner_descent
from conflict_composition_research.standard import observation
from strict_pachner32_research.check_evidence import check_archive as check_strict32_archive
from strict_pachner32_research.check_evidence import _archive_files as strict32_archive_files
from strict_pachner32_research.check_evidence import _candidates
from .common import (ARMS, BENCHMARK_PROTOCOL, CAP_STATS, MAX_STATS, PACKAGE,
                     canonical_bytes, cases, configs, digest, source_hashes)

def _same(actual, expected):
    if type(actual) is not type(expected):
        return False
    if type(expected) is dict:
        return actual.keys() == expected.keys() and all(_same(actual[k], v) for k, v in expected.items())
    if type(expected) in (list, tuple):
        return len(actual) == len(expected) and all(_same(a, b) for a, b in zip(actual, expected))
    return actual == expected



def _statistics(stats, options):
    assert type(stats) is dict
    assert all(type(k) is str and type(v) is int and v >= 0 for k, v in stats.items())
    assert all(k in MAX_STATS for k in stats if k.startswith(('maximum_', 'peak_', 'max_')))
    enabled = options.get('reduce_pachner_descent', False)
    for cap, fields in CAP_STATS.items():
        required = [f for f in fields if f != 'pachner_descent_macros' or enabled]
        assert all(f in stats for f in required)
        limit = options[cap]
        assert limit is None or type(limit) is int and limit >= 0
        assert limit is None or sum(stats.get(f, 0) for f in fields) <= limit
    assert {'pachner32_calls', 'pachner32_candidates', 'pachner32_moves'} <= stats.keys()
    assert stats['pachner32_moves'] <= stats['pachner32_calls'] <= stats['stages']
    assert stats['pachner32_candidates'] >= stats['pachner32_moves']
    fields = {'pachner_descent_calls', 'pachner_descent_nodes', 'pachner_descent_work',
              'pachner_descent_macros', 'pachner_descent_upward_moves', 'pachner_descent_downward_moves'}
    supplied = {k for k in stats if k.startswith('pachner_descent_')}
    if enabled:
        assert supplied == fields
        assert stats['pachner_descent_macros'] <= stats['pachner_descent_calls'] <= stats['stages']
        assert stats['pachner_descent_upward_moves'] <= stats['pachner_descent_macros']
        assert stats['pachner_descent_downward_moves'] == stats['pachner_descent_macros']+stats['pachner_descent_upward_moves']
    else:
        assert not supplied


def _driver_replay(diagram, result, options):
    """Shared proof checks; caller separately binds the historical/fresh config."""
    diagram = Diagram.from_pd(diagram.pd)
    assert type(result) is dict and type(result['status']) is str
    assert result['status'] in ('UNKNOT', 'KNOTTED', 'INCONCLUSIVE')
    stats = result['stats']
    _statistics(stats, options)
    assert not any(k.startswith('factors_') for k in stats)
    if result['status'] == 'INCONCLUSIVE':
        assert set(result) == {'status', 'reason', 'stats', 'partial_chain'}
        assert type(result['reason']) is str and result['reason']
        chain = result['partial_chain']
        assert chain['status'] == 'REDUCED' and verify_crushing_chain(diagram, chain)
    else:
        assert set(result) == {'status', 'certificate', 'stats'}
        packet = result['certificate']
        assert packet['status'] == result['status'] and verify_crushing_recognition(diagram, packet)
        chain = packet['chain']
    assert chain['schema'] == ('diagram-crushing-v4' if options.get('reduce_pachner_descent', False) else 'diagram-crushing-v3')
    initial = chain['source_triangulation']
    shelled = initial if chain['shelling'] is None else chain['shelling']['triangulation']
    assert stats['initial_tetrahedra'] == len(initial['tetrahedra'])
    assert stats['shelled_tetrahedra'] == len(shelled['tetrahedra'])
    schemas = {'normal-ray-crushing-v1': 'crushing_steps',
               'normal-boundary-unlayer-v1': 'boundary_unlayerings',
               'normal-pachner-32-v1': 'pachner32_moves',
               'normal-pachner-descent-v1': 'pachner_descent_macros'}
    counts = {field: 0 for field in schemas.values()}
    up = down = 0
    for step in chain['steps']:
        assert step['schema'] in schemas
        counts[schemas[step['schema']]] += 1
        if step['schema'] == 'normal-pachner-descent-v1':
            for move in step['certificate']['moves']:
                kind = move['transport']['move']['schema']
                assert kind in ('pachner-23-v1', 'pachner-32-v1')
                up += kind == 'pachner-23-v1'
                down += kind == 'pachner-32-v1'
    assert all(stats.get(field, 0) == count for field, count in counts.items())
    assert stats.get('pachner_descent_upward_moves', 0) == up
    assert stats.get('pachner_descent_downward_moves', 0) == down
    assert stats['vertex_reduction_crushes'] <= counts['crushing_steps']
    assert stats['stages'] == len(chain['steps'])+int(chain['triangulation'] is not None)
    return dict(status=result['status'], proof_verified=result['status'] != 'INCONCLUSIVE',
        partial_chain_verified=result['status'] == 'INCONCLUSIVE', returned_work_complete=True,
        **counts, elementary_macro_upward_moves=up, elementary_macro_downward_moves=down,
        final_tetrahedra=None if chain['triangulation'] is None else len(chain['triangulation']['tetrahedra']))


def replay_result(diagram, arm, result, options):
    assert __debug__, 'research replay requires assertions enabled'
    assert arm in ARMS and _same(options, configs(arm))
    return _driver_replay(diagram, result, options)


def _chain(result):
    return result['partial_chain'] if result['status'] == 'INCONCLUSIVE' else result['certificate']['chain']


def _archives():
    """Independently bind every stored byte and every original manifest entry."""
    manifest = json.loads((PACKAGE/'data/manifest.json').read_bytes())
    assert manifest['schema'] == 'pachner-descent-archives-v1'
    assert set(manifest['groups']) == {'strict-descent-next-design', 'fixed-u1-staged-audit'}
    result = {}
    for group, entry in manifest['groups'].items():
        assert set(entry) == {'files', 'original_location', 'original_manifest'}
        files = {}
        for name, spec in dict(entry['files'], **{'manifest.json': entry['original_manifest']}).items():
            assert type(name) is str and Path(name).name == name
            assert set(spec) == {'encoding', 'path', 'raw_bytes', 'raw_sha256', 'stored_bytes', 'stored_sha256'}
            path = Path(spec['path'])
            assert not path.is_absolute() and '..' not in path.parts and path.parts[:2] == ('data', group)
            stored = (PACKAGE/path).read_bytes()
            assert type(spec['stored_bytes']) is int and len(stored) == spec['stored_bytes']
            assert sha256(stored).hexdigest() == spec['stored_sha256']
            assert spec['encoding'] in ('identity', 'gzip')
            raw = gzip.decompress(stored) if spec['encoding'] == 'gzip' else stored
            assert type(spec['raw_bytes']) is int and len(raw) == spec['raw_bytes']
            assert sha256(raw).hexdigest() == spec['raw_sha256']
            files[name] = raw
        original = json.loads(files['manifest.json'])
        assert _same(original['files_sha256'], {name: sha256(raw).hexdigest()
                     for name, raw in files.items() if name != 'manifest.json'})
        result[group] = files
    return result


def _query_config():
    return dict(candidate_policy='conflicts', lp_fast_path_pivots=None, lp_policy='polynomial',
        max_anchors=10000, max_ellipsoid_iterations=10000, max_feasibility_calls=10000,
        max_hitting_subsets=10000, max_nodes=256, max_pivots=10000, strategy='envelope')


def _query_replay(source, query):
    assert _same(query['config'], _query_config()) and query['source_sha256'] == digest(source)
    assert _same(query['source'], source)
    result = query['result']
    assert type(result) is dict and type(result['stats']) is dict
    assert all(type(k) is str and type(v) is int and v >= 0 for k, v in result['stats'].items())
    cap_fields = {'max_nodes': 'nodes_attempted', 'max_pivots': 'lp_pivots',
        'max_anchors': 'anchors_tested', 'max_hitting_subsets': 'hitting_subsets_tested',
        'max_ellipsoid_iterations': 'lp_ellipsoid_iterations', 'max_feasibility_calls': 'lp_feasibility_calls'}
    for cap, field in cap_fields.items():
        assert result['stats'][field] <= query['config'][cap]
    if result['status'] == 'NO_POSITIVE_EULER':
        assert set(result) == {'status', 'certificate', 'resolving_set', 'stats'}
        proof = result['certificate']
        assert _same(proof['allowed_types'], [[t, q] for t in range(len(source['tetrahedra'])) for q in range(3)])
        assert verify_euler_branch_tree(source, proof)
        split = sorted({node['tetrahedron'] for node in proof['nodes'] if node['kind'] == 'split'})
        assert _same(result['resolving_set'], split)
        assert _same(query['replay'], dict(status='NO_POSITIVE_EULER', full_root_negative_verified=True,
                                          h_upper_bound=len(split), splitting_set=split))
        return len(split), split
    assert result['status'] == 'INCONCLUSIVE' and set(result) == {'status', 'stats', 'reason'}
    assert type(result['reason']) is str and result['reason']
    assert _same(query['replay'], dict(status='INCONCLUSIVE', no_negative_claim=True))
    return None, None


def _exposed_rays(source, points):
    """Replay every exposed payload and ORIGINAL STANDARD rank for every unique ray."""
    assert type(points) is list
    n = len(source['tetrahedra'])
    records, seen = [], {}
    for index, point in enumerate(points):
        assert type(point) is dict and set(point) == {'mask', 'result'}
        mask = point['mask']
        assert type(mask) is list
        assert all(type(pair) is list and len(pair) == 2 and all(type(x) is int for x in pair)
                   and 0 <= pair[0] < n and 0 <= pair[1] < 3 for pair in mask)
        assert mask == sorted(mask) and len({tuple(pair) for pair in mask}) == len(mask)
        result = point['result']
        assert type(result) is dict and set(result) == {'status', 'coordinates', 'conflicts', 'euler_characteristic'}
        assert result['status'] == 'POSITIVE'
        rows = result['coordinates']
        key = digest(rows)
        if key not in seen:
            obs, rank = observation(source, rows)
            seen[key] = obs, rank
            records.append(dict(captured_index=index, coordinates=rows, observation=obs, rank=rank))
        obs, rank = seen[key]
        assert type(result['euler_characteristic']) is int and result['euler_characteristic'] == obs['canonical_euler'] > 0
        assert _same(result['conflicts'], obs['conflicts']) and obs['conflicts']
        assert all([t, q] in mask for t, row in enumerate(rows) for q in range(3) if row[4+q])
    return records


def _hitting(n, rays, limit=10000):
    edges = [set(ray['observation']['conflicts']) for ray in rays]
    tested, witness, lower, total = [], None, 0, 0
    for size in range(n+1):
        count, exhausted = 0, True
        for subset in combinations(range(n), size):
            if total == limit:
                exhausted = False
                break
            count += 1
            total += 1
            if all(set(subset) & edge for edge in edges):
                witness, exhausted = list(subset), False
                break
        if exhausted:
            lower = size+1
        tested.append(dict(size=size, subsets_tested=count, exhausted=exhausted))
        if witness is not None or not exhausted:
            break
    return dict(retained_hypergraph_tau=None if witness is None else len(witness),
        retained_hypergraph_hitting_set=witness, combination_counts=tested,
        global_h_lower_bound=lower)


def _old_archives(files, strict32):
    original_pins = None
    expected_cases = {c['id']: c for c in cases()}
    def load(name):
        nonlocal original_pins
        data = json.loads(files[name+'.json'])
        assert data['passed'] is True
        if original_pins is None:
            original_pins = data['native_sha256']
        assert _same(data['native_sha256'], original_pins)
        assert data['script_sha256'] == sha256(files['probe.py']).hexdigest()
        return data['record']
    prime = []
    for name in ('T25', 'T27', 'W34'):
        prep, query = load(name+'-preprocess'), load(name+'-query')
        case = expected_cases[name]
        assert _same(prep['braid'], case['braid']) and _same(prep['input_pd'], case['input_pd'])
        assert prep['id'] == query['id'] == name
        options = dict(configs('baseline'), max_tree_nodes=0)
        del options['reduce_pachner_descent']
        assert _same(prep['config'], options)
        replay = _driver_replay(Diagram.from_pd(case['input_pd']), prep['result'], options)
        assert replay['status'] == 'INCONCLUSIVE' and prep['chain_verified'] is True
        assert prep['result']['stats']['lp_calls'] == prep['result']['stats']['nodes_attempted'] == 0
        source = _chain(prep['result'])['triangulation']
        assert _same(prep['source'], source) and prep['source_sha256'] == digest(source)
        assert query['preprocessing_file_sha256'] == sha256(files[name+'-preprocess.json']).hexdigest()
        p, candidates = _candidates(source)
        assert _same(prep['vertices'], 1) and p['vertices'] == 1 and not candidates
        assert _same(prep['boundary_faces'], [list(f) for f in p['boundary_faces']])
        # These retained sources have distinct boundary tetrahedra: no collar candidate.
        assert len(p['boundary_faces']) == 2 and p['boundary_faces'][0][0] != p['boundary_faces'][1][0]
        n = len(source['tetrahedra'])
        assert _same(prep['pachner32_terminal'], dict(status='UNCHANGED', reason='no eligible interior edge',
            stats=dict(candidate_tests=0, initial_tetrahedra=n, remaining_tetrahedra=n, moves=0, scan_complete=True)))
        assert _same(prep['unlayer_terminal'], dict(status='UNCHANGED', reason='boundary triangles belong to different tetrahedra',
            stats=dict(candidate_tests=0, initial_tetrahedra=n, remaining_tetrahedra=n, moves=0)))
        upper, split = _query_replay(source, query)
        rays = _exposed_rays(source, query['exposed_positive_points'])
        hitting = _hitting(n, rays)
        if name != 'W34':
            retained = json.loads(files[name+'-exposed-replay.json'])
            assert retained['passed'] is True and retained['discovery_used'] is False
            assert retained['original_matching_replayed'] is True
            assert retained['query_sha256'] == sha256(files[name+'-query.json']).hexdigest()
            assert retained['script_sha256'] == sha256(files['replay_exposed.py']).hexdigest()
            assert retained['source_sha256'] == digest(source) and _same(retained['native_sha256'], original_pins)
            assert _same(retained['unique_exposed_rays'], rays)
            assert all(_same(retained[k], v) for k, v in hitting.items())
            assert _same(retained['max_hitting_subsets'], 10000)
            assert _same(retained['global_h_upper_bound'], upper)
            assert _same(retained['exact_h'], upper if upper == hitting['global_h_lower_bound'] else None)
        else:
            assert not rays
        prime.append(dict(id=name, tetrahedra=n, source_sha256=digest(source),
            v3_chain_verified=True, strict32_exhausted=True, euler_status=query['result']['status'],
            h_lower_bound=hitting['global_h_lower_bound'], h_upper_bound=upper,
            exact_h=upper if upper == hitting['global_h_lower_bound'] else None,
            exposed_root_rays_verified=len(rays)))
    assert [r['h_lower_bound'] for r in prime] == [3, 3, 0]
    assert [r['h_upper_bound'] for r in prime] == [3, None, None]
    assert [r['exposed_root_rays_verified'] for r in prime] == [5, 6, 0]
    legacy_files = strict32_archive_files()
    legacy_query = json.loads(legacy_files['euler-queries.json'])
    archive_path = PACKAGE.parent/'strict_pachner32_research/data/generation/euler-queries.json.gz'
    descents = []
    for index, name in enumerate(('T8', 'F12', 'TT17')):
        data = load(name+'-descent')
        source, result = data['source'], data['result']
        assert _same(source, legacy_query['records'][index]['source'])
        assert data['historical_source_archive_sha256'] == sha256(archive_path.read_bytes()).hexdigest()
        assert data['source_sha256'] == digest(source) and data['id'] == name
        assert _same(data['heights'], [[0]*4 for _ in source['tetrahedra']])
        assert _same(data['config'], dict(max_nodes=256, max_oracle_states=10000, max_regions=10000,
                                          max_upward=1, max_work=200000, method='sleep'))
        assert result['status'] == 'DESCENT_FOUND'
        checked = inspect_pachner_descent(source, data['heights'], result['certificate'], max_upward=1)
        packet = dict(schema='normal-pachner-descent-v1', source_sha256=digest(source),
                      certificate=result['certificate'], successor=checked['triangulation'])
        assert verify_normal_pachner_descent(source, packet)
        assert _same(data['replay'], dict(status='DESCENT_FOUND', summary=checked, verified=True))
        assert checked['upward_moves'] == 1 and checked['downward_moves'] == 2
        stats = result['stats']
        assert all(type(v) is int and v >= 0 for k, v in stats.items() if k not in ('method', 'cover_backend'))
        assert stats['method'] == 'sleep' and stats['cover_backend'] == 'indexed'
        assert stats['nodes'] <= 256 and stats['aggregate_work'] <= 200000
        assert stats['regions_indexed'] <= 10000 and stats['oracle_states'] <= 10000
        descents.append(dict(id=name, source_sha256=digest(source), before=checked['initial_tetrahedra'],
            after=checked['final_tetrahedra'], upward_moves=1, downward_moves=2, verified=True))
    retained = json.loads(files['fresh-replay.json'])
    assert retained['passed'] is True and retained['discovery_used'] is False and retained['general_quasipolynomial'] is False
    assert _same(retained['native_sha256'], original_pins)
    assert retained['script_sha256'] == sha256(files['replay_all.py']).hexdigest()
    assert _same(retained['prime_sources'], prime) and _same(retained['local_descents'], descents)
    assert _same(retained['historical_archive_fresh_replay'], strict32)
    for name, digest_value in retained['files_sha256'].items():
        assert name in files and digest_value == sha256(files[name]).hexdigest()
    return dict(preprocessing_calls=3, supplied_source_queries=3, local_descent_calls=3,
                original_standard_rays=11, prime_sources=prime, local_descents=descents)


def _staged_archives(files, baseline_sources):
    data, retained = json.loads(files['audit.json']), json.loads(files['replay.json'])
    assert data['passed'] is True and _same(data['calls_completed'], 20)
    assert data['failures'] == data['unreturned_calls'] == [] and data['active_call'] is None
    assert data['script_sha256'] == sha256(files['audit.py']).hexdigest()
    assert _same(data['protocol'], dict(circle_whole_calls=2, enabled_endpoint_queries=6,
        no_timing_claim=True, preprocessing_only_calls=12,
        source_query_stats_scope='Separate supplied-source call; never summed into alleged whole-recognition stats.', total_calls=20))
    assert retained['passed'] is True and retained['discovery_used'] is False and retained['general_quasipolynomial'] is False
    assert retained['audit_sha256'] == sha256(files['audit.json']).hexdigest()
    assert retained['script_sha256'] == sha256(files['replay.py']).hexdigest()
    assert _same(retained['native_sha256'], data['native_sha256'])
    assert len(data['circle']) == 2 and [r['arm'] for r in data['circle']] == list(ARMS)
    def replay_entry(diagram, entry, options):
        assert _same(entry['config'], options)
        summary = _driver_replay(diagram, entry['result'], options)
        chain = _chain(entry['result'])
        counts = {name: summary[name] for name in ('crushing_steps', 'boundary_unlayerings',
                  'pachner32_moves', 'pachner_descent_macros')}
        # Historical 'proof_verified' meant either full or partial chain replay.
        expected = dict(chain_schema=chain['schema'], proof_verified=True,
            final_tetrahedra=summary['final_tetrahedra'], reductions=counts,
            elementary_macro_upward_moves=summary['elementary_macro_upward_moves'],
            elementary_macro_downward_moves=summary['elementary_macro_downward_moves'])
        assert _same(entry['replay'], expected)
    for entry in data['circle']:
        assert entry['input_pd'] == [] and entry['result']['status'] == 'UNKNOT'
        replay_entry(Diagram.from_pd([]), entry, configs(entry['arm']))
    case_map = {c['id']: c for c in cases()}
    expected_ids = ['T', 'F', 'TT', 'T25', 'T27', 'W34']
    assert [r['id'] for r in data['records']] == expected_ids
    records, assembled_count, ray_count, macro_count = [], 0, 0, 0
    for record in data['records']:
        case = case_map[{'T': 'trefoil', 'F': 'figure_eight'}.get(record['id'], record['id'])]
        assert _same(record['input_pd'], case['input_pd']) and _same(record['braid'], case['braid'])
        diagram = Diagram.from_pd(case['input_pd'])
        assert set(record['preprocessing']) == set(ARMS)
        for arm in ARMS:
            entry = record['preprocessing'][arm]
            replay_entry(diagram, entry, dict(configs(arm), max_tree_nodes=0))
            assert entry['result']['status'] == 'INCONCLUSIVE'
            assert entry['result']['stats']['lp_calls'] == entry['result']['stats']['nodes_attempted'] == 0
        base = _chain(record['preprocessing']['baseline']['result'])
        assert _same(base['triangulation'], baseline_sources[record['id']])
        chain = _chain(record['preprocessing']['u1']['result'])
        assert _same(base['source_triangulation'], chain['source_triangulation']) and _same(base['shelling'], chain['shelling'])
        assert _same(base['steps'], chain['steps'][:len(base['steps'])])
        source = chain['triangulation']
        n = len(source['tetrahedra'])
        assert _same(record['endpoint_comparison'], dict(baseline_tetrahedra=len(base['triangulation']['tetrahedra']),
            u1_tetrahedra=n, baseline_steps_literal_prefix=True,
            baseline_source_sha256=digest(base['triangulation']), u1_source_sha256=digest(source)))
        query = record['source_query']
        upper, split = _query_replay(source, query)
        if upper is not None:
            assembled = query['assembled_proof']
            assert type(assembled) is dict and set(assembled) == {'certificate', 'scope', 'verified'}
            assert assembled['verified'] is True
            proof = assembled['certificate']
            assert _same(proof['chain'], chain) and _same(proof['exhaustion'], query['result']['certificate'])
            assert verify_crushing_recognition(diagram, proof)
            assert 'not a fresh whole-driver result' in assembled['scope']
            assembled_count += 1
        else:
            assert query['assembled_proof'] is None
        rays = _exposed_rays(source, query['exposed_positive_points'])
        hitting = _hitting(n, rays)
        lower = hitting['global_h_lower_bound']
        records.append(dict(id=record['id'], source_sha256=digest(source), tetrahedra=n,
            original_matching_replayed=True, unique_exposed_rays=rays, **hitting,
            global_h_upper_bound=upper, exact_h=upper if upper == lower else None,
            status=query['result']['status'], discovery_used=False))
        ray_count += len(rays)
        macro_count += record['preprocessing']['u1']['result']['stats']['pachner_descent_macros']
    assert [r['exact_h'] for r in records] == [1, 0, 2, 1, 2, None]
    assert [r['tetrahedra'] for r in records] == [7, 10, 16, 11, 17, 31]
    assert _same(retained['records'], records)
    assert _same(retained['replayed_circle_whole_calls'], 2) and _same(retained['replayed_preprocessing_calls'], 12)
    assert _same(retained['replayed_source_queries'], 6) and _same(retained['assembled_negative_proofs'], assembled_count)
    assert assembled_count == 5 and ray_count == 10 and macro_count == 13
    compact = [{k: r[k] for k in ('id', 'source_sha256', 'tetrahedra', 'global_h_lower_bound',
                'global_h_upper_bound', 'exact_h', 'status')} for r in records]
    return dict(calls=20, whole_circle_calls=2, preprocessing_calls=12, supplied_source_queries=6,
        assembled_negative_proofs=5, original_standard_rays=10, accepted_preprocessing_macros=13,
        records=compact, no_timing_claim=True)


def check_archive():
    assert __debug__, 'research replay requires assertions enabled'
    files = _archives()
    strict32 = check_strict32_archive()
    old = _old_archives(files['strict-descent-next-design'], strict32)
    legacy_queries = json.loads(strict32_archive_files()['euler-queries.json'])['records']
    baseline_sources = {name: row['source'] for name, row in zip(('T', 'F', 'TT'), legacy_queries)}
    baseline_sources.update({name: json.loads(files['strict-descent-next-design'][name+'-preprocess.json'])['record']['source']
                             for name in ('T25', 'T27', 'W34')})
    staged = _staged_archives(files['fixed-u1-staged-audit'], baseline_sources)
    return dict(passed=True, strict32_prerequisite=strict32, earlier_stages=old, fixed_u1_stages=staged,
        discovery_used=False, fresh_regina_used=False, general_quasipolynomial=False,
        historical_pins_scope='Generation-time metadata; replayed proofs are checked with current pinned verifiers.',
        counter_scope='Recorded nonnegative bounds and retained-move aggregation, not independently replayed LP operation traces.',
        staged_scope='Separate preprocessing and source queries; assembled proofs are not fresh whole-driver calls.',
        h_scope='Exact labelled-source bounds; no invariance or general monotonicity under retriangulation.')


replay_archives = check_archive


def check_audit(audit):
    assert __debug__, 'research replay requires assertions enabled'
    pins = source_hashes()
    assert audit['schema'] == 'pachner-descent-audit-v1' and audit['passed'] is True
    assert _same(audit['source_sha256'], pins)
    assert _same(audit['config'], {arm: configs(arm) for arm in ARMS})
    assert audit['wall_limit_seconds'] is None and audit['unreturned_calls'] == []
    assert audit['failures'] == [] and audit['active_call'] is None
    definitions = cases()
    assert _same(audit['case_order'], [c['id'] for c in definitions])
    assert type(audit['records']) is list and len(audit['records']) == 7
    for record, case in zip(audit['records'], definitions):
        assert all(_same(record[k], v) for k, v in case.items())
        assert record['input_pd_sha256'] == digest(case['input_pd'])
        assert set(record['arms']) == set(ARMS)
        for arm in ARMS:
            retained = record['arms'][arm]
            assert type(retained) is dict and set(retained) == {'result', 'replay'}
            summary = replay_result(Diagram.from_pd(case['input_pd']), arm, retained['result'], configs(arm))
            assert _same(retained['replay'], summary)
            assert summary['status'] in ('INCONCLUSIVE', 'UNKNOT' if case['id'] == 'circle' else 'KNOTTED')
    assert _same(audit['coverage'], dict(ordinary_calls_expected=14, ordinary_calls_completed=14))
    assert _same(audit['archival_replay'], check_archive())
    assert source_hashes() == pins
    return True


def check_benchmark(benchmark, audit, audit_bytes):
    assert check_audit(audit)
    pins = source_hashes()
    assert benchmark['schema'] == 'pachner-descent-benchmark-v1' and benchmark['passed'] is True
    assert _same(benchmark['source_sha256'], pins)
    assert benchmark['audit_sha256'] == sha256(audit_bytes).hexdigest()
    assert _same(benchmark['protocol'], BENCHMARK_PROTOCOL)
    assert _same(benchmark['config'], {arm: configs(arm) for arm in ARMS})
    assert benchmark['unreturned_calls'] == [] and _same(benchmark['calls_completed'], 50)
    assert benchmark['failures'] == [] and benchmark['active_call'] is None
    assert [r['id'] for r in benchmark['records']] == BENCHMARK_PROTOCOL['case_ids']
    indexed = {r['id']: r for r in audit['records']}
    count = 0
    for case_index, record in enumerate(benchmark['records']):
        case = indexed[record['id']]
        assert record['input_pd_sha256'] == case['input_pd_sha256']
        assert set(record['warmups']) == set(ARMS)
        reference, all_samples = {}, []
        for arm in ARMS:
            warmup = record['warmups'][arm]
            assert _same(warmup['result'], case['arms'][arm]['result'])
            assert _same(warmup['replay'], case['arms'][arm]['replay'])
            payload = canonical_bytes(warmup['result'])
            reference[arm] = dict(status=warmup['result']['status'],
                result_sha256=sha256(payload).hexdigest(), serialized_bytes=len(payload))
            all_samples.append((arm, warmup, True))
        assert len(record['paired']) == 3
        for round_index, pair in enumerate(record['paired']):
            assert _same(pair['round'], round_index)
            assert pair['order'] == list(ARMS if (case_index+round_index) % 2 == 0 else reversed(ARMS))
            assert set(pair['samples']) == set(ARMS)
            all_samples.extend((arm, pair['samples'][arm], False) for arm in ARMS)
        assert record['aa']['arm'] == 'baseline' and len(record['aa']['samples']) == 2
        all_samples.extend(('baseline', sample, False) for sample in record['aa']['samples'])
        for arm, sample, warmup in all_samples:
            fields = {'elapsed_ns', 'status', 'result_sha256', 'serialized_bytes'}
            assert type(sample) is dict and set(sample) == fields | ({'result', 'replay'} if warmup else set())
            assert type(sample['elapsed_ns']) is int and sample['elapsed_ns'] > 0
            assert type(sample['serialized_bytes']) is int and sample['serialized_bytes'] > 0
            assert all(_same(sample[k], v) for k, v in reference[arm].items())
            count += 1
        statuses = {sample['status'] for _, sample, _ in all_samples}
        eligible = len(statuses) == 1 and statuses <= {'UNKNOT', 'KNOTTED'}
        ratios = [pair['samples']['baseline']['elapsed_ns']/pair['samples']['u1']['elapsed_ns']
                  for pair in record['paired']] if eligible else []
        summary = dict(eligible_common_complete_outcome=eligible,
            common_status=next(iter(statuses)) if eligible else None,
            paired_baseline_over_u1=ratios,
            median_paired_baseline_over_u1=median(ratios) if ratios else None,
            median_ns={arm: median([p['samples'][arm]['elapsed_ns'] for p in record['paired']]) for arm in ARMS},
            aa_ratio=record['aa']['samples'][0]['elapsed_ns']/record['aa']['samples'][1]['elapsed_ns'],
            outcome_scope='Same completed whole-diagram verdict.' if eligible else
                'Resource-bounded outcomes retained; no recognition speed ratio.')
        assert _same(record['summary'], summary)
    assert count == BENCHMARK_PROTOCOL['total_calls'] == 50
    assert source_hashes() == pins
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, required=True)
    parser.add_argument('--benchmark', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    raw = args.audit.read_bytes()
    audit = json.loads(raw)
    benchmark = json.loads(args.benchmark.read_bytes()) if args.benchmark else None
    assert check_audit(audit) if benchmark is None else check_benchmark(benchmark, audit, raw)
    summary = dict(passed=True, ordinary_calls=14, discovery_used=False,
        general_quasipolynomial=False, source_files=len(audit['source_sha256']),
        archival_old_preprocessing_calls=3, archival_old_source_queries=3,
        archival_local_descents=3, archival_staged_calls=20,
        archival_staged_assembled_proofs=5, archival_standard_rays=21,
        outcomes={arm: [r['arms'][arm]['result']['status'] for r in audit['records']] for arm in ARMS})
    if benchmark is not None:
        summary.update(benchmark_cases=5, timed_and_warmup_calls=50,
            eligible_cases=[r['id'] for r in benchmark['records'] if r['summary']['eligible_common_complete_outcome']])
    if args.output:
        args.output.write_bytes(canonical_bytes(summary)+b'\n')
    print(json.dumps(summary, sort_keys=True))


if __name__ == '__main__':
    main()
