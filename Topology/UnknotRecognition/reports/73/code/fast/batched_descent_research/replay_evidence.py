"""Independently replay retained batch experiments without any producer calls.

Typical packaged invocation from code/fast/:
    python -m batched_descent_research.replay_evidence --output replay.json

The default evidence directory is ../../evidence/geometry relative to
code/fast, containing paired_batch_benchmark.json and benchmark_evidence/.
Counterexample records live in the sibling evidence/counterexample/
directory.  The --evidence-root option permits any extracted location.

Only native consumers and input parsing are used.  In particular no move,
transport, normal-coordinate, fixture, dynamic-score or matching producer
is called, and neither Regina nor NetworkX is required.  The default call
guard enforces those exclusions at runtime.
"""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import time


# Also support direct invocation by an absolute script path, from any cwd.
_FAST_ROOT = Path(__file__).resolve().parents[1]
if str(_FAST_ROOT) not in sys.path:
    sys.path.insert(0, str(_FAST_ROOT))


class EvidenceError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise EvidenceError(message)


def digest(value):
    data = json.dumps(value, sort_keys=True, separators=(',', ':')).encode()
    return hashlib.sha256(data).hexdigest()


def _read_heights_checked(raw, values):
    from fastunknot.cocycle_transport_verify import _read_heights, _check_signed_edges
    from fastunknot.normal_surface_geometry import _prepare

    prepared = _prepare(raw, lambda: None)
    heights = _read_heights(values, len(raw['tetrahedra']), lambda: None)
    require(heights is not None and _check_signed_edges(prepared, heights, lambda: None),
            'invalid retained source cocycle')
    return heights


def _verify_source(raw, metadata):
    """Check the given PD exterior or the given explicit layered face pattern."""
    require(metadata['initial_tetrahedra'] == len(raw['tetrahedra']),
            'source tetrahedron count does not match metadata')
    require(metadata['initial_triangulation_sha256'] == digest(raw),
            'initial geometry fingerprint mismatch')
    if metadata.get('diagram_bound') is True:
        from fastunknot.diagram import Diagram
        from fastunknot.diagram_exterior_verify import verify_diagram_exterior

        diagram = Diagram.from_pd(metadata['pd'])
        require(diagram.crossings == metadata['crossings'], 'source crossing count mismatch')
        require(verify_diagram_exterior(diagram, raw), 'initial PD exterior rejected')
        return 'independently verified source PD exterior'
    require(metadata.get('kind') == 'layered_solid_torus', 'unknown source geometry contract')
    count = metadata.get('tetrahedra')
    require(type(count) is int and count >= 1 and count == len(raw['tetrahedra']),
            'invalid layered source size')
    for t, faces in enumerate(raw['tetrahedra']):
        if t + 1 == count:
            first = ((t, [1, 2, 3, 0]), (t, [3, 0, 1, 2]))
        else:
            first = ((t + 1, [2, 1, 3, 0]), (t + 1, [0, 3, 1, 2]))
        for f, (target, permutation) in enumerate(first):
            require(faces[f] == dict(tetrahedron=target, permutation=permutation),
                    'layered source violates its specified forward face pattern')
        if t == 0:
            require(faces[2:] == [None, None], 'incorrect layered boundary faces')
        else:
            for f, permutation in ((2, [3, 1, 0, 2]), (3, [0, 2, 3, 1])):
                require(faces[f] == dict(tetrahedron=t - 1, permutation=permutation),
                        'layered source violates its specified backward face pattern')
    return 'independently checked explicit layered source face pattern'


def _verify_isomorphism(source, source_h, target, target_h, charts):
    """Check an explicit target-to-source tetrahedron/corner isomorphism."""
    require(len(source['tetrahedra']) == len(target['tetrahedra']) == len(charts),
            'source/final isomorphism has the wrong size')
    require(sorted(t for t, _ in charts) == list(range(len(charts))),
            'source/final tetrahedron map is not a bijection')
    for t, (old_t, chart) in enumerate(charts):
        require(sorted(chart) == [0, 1, 2, 3], 'source/final corner chart is not a permutation')
        for a in range(4):
            require(target_h[t][a] - target_h[t][0]
                    == source_h[old_t][chart[a]] - source_h[old_t][chart[0]],
                    'source/final cocycle differs under the explicit isomorphism')
        for f, entry in enumerate(target['tetrahedra'][t]):
            original = source['tetrahedra'][old_t][chart[f]]
            if entry is None:
                require(original is None, 'source/final boundary face mismatch')
                continue
            require(original is not None, 'source/final interior face mismatch')
            u, permutation = entry['tetrahedron'], entry['permutation']
            old_u, other = charts[u]
            require(original['tetrahedron'] == old_u and all(
                original['permutation'][chart[v]] == other[permutation[v]]
                for v in range(4)), 'source/final face-permutation mismatch')


def _bind_source_by_expansion_labels(evidence):
    """Check compact expansion metadata using an explicit final source map.

    The recorded forward operations expand disjoint pairs of ORIGINAL
    tetrahedra.  Tracking their labels needs no intermediate triangulation.
    The saved batch verifier establishes before-to-final homeomorphism;
    the final-to-initial face-permutation check below independently binds
    that final geometry to the source.  No forward producer is invoked.
    """
    from fastunknot.integer_codec import encoded_integer

    initial, initial_h = evidence['initial_triangulation'], evidence['initial_heights']
    initial_h = _read_heights_checked(initial, initial_h)
    before, heights = evidence['before'], evidence['heights']
    heights = _read_heights_checked(before, heights)
    expansions = evidence['expansions']
    tags = [('old', t) for t in range(len(initial['tetrahedra']))]
    old_charts, five_rows = [], []
    for i, expansion in enumerate(expansions):
        require(type(expansion) is dict and set(expansion) == {'move', 'bipyramid_heights'},
                'invalid compact expansion fields')
        move = expansion['move']
        require(type(move) is dict and set(move) == {'schema', 'tetrahedron', 'face'}
                and move['schema'] == 'pachner-23-v1', 'invalid compact expansion schema')
        t, f = move['tetrahedron'], move['face']
        require(type(t) is int and 0 <= t < len(tags) and type(f) is int and 0 <= f < 4,
                'compact expansion has an invalid address')
        require(tags[t][0] == 'old', 'expansion pairs are not disjoint original tetrahedra')
        old_t = tags[t][1]
        entry = initial['tetrahedra'][old_t][f]
        require(entry is not None and entry['tetrahedron'] != old_t,
                'expansion source is not a pair of distinct tetrahedra')
        old_u, permutation = entry['tetrahedron'], entry['permutation']
        require(('old', old_u) in tags, 'expansion reuses an earlier removed original tetrahedron')
        u = tags.index(('old', old_u))
        shared = [v for v in range(4) if v != f]
        left = [3 if v == f else shared.index(v) for v in range(4)]
        right = [4 if v == permutation[f] else left[permutation.index(v)] for v in range(4)]
        five = expansion['bipyramid_heights']
        require(type(five) is list and len(five) == 5, 'invalid compact five-height row')
        five = [encoded_integer(x) for x in five]
        require(five[0] == 0, 'compact five-height row is not normalized')
        for old, labels in ((old_t, left), (old_u, right)):
            for v in range(4):
                require(initial_h[old][v] - initial_h[old][0]
                        == five[labels[v]] - five[labels[0]],
                        'compact expansion heights disagree with the source cocycle')
        old_charts.append(((old_t, left), (old_u, right)))
        five_rows.append(five)
        tags = [tag for j, tag in enumerate(tags) if j not in (t, u)]
        tags.extend(('up', i, j) for j in range(3))
    require(len(tags) == len(before['tetrahedra']), 'compact expansion count does not reach before state')
    old_labels = ((3, 4, 0, 1), (3, 4, 1, 2), (3, 4, 2, 0))
    for t, tag in enumerate(tags):
        expected = (initial_h[tag[1]] if tag[0] == 'old' else
                    [five_rows[tag[1]][v] for v in old_labels[tag[2]]])
        require([x - heights[t][0] for x in heights[t]] == [x - expected[0] for x in expected],
                'retained inflated cocycle disagrees with its compact source chart')
    batch = evidence['batch']
    regions = batch['certificate']['regions']
    require(len(regions) == len(expansions), 'batch does not undo all disjoint expansion regions')
    used, removed, region_ids = set(), set(), []
    for region in regions:
        selected = [tags[item['tetrahedron']] for item in region]
        require(all(tag[0] == 'up' for tag in selected), 'batch consumes an unexpanded source tetrahedron')
        ids = {tag[1] for tag in selected}
        require(len(ids) == 1, 'one batch region combines distinct expansion regions')
        i = next(iter(ids))
        require(i not in used and {tag[2] for tag in selected} == {0, 1, 2},
                'duplicate or incomplete expansion inverse')
        used.add(i)
        region_ids.append(i)
        for item, tag in zip(region, selected):
            require(item['vertices'] == list(old_labels[tag[2]]),
                    'inverse region uses different formal corner charts')
            removed.add(item['tetrahedron'])
    charts = []
    for t, tag in enumerate(tags):
        if t not in removed:
            require(tag[0] == 'old', 'an expansion region was left in the final source map')
            charts.append((tag[1], [0, 1, 2, 3]))
    for i in region_ids:
        for (old_t, source_labels), new_labels in zip(old_charts[i],
                                                     ((0, 1, 2, 3), (0, 1, 2, 4))):
            charts.append((old_t, [source_labels.index(v) for v in new_labels]))
    final_h = batch['certificate']['cocycle']['heights']
    _verify_isomorphism(initial, initial_h, batch['triangulation'], final_h, charts)
    return len(expansions)


def _verify_sequential(evidence):
    from fastunknot.cocycle_transport_verify import verify_cocycle_transport

    certificate = evidence['sequential']
    require(type(certificate) is dict and set(certificate) == {
        'schema', 'moves', 'canonical_final_permutation'} and certificate['schema']
        == 'sequential-cocycle-transport-transcript-v1', 'invalid sequential transcript schema')
    raw, heights = evidence['before'], evidence['heights']
    original_regions = [{item['tetrahedron']: item['vertices'] for item in region}
                        for region in evidence['batch']['certificate']['regions']]
    require(len(certificate['moves']) == len(original_regions),
            'sequential transcript has a different number of selected sites')
    tags = [('old', t) for t in range(len(raw['tetrahedra']))]
    for i, move in enumerate(certificate['moves']):
        require(type(move) is dict and set(move) == {'triangulation', 'transport'},
                'invalid sequential transcript step')
        require(verify_cocycle_transport(raw, heights, move['triangulation'], move['transport']),
                'independent one-step transport consumer rejected the transcript')
        local = move['transport']['move']
        require(local['schema'] == 'pachner-32-v1', 'sequential transcript contains a different move type')
        removed = {item['tetrahedron'] for item in local['region']}
        require(all(tags[t][0] == 'old' for t in removed)
                and {tags[t][1] for t in removed} == set(original_regions[i]),
                'sequential transcript did not apply the same fixed original site')
        for item in local['region']:
            require(item['vertices'] == original_regions[i][tags[item['tetrahedron']][1]],
                    'sequential and batch formal charts differ')
        tags = [tag for t, tag in enumerate(tags) if t not in removed]
        tags.extend(('new', i, j) for j in range(2))
        raw, heights = move['triangulation'], move['transport']['heights']
    permutation = certificate['canonical_final_permutation']
    require(type(permutation) is list and all(type(i) is int for i in permutation)
            and sorted(permutation) == list(range(len(raw['tetrahedra']))),
            'invalid final sequential-to-batch index permutation')
    lookup = {old: new for new, old in enumerate(permutation)}
    batch_raw = evidence['batch']['triangulation']
    batch_h = evidence['batch']['certificate']['cocycle']['heights']
    require(len(batch_raw['tetrahedra']) == len(permutation), 'different sequential and batch output sizes')
    for new, old in enumerate(permutation):
        require(heights[old] == batch_h[new], 'sequential and batch height rows disagree')
        for f, entry in enumerate(raw['tetrahedra'][old]):
            expected = (None if entry is None else dict(tetrahedron=lookup[entry['tetrahedron']],
                                                        permutation=entry['permutation']))
            require(batch_raw['tetrahedra'][new][f] == expected,
                    'sequential and batch face pairings disagree')
    return len(certificate['moves'])


def replay_case(path, expected=None):
    from fastunknot.pachner_batch_verify import verify_pachner_32_batch

    evidence = json.loads(path.read_text())
    source = evidence['source']
    source_kind = _verify_source(evidence['initial_triangulation'], source)
    require(source['inflated_triangulation_sha256'] == digest(evidence['before'])
            and source['inflated_tetrahedra'] == len(evidence['before']['tetrahedra']),
            'retained before-state metadata mismatch')
    batch = evidence['batch']
    require(verify_pachner_32_batch(evidence['before'], batch['triangulation'],
                                   batch['certificate'], evidence['heights']),
            'independent simultaneous consumer rejected retained evidence')
    regions = batch['certificate']['regions']
    owners = {item['tetrahedron']: (i, item['vertices']) for i, region in enumerate(regions)
              for item in region}
    sites = evidence['sites']
    require(type(sites) is list and len(sites) == len(regions), 'incorrect retained site count')
    used = set()
    for site in sites:
        require(type(site) is dict and set(site) == {'tetrahedron', 'vertices'},
                'invalid retained input site')
        t, vertices = site['tetrahedron'], site['vertices']
        require(type(t) is int and t in owners and type(vertices) is list
                and len(vertices) == 2 and all(type(v) is int and 0 <= v < 4 for v in vertices)
                and vertices[0] != vertices[1], 'invalid retained input edge address')
        region_id, labels = owners[t]
        require(region_id not in used and {labels[v] for v in vertices} == {3, 4},
                'retained input sites differ from the certified selected centres')
        used.add(region_id)
    expansions = _bind_source_by_expansion_labels(evidence)
    moves = _verify_sequential(evidence)
    require(expansions == moves == len(batch['certificate']['regions'])
            == source['expansions'], 'different retained move counts')
    final_sha = digest(batch['triangulation'])
    heights_sha = digest(batch['certificate']['cocycle']['heights'])
    if expected is not None:
        require(expected['evidence_sha256'] == digest(evidence), 'benchmark evidence fingerprint mismatch')
        require(expected['final_triangulation_sha256'] == final_sha
                and expected['final_heights_sha256'] == heights_sha,
                'replayed final state differs from the measured state')
        require(expected['mathematical_state_equal'] is True and expected['moves'] == moves,
                'benchmark comparison claim mismatch')
        sizes = expected['sizes']
        require(sizes['batch_bytes'] == len(json.dumps(batch, sort_keys=True,
                    separators=(',', ':')).encode())
                and sizes['sequential_bytes'] == len(json.dumps(evidence['sequential'],
                    sort_keys=True, separators=(',', ':')).encode()),
                'retained serialized witness byte counts disagree')
        require(sizes['batch_tetrahedron_rows'] == len(batch['triangulation']['tetrahedra'])
                and sizes['sequential_tetrahedron_rows'] == sum(
                    len(move['triangulation']['tetrahedra'])
                    for move in evidence['sequential']['moves']),
                'retained literal tetrahedron-row counts disagree')
    return dict(file=path.name, passed=True, moves=moves, compact_source_expansions=expansions,
                source_validation=source_kind, final_triangulation_sha256=final_sha,
                final_heights_sha256=heights_sha)


def replay_counterexample(path, batch_path):
    from fastunknot.cocycle_transport_verify import verify_cocycle_transport
    from fastunknot.cocycle_peeling_verify import _summary
    from fastunknot.pachner_batch_verify import verify_pachner_32_batch

    record = json.loads(path.read_text())
    batch = json.loads(batch_path.read_text())
    before, heights = record['before']['triangulation'], record['before']['heights']
    initial = _summary(before, heights, lambda: None)
    raw_summaries = {'before': initial}
    for key in ('singleton_one', 'singleton_two'):
        move = record[key]
        require(verify_cocycle_transport(before, heights, move['triangulation'], move['transport']),
                'counterexample singleton transport rejected')
        raw_summaries[key] = _summary(move['triangulation'], move['transport']['heights'], lambda: None)
    first, both = record['singleton_one'], record['after_both']
    require(verify_cocycle_transport(first['triangulation'], first['transport']['heights'],
                                     both['triangulation'], both['transport']),
            'counterexample second sequential transport rejected')
    raw_summaries['after_both'] = _summary(both['triangulation'], both['transport']['heights'], lambda: None)
    require(verify_pachner_32_batch(before, batch['triangulation'], batch['certificate'], heights),
            'counterexample simultaneous consumer rejected')
    require(batch['triangulation'] == both['triangulation']
            and batch['certificate']['cocycle']['heights'] == both['transport']['heights'],
            'counterexample sequential and simultaneous endpoints disagree')
    for key, values in raw_summaries.items():
        claimed = record[key]['summary']
        require(claimed['raw_euler'] == values['euler']
                and claimed['peel_penalty'] == values['link_euler']
                and claimed['peeled_euler'] == values['euler'] - values['link_euler'],
                'counterexample full-cell summary mismatch')
    peeled = {key: values['euler'] - values['link_euler'] for key, values in raw_summaries.items()}
    gains = dict(first=peeled['singleton_one'] - peeled['before'],
                 second=peeled['singleton_two'] - peeled['before'],
                 combined=peeled['after_both'] - peeled['before'])
    require(gains == record['peeled_gains'] == dict(first=1, second=1, combined=0),
            'counterexample does not have the stated strict interaction')
    return dict(passed=True, singleton_transports=2, continuation_transports=1,
                batch_transports=1, independently_recomputed_states=4, peeled_gains=gains)


_FORBIDDEN = {
    'fastunknot.pachner23', 'fastunknot.pachner32', 'fastunknot.pachner_batch',
    'fastunknot.cocycle_transport', 'fastunknot.normal_cocycle',
    'fastunknot.cocycle_peeling', 'fastunknot.corner_minima',
    'normal_orbit_research.fixtures', 'batched_descent_research.fixtures',
    'fastunknot.diagram_exterior',
}


def _guard(frame, event, arg):
    if event != 'call' or frame.f_code.co_name == '<module>':
        return
    module = frame.f_globals.get('__name__', '')
    if module in _FORBIDDEN or module.split('.', 1)[0] in ('regina', 'networkx'):
        raise EvidenceError('forbidden producer/dependency call during replay: ' + module)


def default_evidence_root():
    package = Path(__file__).resolve().parents[3]
    options = (package / 'evidence' / 'geometry', package / 'geometry_theory')
    return next((path for path in options if (path / 'benchmark_evidence').is_dir()), options[0])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence-root', type=Path, default=default_evidence_root())
    parser.add_argument('--output', type=Path)
    parser.add_argument('--no-call-guard', action='store_true',
                        help='Disable the diagnostic producer-call guard; never enables producers.')
    args = parser.parse_args()
    root = args.evidence_root
    benchmark = json.loads((root / 'paired_batch_benchmark.json').read_text())
    expected = {case['evidence_file']: case for case in benchmark['cases']}
    files = sorted((root / 'benchmark_evidence').glob('*.json'))
    require(set(expected) == {path.name for path in files}, 'benchmark inventory and evidence files differ')
    start = time.perf_counter()
    previous = sys.getprofile()
    if not args.no_call_guard:
        sys.setprofile(_guard)
    try:
        cases = []
        for path in files:
            case = replay_case(path, expected[path.name])
            cases.append(case)
            print(json.dumps(dict(file=path.name, moves=case['moves'], passed=True)), flush=True)
        counterexample_path = root.parent / 'counterexample' / 'peeling_geometric_counterexample.json'
        counterexample_batch = root.parent / 'counterexample' / 'peeled_counterexample_batch.json'
        if not counterexample_path.exists():
            counterexample_path = root / 'peeled_counterexample.json'
        if not counterexample_batch.exists():
            counterexample_batch = root / 'peeled_counterexample_batch.json'
        counterexample = replay_counterexample(counterexample_path, counterexample_batch)
    finally:
        sys.setprofile(previous)
    result = dict(schema='pachner-batch-evidence-replay-v1', passed=True,
        producer_call_guard=not args.no_call_guard, regina_required=False, networkx_required=False,
        benchmark_cases=len(cases), benchmark_batch_transports=len(cases),
        benchmark_sequential_transports=sum(case['moves'] for case in cases),
        compact_source_expansions=sum(case['compact_source_expansions'] for case in cases),
        source_final_isomorphisms=len(cases), elapsed_seconds=time.perf_counter() - start,
        counterexample=counterexample, cases=cases)
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items() if key != 'cases'}, indent=2))


if __name__ == '__main__':
    main()
