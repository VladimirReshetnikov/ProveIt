#!/usr/bin/env python3
"""One fresh native W34 call, followed separately by discovery-disabled replay.

No timing, wall cutoff, selector replacement, injected source, or earlier-arm
solve. The archive supplies only the exact original PD/options and retained
comparison result. Returned results are saved before any proof verification.
"""
import argparse
from contextlib import contextmanager, ExitStack
from copy import deepcopy
from hashlib import sha256
import importlib
import json
from pathlib import Path
import platform
import sys
from unittest.mock import patch

import whole_call_prefix_replay as historical

if not __debug__:
    raise RuntimeError('Evidence checks require assertions enabled')

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
FAST = ROOT/'fast'
ARCHIVE = DATA/historical.ARCHIVE_NAME
CASE_ID = 'W34'
ARCHIVED_ARM = 'prepared_dantzig_lex'
RUN_SCHEMA = 'native-lex-prefix-whole-call-v1'
REPLAY_SCHEMA = 'native-lex-prefix-whole-call-replay-v1'
CAP_STATS = {
    'max_sectors': ('sectors_attempted',), 'max_bases': ('bases_attempted',),
    'max_crushes': ('crushing_steps', 'boundary_unlayerings', 'pachner32_moves', 'pachner_descent_macros'),
    'max_pivots': ('lp_pivots',), 'max_anchors': ('anchors_tested',),
    'max_tree_nodes': ('nodes_attempted',), 'max_hitting_subsets': ('hitting_subsets_tested',),
    'max_ellipsoid_iterations': ('lp_ellipsoid_iterations',),
    'max_feasibility_calls': ('lp_feasibility_calls',),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def same(left, right):
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return left.keys() == right.keys() and all(same(left[k], right[k]) for k in left)
    if type(left) in (list, tuple):
        return len(left) == len(right) and all(same(x, y) for x, y in zip(left, right))
    return left == right


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':')).encode()


def value_hash(value):
    return sha256(canonical(value)).hexdigest()


def file_hash(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def source_hashes():
    """Pure current-byte pin map; never equates native bytes to the archive."""
    native = sorted((FAST/'fastunknot').rglob('*.py'))
    require(len(native) == 299, 'expected complete current 299-module native inventory')
    paths = native+[Path(__file__).resolve(), DATA/'whole_call_prefix_replay.py', ARCHIVE]
    return {str(path.relative_to(ROOT)): file_hash(path) for path in sorted(paths)}


def load_reference():
    """Pure archive/metadata validation; no archived or native code is run."""
    payloads = historical.checked_members(ARCHIVE)
    audit_bytes = payloads[historical.PREFIX+'audit.json']
    audit = json.loads(audit_bytes)
    require(audit['schema'] == 'whole-call-prefix-audit-v1' and audit['passed'] is True,
            'expected completed historical whole-call audit')
    slots = [slot for slot in audit['calls']
             if slot['case_id'] == CASE_ID and slot['arm'] == ARCHIVED_ARM]
    require(len(slots) == 1, 'one exact historical W34 candidate record')
    slot = slots[0]
    require(slot['completion'] == 'RETURNED' and slot['active_phase'] is None,
            'historical candidate actually returned')
    require(value_hash(slot['input_pd']) == slot['input_pd_sha256'], 'historical PD digest')
    require(value_hash(slot['result']) == slot['result_sha256'], 'historical result digest')
    require(slot['options']['lp_policy'] == 'polynomial' and
            slot['options']['pachner_descent_method'] == 'geometric', 'fixed candidate policies')
    config = dict(case_id=CASE_ID, input_pd=slot['input_pd'], options=slot['options'])
    return dict(archive_sha256=historical.ARCHIVE_SHA256,
        archive_audit_sha256=sha256(audit_bytes).hexdigest(),
        historical_revision=historical.REVISION, archived_arm=ARCHIVED_ARM,
        config=config, config_sha256=value_hash(config),
        result=slot['result'], result_sha256=slot['result_sha256'],
        source_ledger=slot['source_ledger'])


def activate_native():
    if str(FAST) not in sys.path:
        sys.path.insert(0, str(FAST))


def check_import_paths():
    for name, module in tuple(sys.modules.items()):
        if name == 'fastunknot' or name.startswith('fastunknot.'):
            path = getattr(module, '__file__', None)
            if path is not None:
                require(Path(path).resolve().is_relative_to(FAST/'fastunknot'),
                        'native import came from another checkout: '+name)


@contextmanager
def discovery_disabled():
    """Disable producer entry points and already imported aliases by identity."""
    activate_native()
    targets = {
        'exact_lp': ('solve_nonnegative_kernel', '_solve_prepared_nonnegative_kernel',
                     '_run_kernel_policy', '_solve_prepared_kernel', '_ellipsoid_kernel'),
        'normal_crushing_search': ('recognize_by_crushing', '_recognize_by_crushing'),
        'normal_euler_tree': ('search_euler_tree',),
        'normal_euler_transversal': ('search_euler_transversal',),
        'normal_euler': ('decide_sector_euler',),
        'normal_sector': ('sector_rays', 'enumerate_sector', 'discover_in_sector',
                          '_discover_in_kernel', 'sparse_disc_search'),
        'positive_ray': ('extract_positive_ray',),
        'normal_vertex_reduction': ('vertex_reduction_ray',),
        'diagram_exterior': ('diagram_exterior',),
        'boundary_shellings': ('shell_boundary',),
        'normal_crushing': ('crush_normal_ray',),
        'normal_crushing_chain': ('make_crushing_chain', '_make_crushing_chain'),
        'boundary_unlayer': ('unlayer_boundary_once',),
        'normal_pachner32': ('reduce_pachner32_once', '_reduce'),
        'normal_geometric_descent': ('reduce_geometric_descent_once', '_reduce'),
        'normal_pachner_descent': ('reduce_pachner_descent_once', '_reduce'),
        'pachner23': ('pachner_23',), 'pachner32': ('pachner_32',),
    }
    originals = []
    for module_name, names in targets.items():
        module = importlib.import_module('fastunknot.'+module_name)
        originals.extend(getattr(module, name) for name in names)
    aliases = []
    for module_name, module in tuple(sys.modules.items()):
        if module is None or not module_name.startswith('fastunknot.'):
            continue
        for name, value in tuple(vars(module).items()):
            if any(value is original for original in originals):
                aliases.append((module, name))
    with ExitStack() as stack:
        for module, name in aliases:
            stack.enter_context(patch.object(module, name, side_effect=AssertionError('discovery disabled')))
        tree = importlib.import_module('fastunknot.normal_euler_tree')
        kernel = importlib.import_module('fastunknot.source_kernel')
        stack.enter_context(patch.object(tree._EulerMaskOracle, 'attempt',
                                        side_effect=AssertionError('mask discovery disabled')))
        stack.enter_context(patch.object(kernel.SourceKernel, 'extreme_witness',
                                        side_effect=AssertionError('ray discovery disabled')))
        check_import_paths()
        yield sorted([module.__name__+'.'+name for module, name in aliases]+
                     ['fastunknot.normal_euler_tree._EulerMaskOracle.attempt',
                      'fastunknot.source_kernel.SourceKernel.extreme_witness'])
        check_import_paths()


def replay_result(config, result):
    """Original-diagram proof replay and exact accepted-operation ledger."""
    from fastunknot.diagram import Diagram
    from fastunknot.normal_crushing_chain import verify_crushing_chain
    from fastunknot.normal_crushing_search import verify_crushing_recognition
    from fastunknot.normal_surface_geometry import _prepare
    require(type(result) is dict and result.get('status') in ('UNKNOT', 'KNOTTED', 'INCONCLUSIVE'),
            'native whole-call result shape/status')
    diagram = Diagram.from_pd(config['input_pd'])
    partial = result['status'] == 'INCONCLUSIVE'
    if partial:
        require(set(result) == {'status', 'reason', 'stats', 'partial_chain'}, 'partial result fields')
        require(type(result['reason']) is str and result['reason'], 'explicit partial reason')
        chain = result['partial_chain']
        require(verify_crushing_chain(diagram, chain), 'independent original-diagram partial replay')
        require(chain['status'] == 'REDUCED', 'partial chain never proves a verdict')
    else:
        require(set(result) == {'status', 'certificate', 'stats'}, 'conclusive result fields')
        require(verify_crushing_recognition(diagram, result['certificate']),
                'independent original-diagram conclusive replay')
        require(result['certificate']['status'] == result['status'], 'outer verdict binding')
        chain = result['certificate']['chain']
    require(chain['schema'] == 'diagram-crushing-v5' and same(chain['input_pd'], config['input_pd']),
            'original PD and geometric chain policy binding')
    stats = result['stats']
    require(type(stats) is dict and all(type(k) is str and type(v) is int and v >= 0
            for k, v in stats.items()), 'literal nonnegative reported counters')
    for cap, fields in CAP_STATS.items():
        require(all(field in stats for field in fields), 'complete reported cap counters')
        allowance = config['options'][cap]
        require(allowance is None or (type(allowance) is int and allowance >= 0 and
            sum(stats[field] for field in fields) <= allowance), 'recorded cumulative cap: '+cap)
    current = chain['source_triangulation']
    initial_count = len(current['tetrahedra'])
    ledger = [dict(kind='initial', source_key=value_hash(current))]
    if chain['shelling'] is not None:
        current = chain['shelling']['triangulation']
    ledger.append(dict(kind='shelled', source_key=value_hash(current)))
    shelled_count = len(current['tetrahedra'])
    mapping = {'normal-ray-crushing-v1': 'crushing_steps',
        'normal-boundary-unlayer-v1': 'boundary_unlayerings',
        'normal-pachner-32-v1': 'pachner32_moves',
        'normal-geometric-descent-v1': 'pachner_descent_macros'}
    counts = dict.fromkeys(mapping.values(), 0)
    up = down = 0
    for index, step in enumerate(chain['steps']):
        require(current is not None and step['schema'] in mapping, 'supported accepted chain operation')
        source_key = value_hash(current)
        if step['schema'] != 'normal-ray-crushing-v1':
            require(step['source_sha256'] == source_key, 'operation source binding')
        successor = step['successor']
        require(successor is None or len(successor['tetrahedra']) < len(current['tetrahedra']),
                'strict accepted source descent')
        extra = {}
        if step['schema'] == 'normal-geometric-descent-v1':
            moves, n = step['steps'], len(current['tetrahedra'])
            kinds = [move['certificate']['schema'] for move in moves]
            require(kinds in (['pachner-32-v1'], ['pachner-23-v1', 'pachner-32-v1', 'pachner-32-v1']),
                    'D or UDD macro')
            sizes = [len(move['triangulation']['tetrahedra']) for move in moves]
            require(sizes == ([n-1] if len(moves) == 1 else [n+1, n, n-1]) and
                    same(successor, moves[-1]['triangulation']), 'macro endpoint/counts')
            up += int(len(moves) == 3)
            down += 1+int(len(moves) == 3)
            extra = dict(word='D' if len(moves) == 1 else 'UDD', intermediate_tetrahedra=sizes)
        counts[mapping[step['schema']]] += 1
        ledger.append(dict(kind='step', index=index, schema=step['schema'], source_key=source_key,
            successor_key=None if successor is None else value_hash(successor),
            before_tetrahedra=len(current['tetrahedra']),
            after_tetrahedra=None if successor is None else len(successor['tetrahedra']), **extra))
        current = successor
    require(same(current, chain['triangulation']), 'exact final chain endpoint')
    require(stats['initial_tetrahedra'] == initial_count and stats['shelled_tetrahedra'] == shelled_count,
            'recorded initial/shelled counts')
    require(all(stats[field] == count for field, count in counts.items()), 'accepted operation counters')
    require(stats['stages'] == len(chain['steps'])+int(current is not None), 'stage count')
    require(stats['pachner_descent_upward_moves'] == up and
            stats['pachner_descent_downward_moves'] == down, 'macro elementary counters')
    endpoint = dict(terminal=True, source_sha256=None, tetrahedra=None, vertices=None, boundary_faces=None)
    if current is not None:
        prepared = _prepare(current, lambda: None)
        endpoint = dict(terminal=False, source_sha256=value_hash(current),
            tetrahedra=len(current['tetrahedra']), vertices=prepared['vertices'],
            boundary_faces=len(prepared['boundary_faces']))
    return dict(status=result['status'], proof_verified=not partial, partial_chain_verified=partial,
        accepted_counts=counts, elementary_macro_upward_moves=up,
        elementary_macro_downward_moves=down, endpoint=endpoint,
        recorded_work_counters_checked=True, lp_operation_trace_reconstructed=False), ledger


def verified_comparison(config, result, reference):
    """Replay actual proof first. Only then inspect equality to old candidate."""
    with discovery_disabled() as disabled:
        replay, ledger = replay_result(config, result)
        # Replay just this one historical proof, never its 449 LP queries or
        # other thirteen calls. No old native code or pivot selectors load.
        old_replay, old_ledger = replay_result(reference['config'], reference['result'])
        require(same(old_ledger, reference['source_ledger']), 'archived candidate source ledger binding')
    comparison = dict(typed_result_equal=same(result, reference['result']),
        typed_stats_equal=same(result['stats'], reference['result']['stats']),
        typed_source_ledger_equal=same(ledger, old_ledger),
        actual_status=result['status'], archived_status=reference['result']['status'],
        actual_result_sha256=value_hash(result), archived_result_sha256=reference['result_sha256'])
    return replay, ledger, comparison, old_replay, disabled


def reference_binding(reference):
    return {key: reference[key] for key in ('archive_sha256', 'archive_audit_sha256',
        'historical_revision', 'archived_arm', 'config_sha256', 'result_sha256')}


def summary(record):
    """Pure saved-metadata summary, also the stdout contract."""
    keys = ('schema', 'passed', 'phase', 'case_id', 'recognition_calls_started',
        'recognition_calls_returned', 'config_sha256', 'result_sha256', 'replay',
        'comparison', 'matches_archived_candidate', 'failures', 'source_pins_unchanged',
        'timings_claimed', 'wall_limit_seconds', 'historical_native_equality_asserted')
    return {key: record[key] for key in keys if key in record}


def save(path, record):
    temporary = path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(record, sort_keys=True, indent=2)+'\n')
    temporary.replace(path)


def reserve(path):
    path = Path(path).resolve()
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        stream.write('{}\n')
    return path


def new_record(schema):
    return dict(schema=schema, passed=False, phase='preflight', case_id=CASE_ID,
        failures=[], timings_claimed=False, wall_limit_seconds=None,
        historical_native_equality_asserted=False, archived_native_imported=False,
        selector_monkeypatch_used=False, injected_source_used=False,
        historical_lp_queries_replayed=0, other_historical_calls_replayed=0)


def run(output):
    output = reserve(output)
    record = new_record(RUN_SCHEMA)
    record.update(recognition_calls_started=0, recognition_calls_returned=0,
        result=None, result_sha256=None, source_ledger=None, replay=None, comparison=None,
        matches_archived_candidate=None, python=sys.version, platform=platform.platform())
    save(output, record)
    try:
        before = source_hashes()
        record['source_sha256'] = before
        reference = load_reference()
        record.update(reference=reference_binding(reference), config=deepcopy(reference['config']),
                      config_sha256=reference['config_sha256'])
        activate_native()
        from fastunknot.diagram import Diagram
        from fastunknot.integer_codec import json_safe
        from fastunknot.normal_crushing_search import recognize_by_crushing
        check_import_paths()
        diagram = Diagram.from_pd(record['config']['input_pd'])
        record.update(phase='recognition', recognition_calls_started=1)
        save(output, record)
        answer = recognize_by_crushing(diagram, **record['config']['options'])
        # Persist the actual full returned payload before mathematical replay
        # or comparisons, including a legitimate finite-cap partial result.
        record.update(result=json_safe(answer), recognition_calls_returned=1,
                      phase='independent_replay')
        record['result_sha256'] = value_hash(record['result'])
        save(output, record)
        replay, ledger, comparison, old_replay, disabled = verified_comparison(
            record['config'], record['result'], reference)
        record.update(replay=replay, source_ledger=ledger, comparison=comparison,
            archived_candidate_replay=old_replay, disabled_discovery_hooks=disabled,
            matches_archived_candidate=all(comparison[key] for key in
                ('typed_result_equal', 'typed_stats_equal', 'typed_source_ledger_equal')))
        check_import_paths()
        after = source_hashes()
        record.update(source_sha256_after=after, source_pins_unchanged=same(before, after))
        require(record['source_pins_unchanged'], 'current inputs changed during whole call/replay')
        record.update(passed=True, phase='complete')
        save(output, record)
        return record
    except BaseException as error:
        record['failures'].append(dict(phase=record['phase'], exception_class=type(error).__name__,
            message=str(error), result_returned=record['recognition_calls_returned'] == 1))
        try:
            record['source_sha256_after'] = source_hashes()
            record['source_pins_unchanged'] = same(record.get('source_sha256'), record['source_sha256_after'])
        except BaseException as pin_error:
            record['pin_failure'] = dict(exception_class=type(pin_error).__name__, message=str(pin_error))
        record.update(passed=False, phase='failed')
        save(output, record)
        raise


def check_record(record):
    """Discovery-disabled saved-proof replay; never invokes the recognizer."""
    require(record['schema'] == RUN_SCHEMA and record['passed'] is True and
            record['phase'] == 'complete' and record['failures'] == [], 'complete saved native evidence')
    require(type(record['recognition_calls_started']) is int and record['recognition_calls_started'] == 1 and
            type(record['recognition_calls_returned']) is int and record['recognition_calls_returned'] == 1,
            'exactly one fresh returned recognition call')
    expected_flags = dict(timings_claimed=False, wall_limit_seconds=None,
        historical_native_equality_asserted=False, archived_native_imported=False,
        selector_monkeypatch_used=False, injected_source_used=False,
        historical_lp_queries_replayed=0, other_historical_calls_replayed=0,
        source_pins_unchanged=True, case_id=CASE_ID)
    require(same({key: record[key] for key in expected_flags}, expected_flags), 'native evidence scope')
    before = source_hashes()
    require(same(record['source_sha256'], before) and same(record['source_sha256_after'], before),
            'exact current before/after native and runner/archive input pins')
    reference = load_reference()
    require(same(record['reference'], reference_binding(reference)), 'exact historical comparison binding')
    require(same(record['config'], reference['config']) and
            record['config_sha256'] == value_hash(record['config']) == reference['config_sha256'],
            'exact original archived PD/options')
    require(record['result_sha256'] == value_hash(record['result']), 'saved complete result hash')
    replay, ledger, comparison, old_replay, disabled = verified_comparison(
        record['config'], record['result'], reference)
    for key, value in (('replay', replay), ('source_ledger', ledger), ('comparison', comparison),
                       ('archived_candidate_replay', old_replay), ('disabled_discovery_hooks', disabled)):
        require(same(record[key], value), 'saved independent replay binding: '+key)
    expected_match = all(comparison[key] for key in
        ('typed_result_equal', 'typed_stats_equal', 'typed_source_ledger_equal'))
    require(type(record['matches_archived_candidate']) is bool and
            record['matches_archived_candidate'] == expected_match, 'reported equality is observed, not assumed')
    require(same(before, source_hashes()), 'inputs changed during saved-proof replay')
    return summary(record)


def check(input_path, output):
    input_path = Path(input_path).resolve()
    output = reserve(output)
    record = new_record(REPLAY_SCHEMA)
    record.update(input_path=str(input_path), input_sha256=None,
                  recognition_calls_started=0, recognition_calls_returned=0, discovery_disabled=True)
    save(output, record)
    try:
        record['input_sha256'] = file_hash(input_path)
        record['source_sha256'] = source_hashes()
        source = json.loads(input_path.read_bytes())
        record['phase'] = 'saved_proof_replay'
        save(output, record)
        record['run_summary'] = check_record(source)
        record['source_sha256_after'] = source_hashes()
        require(same(record['source_sha256'], record['source_sha256_after']), 'replay input pin stability')
        require(record['input_sha256'] == file_hash(input_path), 'saved run changed during replay')
        record.update(passed=True, phase='complete', source_pins_unchanged=True)
        save(output, record)
        return record
    except BaseException as error:
        record['failures'].append(dict(phase=record['phase'], exception_class=type(error).__name__, message=str(error)))
        record.update(passed=False, phase='failed')
        save(output, record)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    native = sub.add_parser('run')
    native.add_argument('--output', type=Path, default=DATA/'native-lex-prefix-whole-call.json')
    replay = sub.add_parser('check')
    replay.add_argument('--input', type=Path, default=DATA/'native-lex-prefix-whole-call.json')
    replay.add_argument('--output', type=Path, default=DATA/'native-lex-prefix-whole-call-replay.json')
    args = parser.parse_args()
    try:
        record = run(args.output) if args.command == 'run' else check(args.input, args.output)
    except BaseException:
        if args.output.is_file():
            retained = json.loads(args.output.read_bytes())
            if retained.get('phase') == 'failed':
                print(json.dumps(summary(retained), sort_keys=True), flush=True)
        raise
    print(json.dumps(summary(record) if args.command == 'run' else record, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
