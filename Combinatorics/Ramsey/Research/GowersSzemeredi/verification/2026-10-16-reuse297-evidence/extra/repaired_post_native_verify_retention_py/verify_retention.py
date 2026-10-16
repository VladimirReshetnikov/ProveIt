"""Read-only final retention check; run only after all three native modes pass."""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
import argparse, functools, json
from common import *
from run import verify_prior

SOURCE = '6a753d0702d1691c25a21bdbdb58e29412931be5'
SNAPSHOT_SHA = 'e3f24c8ebfe20b2a248076497748ca1cbd2f2c1d5176e56ce45af9eebe6011b3'
ADDED_MODULES = {
    'GowersSzemeredi.Proofs05FullPartitionScale',
    'GowersSzemeredi.Proofs05ThresholdFreeCorollary58',
}
REVIEW = Path('/tmp/gowers-reuse135-seven-supplemental-retention-input-review.json')
REVIEW_SHA = '0ce8d9f986e2963fceb6c08c4c96193e9db4c5ca061fde0ee1cd4fe92e7e57dc'
HELPERS = {'common.py': '4c71aedd3ec630046fd5dd5d205e250893c93bb0b1f1d2b0faf69bfe89e07328',
           'run.py': 'bf1aa169ed14fc098fd20c57a93a8c9904718bfc2b2648997384a3effd61e83a'}
ARCHIVE = 'Combinatorics/Ramsey/Research/GowersSzemeredi/verification/2026-10-15-merged-evidence/evidence/'

def load(path): return json.loads(Path(path).read_text())
def chronology(values):
    times = [datetime.datetime.fromisoformat(v) for v in values]
    require(all(t.tzinfo is not None for t in times) and times == sorted(times), 'Event chronology mismatch')

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--snapshot', type=Path, required=True)
    p.add_argument('--final-receipt', type=Path, required=True)
    p.add_argument('--final-receipt-sha256', required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args(); base = Path(__file__).resolve().parent
    require(a.output.is_absolute() and a.output.resolve().is_relative_to(Path('/tmp')) and a.output.parent.is_dir() and not a.output.exists(), 'Use a NEW /tmp output file')
    protected = {str(base / n): h for n, h in HELPERS.items()}
    protected[str(Path(__file__).resolve())] = sha(__file__)
    protected[str(REVIEW)] = REVIEW_SHA
    protected[str(a.snapshot.resolve())] = SNAPSHOT_SHA
    for path, expected in protected.items(): require(sha(path) == expected, 'Input/helper pin mismatch: ' + path)
    snapshot = load(a.snapshot); root = Path(snapshot['root']); review = load(REVIEW)
    require(snapshot['source_commit'] == SOURCE, 'Wrong accepted source')
    require(set(snapshot['tools']) == {str(Path('/tmp/gowers-next297-native-tools') / n) for n in ('common.py', 'capture.py', 'run.py')}, 'Snapshot tool keyset mismatch')
    protected.update(snapshot['tools']); protected[snapshot['plan']['path']] = snapshot['plan']['sha256']
    for path, expected in protected.items(): require(sha(path) == expected, 'Tool/plan mismatch: ' + path)
    worker_check(root); guard = source_guard(snapshot)
    require([len(snapshot['modes'][m]['roots']) for m in ('core', 'shared', 'supplemental')] == [1, 58, 18], 'Unexpected current roots')
    require([snapshot['modes'][m]['module_count'] for m in ('core', 'shared', 'supplemental')] == [573, 1906, 351], 'Unexpected current closures')
    new_modules = set(snapshot['modes']['supplemental']['cumulative_modules'])
    require(len(new_modules) == 1955, 'Unexpected current union')
    require(ADDED_MODULES <= set(snapshot['graph']) and ADDED_MODULES <= new_modules, 'Required two added modules absent from current snapshot/native union')

    # Traverse actual receipt links; each verifier checks current artifacts,
    # source guards, exact events, terminal/log output and its own chronology.
    path = a.final_receipt.resolve(); digest = a.final_receipt_sha256
    receipts = {}; receipt_pins = {}
    for label in ('supplemental', 'shared', 'core'):
        r, pins = verify_prior(path, digest, snapshot, SNAPSHOT_SHA, label, guard)
        require(Path(r['snapshot_path']).resolve() == a.snapshot.resolve(), 'Receipt snapshot path mismatch')
        receipts[label] = r; receipt_pins[label] = {'path': str(path), 'sha256': digest}; protected.update(pins)
        if label != 'core':
            previous = r['previous_receipt']; require(set(previous) == {'path', 'sha256'}, 'Prior link shape mismatch')
            path = Path(previous['path']).resolve(); digest = previous['sha256']
        else: require(r['previous_receipt'] is None, 'Core is not a fresh-batch start')
    chronology([receipts['core']['recorded_at'], receipts['shared']['started_at'], receipts['shared']['recorded_at'], receipts['supplemental']['started_at']])
    final = receipts['supplemental']
    require(ADDED_MODULES <= set(final['artifacts_after']), 'Required two added modules absent from verified actual native receipt')

    # Historical evidence stays attributed to its one actual 25-root command.
    old_pins = review['published_evidence_pins']
    for path, expected in old_pins.items():
        require(sha(root / path) == expected, 'Published evidence mismatch: ' + path)
        protected[str(root / path)] = expected
    committed(root, review['published_checkpoint_commit'], old_pins)
    old = load(root / (ARCHIVE + '051-receipt.json'))
    old_snapshot = load(root / (ARCHIVE + '003-snapshot.json'))
    started = load(root / (ARCHIVE + '053-started.json'))
    launched = load(root / (ARCHIVE + '055-launched.json'))
    terminal = load(root / (ARCHIVE + '054-terminal.json'))
    log = root / (ARCHIVE + '052-native.log')
    expected_start = {k: v for k, v in old.items() if k != 'final_evidence_checked_at'}
    expected_start.update(status='running', finished_at=None, terminal_exit=None,
        terminal_module_count=None, terminal_module_count_matches=False,
        contains_error_diagnostic=None, log_sha256=None, source_guard_after=None,
        artifacts_after=None, source_and_evidence_stable=False, artifact_stability_verified=False)
    require(same(started, expected_start), 'Historical started event mismatch')
    require(set(launched) == {'pid', 'command', 'cwd', 'observed_at'} and type(launched['pid']) is int and launched['pid'] > 0, 'Historical launch shape mismatch')
    require(same(launched['command'], old['command']) and launched['cwd'] == str(root), 'Historical launch mismatch')
    derived_terminal = terminal_fields(old['command'], old['started_at'], old['finished_at'], old['terminal_exit'], log, 437)
    derived_terminal['log'] = old['log']  # Content comes from the pinned published copy.
    require(same(terminal, derived_terminal) and same(terminal, {k: old[k] for k in terminal}), 'Historical terminal/log mismatch')
    require(old['status'] == 'passed' and old['validation_mode'] == 'supplemental' and old['source_commit'] == review['historical_validated_source_commit'] == old_snapshot['source_commit'], 'Historical source/outcome mismatch')
    require(type(old['terminal_exit']) is int and old['terminal_exit'] == 0 and old['terminal_module_count_matches'] is True and old['contains_error_diagnostic'] is False, 'Historical native failure')
    require(old['source_and_evidence_stable'] is True and old['artifact_stability_verified'] is True, 'Historical stability failure')
    require(same(old['command'], review['historical_actual_command']['command']) and old['command'][1:] == [CHECKER, *old_snapshot['roots']] and same(old['ordered_roots'], old_snapshot['roots']), 'Historical command attribution mismatch')
    require(len(old_snapshot['roots']) == 25 and old['expected_modules'] == old_snapshot['module_count'] == 437 and old['expected_inputs'] == old_snapshot['input_count'] == 440 and old['expected_source_lines'] == old_snapshot['source_lines'], 'Historical invocation counts mismatch')
    require(old['snapshot_sha256'] == sha(root / (ARCHIVE + '003-snapshot.json')) and old['log_sha256'] == sha(log), 'Historical snapshot/log identity mismatch')
    chronology([old['started_at'], launched['observed_at'], old['finished_at'], old['final_evidence_checked_at'], receipts['core']['started_at']])
    old_guard = old['source_guard_before']
    require(set(old_guard) == {'snapshot_sha256', 'source_commit', 'mode', 'source_freeze', 'evidence_freeze', 'protected_paths', 'native_source_repairs'}, 'Historical guard keyset mismatch')
    require(same(old_guard, old['source_guard_after']) and old_guard['snapshot_sha256'] == old['snapshot_sha256'] and old_guard['source_commit'] == old['source_commit'] and old_guard['mode'] == 'supplemental', 'Historical guard identity mismatch')
    require(set(old_guard['source_freeze']) == {str(root / p) for p in old_snapshot['protected_source_hashes']} and type(old_guard['protected_paths']) is int and old_guard['protected_paths'] == len(old_guard['source_freeze']), 'Historical protected-source keyset mismatch')
    for values in list(old_guard['source_freeze'].values()) + list(old_guard['evidence_freeze'].values()):
        require(isinstance(values, list) and len(values) == 5 and all(type(v) is int for v in values), 'Historical file-stamp shape mismatch')
    old_graph = old_snapshot['graph']
    require(set(old_graph) == set(old_snapshot['combined_modules']) == set(old['artifacts_after']) and len(old_graph) == old['combined_artifact_count'] == 1962, 'Historical union mismatch')

    @functools.lru_cache(None)
    def closure(module):
        return frozenset({module}).union(*(closure(d) for d in old_graph[module] if local(d)))
    old_command_modules = set().union(*(closure(r) for r in old_snapshot['roots']))
    require(old_command_modules == set(old_snapshot['modules']) and len(old_command_modules) == 437, 'Historical command closure mismatch')
    scopes = review['retained_scope_candidates']; require(len(scopes) == 7, 'Expected seven scopes')
    retained = set(); inputs = {}; scope_metadata = []
    for scope in scopes:
        module = scope['root']; modules = set(closure(module)); retained.update(modules)
        expected_paths = {module_path(m) for m in modules} | set(CONFIGS)
        mapping = scope['own_input_map']; require(set(mapping) == expected_paths, 'Retained input keyset mismatch')
        require(hashlib.sha256((json.dumps(mapping, indent=2) + '\n').encode()).hexdigest() == scope['own_input_map_sha256'], 'Retained map digest mismatch')
        require(len(modules) == scope['own_module_count'] and len(mapping) == scope['own_input_count'], 'Retained closure count mismatch')
        require(sum(len((root / module_path(m)).read_text().splitlines()) for m in modules) == scope['own_source_lines'], 'Retained source-line count changed')
        require(old_snapshot['roots'].index(module) + 1 == scope['historical_shared_command_root_position'], 'Retained root attribution mismatch')
        for path, digest in mapping.items():
            require(old_snapshot['protected_source_hashes'][path] == digest and sha(root / path) == digest, 'Retained source changed: ' + path)
            require(path not in inputs or inputs[path] == digest, 'Conflicting retained input maps'); inputs[path] = digest
        scope_metadata.append({k: scope[k] for k in ('root', 'historical_shared_command_root_position', 'own_module_count', 'own_input_count', 'own_source_lines', 'own_input_map_sha256')})
    require(len(retained) == 125 and len(inputs) == 128, 'Retained union count mismatch')
    current_retained_graph = graph_for(root, [s['root'] for s in scopes])
    require(same(current_retained_graph, {m: old_graph[m] for m in sorted(retained)}), 'Retained imports changed')
    for commit in (review['historical_validated_source_commit'], review['published_checkpoint_commit'], SOURCE): committed(root, commit, inputs)
    overlap = retained & new_modules; outside = retained - new_modules
    require(len(overlap) == 116 and len(outside) == 9 and sorted(outside) == review['retained_union']['outside_new_native_scope_modules'], 'Retained overlap changed')
    require(ADDED_MODULES.isdisjoint(old_graph), 'Added modules already occur in historical union')
    require(new_modules | retained == set(old_graph) | ADDED_MODULES and len(new_modules | retained) == 1964, 'Combined current coverage differs from historical1962 union plus exactly the two added modules')
    for path, digest in inputs.items(): protected[str(root / path)] = digest
    for path, digest in snapshot['source_hashes'].items(): protected[str(root / path)] = digest
    for path, expected in protected.items(): require(sha(path) == expected, 'Protected input changed')
    stamps = {path: stamp(path) for path in protected}
    retained_snapshot = {'root': str(root), 'graph': old_graph}
    observed = artifacts(retained_snapshot, sorted(retained), True)
    require(all(same(observed[m], final['artifacts_after'][m]) for m in overlap), 'Overlapping retained artifacts differ from final new receipt')
    require(all(same(observed[m], old['artifacts_after'][m]) for m in outside), 'Outside retained artifacts differ from published historical receipt')
    worker_check(root); require(same(source_guard(snapshot), guard), 'Current source guard changed')
    require(same(artifacts(snapshot, sorted(new_modules), True), final['artifacts_after']), 'Current artifacts changed after receipt verification')
    require(same(artifacts(retained_snapshot, sorted(retained), True), observed), 'Retained artifacts changed during check')
    for path, expected in protected.items():
        require(stamp(path) == stamps[path] and sha(path) == expected, 'Protected input changed during final check')
    worker_check(root)
    report = {'status': 'PASS', 'checked_at': now(), 'source_commit': SOURCE,
        'snapshot': {'path': str(a.snapshot.resolve()), 'sha256': SNAPSHOT_SHA},
        'input_retention_review': {'path': str(REVIEW), 'sha256': REVIEW_SHA},
        'actual_new_native_receipts': receipt_pins,
        'historical_shared_invocation': {'receipt': str(root / (ARCHIVE + '051-receipt.json')),
            'receipt_sha256': sha(root / (ARCHIVE + '051-receipt.json')), 'command': old['command'],
            'terminal_exit': old['terminal_exit'], 'module_footer': old['terminal_module_count'],
            'started_at': old['started_at'], 'finished_at': old['finished_at'], 'roots': old_snapshot['roots']},
        'retained_scopes': scope_metadata, 'retained_input_hashes': dict(sorted(inputs.items())),
        'retained_artifacts': observed, 'overlap_with_new_receipt_modules': sorted(overlap),
        'outside_new_receipt_modules': sorted(outside),
        'coverage': {'new_native_union': 1955, 'retained_union': 125, 'retained_overlap': 116,
            'retained_outside': 9, 'combined_union': 1964, 'retained_unique_inputs': 128,
            'historical_union': 1962, 'added_native_modules': sorted(ADDED_MODULES)},
        'attribution': 'The seven retained roots belong to the historical single 25-root/437-module command. Their own closure counts are metadata; no seven new commands, root footers or root exits are claimed.',
        'checks': {'all_three_actual_new_modes_verified': True, 'historical_events_and_log_verified': True,
            'retained_sources_match_historical_publication_and_current_source': True, 'all125_retained_artifacts_fresh_and_stable': True,
            'overlap116_matches_new_final_receipt': True, 'outside9_matches_published_historical_receipt': True},
        'artifact_record_semantics': 'Native helper records freshness, mtime_ns and size; no separate artifact-content hashes are claimed.',
        'evidence_hashes': protected, 'native_commands_executed_by_this_verifier': 0}
    write_new(a.output, report)
    print(json.dumps({'status': 'PASS', 'output': str(a.output), 'sha256': sha(a.output)}))

if __name__ == '__main__': main()
