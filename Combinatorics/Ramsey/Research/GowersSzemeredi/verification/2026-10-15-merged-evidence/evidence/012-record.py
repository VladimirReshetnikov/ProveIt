"""Stage fresh all57 source maps and shared-member records in a new /tmp directory."""
from pathlib import Path
import argparse, datetime, functools, hashlib, json, os, re, sys
sys.dont_write_bytecode = True
if sys.flags.optimize: raise RuntimeError('Assertions must remain enabled')
TOOLS = Path('/tmp/gowers-merged-native-tools')
SNAPSHOT_SHA = 'ea073d3d780e82c569997118c70dbf880cee2d437ddd8e05e10119e4c602256a'
GUARD_SHA = '59675ea063b9809e2f9db1bf541698bc67a3b75493d85ace82b3c92fc52d692f'
CORE_RUNNER_SHA = 'fbec54638f6059d2eb8ee4174c101136f5b93385bc61ef9075a26b55b05bc9de'
SHARED_RUNNER = Path('/tmp/gowers-merged-shared-native-tools-v3/gowers_run_merged_shared_audits.py')
SHARED_RUNNER_SHA = '0bb00e6514b4638f769245872d6f52b3bcc6610d979339a4d44db77db6a1a388'
ATTEMPT_CHECKS = Path('/tmp/gowers-merged-shared-native-tools-v3/actual_attempt_checks.py')
ATTEMPT_CHECKS_SHA = '832e90738b753963b9ffa0d3fe6cf57ee7a9f52aedd01db2f3adbdd23982bb44'
DEST = 'Combinatorics/Ramsey/Research/GowersSzemeredi/verification/'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
encode = lambda v: (json.dumps(v, indent=2) + '\n').encode()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--shared-receipt', type=Path, required=True); p.add_argument('--shared-receipt-sha256', required=True)
    p.add_argument('--output-dir', type=Path, required=True); p.add_argument('--prefix', required=True)
    a = p.parse_args(); evidence = {}
    def load(path, expected):
        path = Path(path).resolve(); assert re.fullmatch('[0-9a-f]{64}', expected or '') and sha(path) == expected
        evidence[str(path)] = expected; return json.loads(path.read_text())
    snap = load(TOOLS / 'snapshot.json', SNAPSHOT_SHA); receipt = load(a.shared_receipt, a.shared_receipt_sha256)
    assert sha(TOOLS / 'guard.py') == GUARD_SHA and sha(SHARED_RUNNER) == SHARED_RUNNER_SHA
    evidence.update({str(TOOLS / 'guard.py'): GUARD_SHA, str(SHARED_RUNNER): SHARED_RUNNER_SHA})
    ns = {'__name__': 'merged_recorder_guard_library', '__file__': str(TOOLS / 'guard.py')}
    exec(compile((TOOLS / 'guard.py').read_bytes(), str(TOOLS / 'guard.py'), 'exec'), ns)
    R = ns['ROOT']; idle = ns['worker_check'](); source_commit = snap['source_commit']; graph = snap['graph']
    assert sha(ATTEMPT_CHECKS) == ATTEMPT_CHECKS_SHA; evidence[str(ATTEMPT_CHECKS)] = ATTEMPT_CHECKS_SHA; checks = {}
    exec(compile(ATTEMPT_CHECKS.read_bytes(), str(ATTEMPT_CHECKS), 'exec'), checks)
    def passed(value, mode, runner_sha, receipt_path):
        config = snap['modes'][mode]
        assert value['status'] == 'passed' and value['validation_mode'] == mode and value['source_commit'] == source_commit
        assert value['snapshot_path'] == str(TOOLS / 'snapshot.json') and value['snapshot_sha256'] == SNAPSHOT_SHA
        assert value['source_guard_sha256'] == GUARD_SHA and value['runner_sha256'] == runner_sha
        assert value['ordered_roots'] == config['roots'] and value['command'][1:] == [snap['checker'], *config['roots']]
        assert type(value['terminal_exit']) is int and value['terminal_exit'] == 0
        assert value['terminal_module_count'] == config['module_count'] and value['terminal_module_count_matches'] is True and value['contains_error_diagnostic'] is False
        assert value['source_guard_before'] == value['source_guard_after'] and value['source_and_evidence_stable'] is True and value['artifact_stability_verified'] is True
        assert set(value['artifacts_after']) == set(config['modules']) and all(x['fresh'] is True for x in value['artifacts_after'].values())
        assert value['native_source_repairs'] == snap['native_source_repairs'] == 1 and value['retained_historical_outcomes'] == 0 and value['per_root_native_outcomes_claimed'] is False
        log = Path(value['log']); assert sha(log) == value['log_sha256']; evidence[str(log)] = value['log_sha256']; text = log.read_text()
        assert re.findall(r'^Checked (\d+) modules \(including up-to-date dependencies\)\.$', text, re.M) == [str(config['module_count'])]
        assert text.rstrip().endswith(f"Checked {config['module_count']} modules (including up-to-date dependencies).") and not ns['error_diagnostic'](text)
        review = load(value['tools_review'], value['tools_review_sha256'])
        assert review['status'].startswith('PASS') and review['findings'] == [] and mode in review['approved_modes']
        assert review['snapshot_sha256'] == SNAPSHOT_SHA and review['guard_sha256'] == GUARD_SHA and review['runner_sha256'] == runner_sha
        assert ns['when'](value['started_at']) <= ns['when'](value['finished_at']) <= ns['when'](value['final_evidence_checked_at'])
        actual_pins = checks['validate_attempt'](receipt_path, value, snap, R); evidence.update(actual_pins); return actual_pins
    assert not (a.shared_receipt.parent / 'failure-after-receipt.json').exists(); shared_actual_pins = passed(receipt, 'shared', SHARED_RUNNER_SHA, a.shared_receipt)
    core_ref = receipt['core_receipt']; core = load(core_ref['path'], core_ref['sha256']); core_actual_pins = passed(core, 'core', CORE_RUNNER_SHA, core_ref['path'])
    assert receipt['core_attempt_evidence'] == core_actual_pins
    assert not (Path(core_ref['path']).parent / 'failure-after-receipt.json').exists()
    assert sha(TOOLS / 'gowers_run_merged_core_audits.py') == CORE_RUNNER_SHA; evidence[str(TOOLS / 'gowers_run_merged_core_audits.py')] = CORE_RUNNER_SHA
    assert ns['when'](core['final_evidence_checked_at']) <= ns['when'](receipt['started_at'])
    ns['committed'](source_commit, snap['protected_source_hashes']); ns['ancestor'](source_commit, ns['head']())
    current = {p: h for p, h in snap['protected_source_hashes'].items() if p != snap['inventory']}
    for path, h in current.items(): assert sha(R / path) == h
    stamps = {str(R / p): ns['stamp'](R / p) for p in current}; evidence_stamps = {p: ns['stamp'](p) for p in evidence}
    artifacts = ns['artifact_snapshot']([snap['modes']['shared']['modules']], graph)
    assert artifacts == receipt['artifacts_after']
    @functools.lru_cache(None)
    def closure(m): return frozenset({m}).union(*(closure(d) for d in graph[m] if d.split('.')[0] in ('GowersSzemeredi', 'OAI')))
    assert re.fullmatch(r'\d{4}-\d{2}-\d{2}-[a-z0-9-]+', a.prefix)
    index_name = a.prefix + '-index.json'; index_path = DEST + index_name
    outputs = {}; records = []; named = {r['target']: r for r in snap['named_scopes']}
    for row in snap['own_rows']:
        target = row['target']; modules = closure(target); i = row['selected_order']
        assert len(modules) == row['modules']
        own = {p: snap['selected_source_hashes'][p] for p in sorted({ns['module_path'](m) for m in modules} | set(snap['configs']))}
        assert len(own) == row['inputs'] and sum(len((R / ns['module_path'](m)).read_bytes().splitlines()) for m in modules) == row['source_lines']
        stem = a.prefix + f'-{i:02d}-' + target.rsplit('.', 1)[-1]; map_name = stem + '-inputs.json'; record_name = stem + '.json'
        outputs[map_name] = encode(own); map_sha = hashlib.sha256(outputs[map_name]).hexdigest()
        record = {'date': receipt['finished_at'][:10], 'status': 'passed', 'target': target, 'selected_order': i, 'shared_root_position': i,
                  'validation_mode': 'shared_invocation_member', 'shared_evidence_index': index_path, 'fresh_native_result': True,
                  'source_commit': source_commit, 'own_root_counts_are_closure_metadata': True, 'per_root_native_outcomes_claimed': False,
                  'own_closure_module_count': row['modules'], 'own_source_input_count': row['inputs'], 'own_source_lines': row['source_lines'],
                  'source_inputs': DEST + map_name, 'input_manifest_sha256': map_sha,
                  'own_native_artifact_count_verified': len(modules), 'own_artifact_snapshot_sha256': hashlib.sha256(encode({m: artifacts[m] for m in sorted(modules)})).hexdigest(),
                  'artifact_evidence': 'source/dependency freshness and mtime_ns/size stability; no content-hash claim',
                  'verification_kind': 'named approved-axiom audit in the shared invocation' if target in named else 'Lean module and dependency closure in the shared invocation'}
        if target in named:
            scope = named[target]; record.update(named_check_provider=scope['provider'], named_declarations=scope['names'], named_declaration_count=scope['count'], approved_axioms=scope['approved_axioms'])
        record['scope'] = 'Shared native command membership and own closure metadata. Named audits cover only the listed declarations, not every export or complete original-paper fidelity.'
        outputs[record_name] = encode(record)
        records.append({'target': target, 'record': DEST + record_name, 'record_sha256': hashlib.sha256(outputs[record_name]).hexdigest(), 'source_inputs': DEST + map_name, 'source_inputs_sha256': map_sha})
    index = {'schema_version': 1, 'status': 'passed', 'source_commit': source_commit, 'validation_mode': 'one_shared_invocation_all57_fresh',
             'command': receipt['command'], 'ordered_roots': receipt['ordered_roots'], 'terminal_exit': receipt['terminal_exit'],
             'terminal_exit_scope': 'one shared command; no individual root exits observed', 'terminal_module_count': receipt['terminal_module_count'],
             'started_at': receipt['started_at'], 'finished_at': receipt['finished_at'], 'shared_receipt': {'path': str(a.shared_receipt.resolve()), 'sha256': a.shared_receipt_sha256},
             'shared_log': {'path': receipt['log'], 'sha256': receipt['log_sha256']}, 'core_receipt': core_ref, 'core_terminal_module_count': core['terminal_module_count'],
             'attempt_evidence': {'core': core_actual_pins, 'shared': shared_actual_pins},
             'snapshot': {'path': str(TOOLS / 'snapshot.json'), 'sha256': SNAPSHOT_SHA}, 'guard_sha256': GUARD_SHA, 'shared_runner_sha256': SHARED_RUNNER_SHA,
             'tools_review': {'path': receipt['tools_review'], 'sha256': receipt['tools_review_sha256']},
             'own_root_counts_are_closure_metadata': True, 'retained_historical_outcomes': 0, 'fresh_root_count': len(records),
             'native_source_repairs': snap['native_source_repairs'], 'original_source_commit': snap['original_source_commit'], 'repaired_source_commit': snap['repaired_source_commit'],
             'incoming_main_commit': snap['incoming_main_commit'], 'failed_original_core': snap['failed_original_core'],
             'native_inventory_sha256': snap['protected_source_hashes'][snap['inventory']], 'inventory_in_own_source_maps': False,
             'named_scope_counts': {r['target']: r['count'] for r in snap['named_scopes']}, 'records': records,
             'scope': 'Fresh validation of all57 selected roots on the merged source. Individual source-map sizes are closure metadata; the actual shared footer counts their1904-module union. Original-paper fidelity limitations remain unchanged.'}
    assert len(records) == 57 and len(outputs) == 114; outputs[index_name] = encode(index)
    output = a.output_dir
    assert output.is_absolute() and output.resolve().is_relative_to(Path('/tmp')) and output.parent.is_dir() and not output.exists()
    for path, h in evidence.items(): assert sha(path) == h
    ns['freeze_check'](stamps); ns['freeze_check'](evidence_stamps); assert ns['worker_check']() == idle
    assert ns['artifact_snapshot']([snap['modes']['shared']['modules']], graph) == artifacts
    output.mkdir(exist_ok=False)
    for name, data in outputs.items():
        with (output / name).open('xb') as out: out.write(data); out.flush(); os.fsync(out.fileno())
        (output / name).chmod(0o444)
    manifest = {'status': 'staged only; repository unmodified', 'staged_at': now(), 'source_commit': source_commit, 'shared_receipt_sha256': a.shared_receipt_sha256, 'files': {DEST + name: hashlib.sha256(data).hexdigest() for name, data in outputs.items()}, 'index': index_path}
    with (output / 'staging-manifest.json').open('xb') as out: out.write(encode(manifest))
    (output / 'staging-manifest.json').chmod(0o444)
    print(json.dumps({'status': manifest['status'], 'output_dir': str(output), 'record_count': len(records), 'file_count': len(outputs), 'manifest_sha256': sha(output / 'staging-manifest.json')}, indent=2))
if __name__ == '__main__': main()
