"""Copy validated merged-checkpoint evidence into new /tmp staging; never publish or run Lean."""
from pathlib import Path
import argparse, functools, hashlib, json, os, re, sys
sys.dont_write_bytecode = True
if sys.flags.optimize: raise RuntimeError('Assertions must remain enabled')
NOTE = Path('/tmp/gowers-merged-publication-durable-evidence-note-v2.json')
NOTE_SHA = '0a3593ca89b97f35be378e7164c278377f8038ff0f6111ee7c6d27b9e4243663'
BASE = Path('/tmp/gowers-merged-native-tools')
SUP = Path('/tmp/gowers-merged-supplemental-native-tools')
DEST = 'Combinatorics/Ramsey/Research/GowersSzemeredi/verification/'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
encode = lambda v: (json.dumps(v, indent=2) + '\n').encode()
equal = lambda a, b: json.dumps(a, sort_keys=True) == json.dumps(b, sort_keys=True)
def new_file(path, data):
    with path.open('xb') as out: out.write(data); out.flush(); os.fsync(out.fileno())
    path.chmod(0o444)
def main():
    p = argparse.ArgumentParser(description=__doc__)
    for name in ('core-receipt', 'shared-receipt', 'supplemental-receipt', 'recorder-manifest'):
        p.add_argument('--' + name, nargs=2, metavar=('PATH', 'SHA256'), required=True)
    p.add_argument('--inventory-file', nargs=2, action='append', default=[], metavar=('PATH', 'SHA256'))
    p.add_argument('--output-dir', type=Path, required=True); p.add_argument('--stage', action='store_true')
    a = p.parse_args(); cache = {}; roles = {}; observed = {}
    def read(path, expected=None, role=None):
        path = Path(path); assert path.is_absolute() and path == path.resolve(strict=True) and path.is_file()
        data = path.read_bytes(); h = hashlib.sha256(data).hexdigest()
        if expected is not None: assert re.fullmatch('[0-9a-f]{64}', expected or '') and h == expected, str(path)
        if str(path) in cache: assert cache[str(path)] == data
        cache[str(path)] = data; observed[str(path)] = h
        if role is not None: roles.setdefault(str(path), []).append(role)
        return data
    def load(path, expected=None, role=None): return json.loads(read(path, expected, role))
    note = load(NOTE, NOTE_SHA, 'archive recommendation')
    for group, rows in note['known_files_to_copy_once'].items():
        for row in rows: read(row['original_path'], row['sha256'], group)
    snap = load(BASE / 'snapshot.json'); sup = load(SUP / 'snapshot.json')
    ns = {'__name__': 'evidence_staging_guard_library', '__file__': str(BASE / 'guard.py')}
    exec(compile(cache[str(BASE / 'guard.py')], str(BASE / 'guard.py'), 'exec'), ns)
    root = ns['ROOT']; source = snap['source_commit']; head = ns['head'](); idle = ns['worker_check']()
    assert sup['source_commit'] == source and sup['base_snapshot']['sha256'] == sha(BASE / 'snapshot.json')
    assert sup['protected_source_hashes'] == {**snap['protected_source_hashes'], **sup['extra_source_hashes']}
    assert len(sup['protected_source_hashes']) == 1969 and len(snap['protected_source_hashes']) == 1911
    ns['committed'](source, sup['protected_source_hashes']); ns['ancestor'](source, head)
    current = {p: h for p, h in sup['protected_source_hashes'].items() if p != snap['inventory']}
    for path, h in current.items(): assert sha(root / path) == h, path
    inventory_sha = sha(root / snap['inventory']); inventory_files = []
    for path, h in a.inventory_file:
        read(path, h, 'explicit inventory evidence; archival only'); inventory_files.append({'path': path, 'sha256': h})
    if inventory_sha != snap['protected_source_hashes'][snap['inventory']]:
        assert any(x['sha256'] == inventory_sha for x in inventory_files), 'Changed current inventory needs an explicit matching evidence file'
    source_stamps = {str(root / path): ns['stamp'](root / path) for path in sup['protected_source_hashes']}
    reviews = {}; events = {}
    def attempt(ref, mode, config, snapshot_path, guard_path, runner_path, protected, evidence_paths):
        path, expected = ref; receipt_path = Path(path); value = load(path, expected, mode + ' receipt')
        assert receipt_path.name == 'receipt.json' and not (receipt_path.parent / 'failure-after-receipt.json').exists()
        assert value['status'] == 'passed' and value['validation_mode'] == mode and value['source_commit'] == source
        assert value['snapshot_path'] == str(snapshot_path) and value['snapshot_sha256'] == sha(snapshot_path)
        assert value['source_guard_sha256'] == sha(guard_path) and value['runner_sha256'] == sha(runner_path)
        assert value['ordered_roots'] == config['roots'] and value['command'][1:] == [snap['checker'], *config['roots']]
        assert isinstance(value['command'][0], str) and Path(value['command'][0]).is_absolute()
        assert type(value['terminal_exit']) is int and value['terminal_exit'] == 0
        assert type(value['terminal_module_count']) is int and value['terminal_module_count'] == config['module_count']
        assert value['terminal_module_count_matches'] is True and value['contains_error_diagnostic'] is False
        assert value['source_and_evidence_stable'] is True and value['artifact_stability_verified'] is True
        assert type(value['native_source_repairs']) is int and value['native_source_repairs'] == 1
        assert type(value['retained_historical_outcomes']) is int and value['retained_historical_outcomes'] == 0
        assert value['per_root_native_outcomes_claimed'] is False
        assert equal(value['source_guard_before'], value['source_guard_after']); g = value['source_guard_before']
        assert set(g) == {'snapshot_sha256', 'source_commit', 'mode', 'source_freeze', 'evidence_freeze', 'protected_paths', 'native_source_repairs'}
        assert g['snapshot_sha256'] == value['snapshot_sha256'] and g['source_commit'] == source and g['mode'] == mode
        assert type(g['protected_paths']) is int and g['protected_paths'] == len(protected)
        assert type(g['native_source_repairs']) is int and g['native_source_repairs'] == 1
        assert set(g['source_freeze']) == {str(root / x) for x in protected} and set(g['evidence_freeze']) == set(evidence_paths)
        assert all(isinstance(s, list) and len(s) == 5 and all(type(x) is int and x >= 0 for x in s) for d in ('source_freeze', 'evidence_freeze') for s in g[d].values())
        for key in ('expected_modules', 'expected_inputs', 'expected_source_lines'):
            field = {'expected_modules': 'module_count', 'expected_inputs': 'input_count', 'expected_source_lines': 'source_lines'}[key]
            assert type(value[key]) is int and value[key] == config[field]
        log = receipt_path.parent / 'native.log'; assert value['log'] == str(log)
        text = read(log, value['log_sha256'], mode + ' log').decode(); footer = f"Checked {config['module_count']} modules (including up-to-date dependencies)."
        assert re.findall(r'^Checked (\d+) modules \(including up-to-date dependencies\)\.$', text, re.M) == [str(config['module_count'])]
        assert text.rstrip().endswith(footer) and not ns['error_diagnostic'](text)
        review = load(value['tools_review'], value['tools_review_sha256'], mode + ' actual launch review'); reviews[mode] = {'path': value['tools_review'], 'sha256': value['tools_review_sha256']}
        assert review['status'].startswith('PASS') and review['findings'] == [] and mode in review['approved_modes']
        for key, expected_value in [('snapshot_path', str(snapshot_path)), ('snapshot_sha256', sha(snapshot_path)), ('guard_path', str(guard_path)), ('guard_sha256', sha(guard_path)), ('runner_path', str(runner_path)), ('runner_sha256', sha(runner_path))]: assert review[key] == expected_value
        started = load(receipt_path.parent / 'started.json', role=mode + ' started'); expected_start = dict(value); expected_start.pop('final_evidence_checked_at')
        expected_start.update(status='running', finished_at=None, terminal_exit=None, terminal_module_count=None, terminal_module_count_matches=False, contains_error_diagnostic=None, log_sha256=None, source_guard_after=None, artifacts_after=None, source_and_evidence_stable=False, artifact_stability_verified=False)
        assert equal(started, expected_start)
        terminal = load(receipt_path.parent / 'terminal.json', role=mode + ' terminal')
        assert equal(terminal, {k: value[k] for k in ('command', 'started_at', 'finished_at', 'terminal_exit', 'terminal_module_count', 'terminal_module_count_matches', 'contains_error_diagnostic', 'log', 'log_sha256')})
        launched = load(receipt_path.parent / 'launched.json', role=mode + ' launched')
        assert set(launched) == {'pid', 'command', 'cwd', 'observed_at'} and type(launched['pid']) is int and launched['pid'] > 0
        assert launched['command'] == value['command'] and launched['cwd'] == str(root)
        assert ns['when'](value['started_at']) <= ns['when'](launched['observed_at']) <= ns['when'](value['finished_at']) <= ns['when'](value['final_evidence_checked_at'])
        modules = config['modules'] if mode != 'supplemental' else sup['combined_modules']
        assert set(value['artifacts_after']) == set(modules)
        assert all(set(x) == {'mtime_ns', 'size', 'fresh'} and type(x['mtime_ns']) is int and x['mtime_ns'] >= 0 and type(x['size']) is int and x['size'] >= 0 and x['fresh'] is True for x in value['artifacts_after'].values())
        events[mode] = {str(receipt_path.parent / n): observed[str(receipt_path.parent / n)] for n in ('started.json', 'launched.json', 'terminal.json')}
        return value
    base_evidence = [str(BASE / 'snapshot.json'), snap['historical_roots_source']['path'], snap['failed_original_core']['path']]
    core = attempt(a.core_receipt, 'core', snap['modes']['core'], BASE / 'snapshot.json', BASE / 'guard.py', BASE / 'gowers_run_merged_core_audits.py', snap['protected_source_hashes'], base_evidence)
    shared = attempt(a.shared_receipt, 'shared', snap['modes']['shared'], BASE / 'snapshot.json', BASE / 'guard.py', Path('/tmp/gowers-merged-shared-native-tools-v3/gowers_run_merged_shared_audits.py'), snap['protected_source_hashes'], base_evidence)
    supplemental = attempt(a.supplemental_receipt, 'supplemental', sup, SUP / 'snapshot.json', SUP / 'guard.py', SUP / 'gowers_run_merged_supplemental_audits.py', sup['protected_source_hashes'], [*base_evidence, str(SUP / 'snapshot.json'), sup['coverage_analysis']['path']])
    cref = {'path': a.core_receipt[0], 'sha256': a.core_receipt[1]}; sref = {'path': a.shared_receipt[0], 'sha256': a.shared_receipt[1]}
    assert equal(shared['core_receipt'], cref) and equal(shared['core_attempt_evidence'], events['core'])
    assert equal(supplemental['core_prerequisite'], cref) and equal(supplemental['shared_prerequisite'], sref)
    assert equal(supplemental['prior_attempt_evidence'], {'core': events['core'], 'shared': events['shared']})
    assert ns['when'](core['final_evidence_checked_at']) <= ns['when'](shared['started_at']) and ns['when'](shared['final_evidence_checked_at']) <= ns['when'](supplemental['started_at'])
    assert equal(supplemental['prior_selected_artifacts'], shared['artifacts_after'])
    assert all(equal(supplemental['artifacts_after'][m], x) for m, x in shared['artifacts_after'].items())
    assert supplemental['combined_artifact_count'] == sup['combined_module_count'] == 1962
    artifacts = ns['artifact_snapshot']([sup['combined_modules']], sup['graph']); assert equal(artifacts, supplemental['artifacts_after'])
    manifest_path, mh = a.recorder_manifest; manifest_path = Path(manifest_path)
    manifest = load(manifest_path, mh, 'approved recorder staging manifest')
    assert manifest_path.name == 'staging-manifest.json' and manifest['status'] == 'staged only; repository unmodified'
    assert manifest['source_commit'] == source and manifest['shared_receipt_sha256'] == a.shared_receipt[1] and len(manifest['files']) == 115
    assert ns['when'](shared['final_evidence_checked_at']) <= ns['when'](manifest['staged_at'])
    staged = {}
    for dest, h in manifest['files'].items():
        assert str(Path(dest).parent) + '/' == DEST
        staged[dest] = load(manifest_path.parent / Path(dest).name, h)
    assert manifest['index'] in staged; index = staged[manifest['index']]
    assert index['status'] == 'passed' and index['source_commit'] == source and index['validation_mode'] == 'one_shared_invocation_all57_fresh'
    assert equal(index['shared_receipt'], sref) and equal(index['core_receipt'], cref)
    assert equal(index['attempt_evidence'], {'core': events['core'], 'shared': events['shared']}) and equal(index['tools_review'], reviews['shared'])
    for key in ('command', 'ordered_roots', 'terminal_exit', 'terminal_module_count', 'started_at', 'finished_at'): assert equal(index[key], shared[key])
    assert index['fresh_root_count'] == len(index['records']) == 57 and index['retained_historical_outcomes'] == 0
    assert index['native_source_repairs'] == 1 and index['native_inventory_sha256'] == snap['protected_source_hashes'][snap['inventory']]
    assert index['own_root_counts_are_closure_metadata'] is True and index['inventory_in_own_source_maps'] is False
    assert equal(index['snapshot'], {'path': str(BASE / 'snapshot.json'), 'sha256': sha(BASE / 'snapshot.json')})
    assert equal(index['shared_log'], {'path': shared['log'], 'sha256': shared['log_sha256']})
    @functools.lru_cache(None)
    def closure(m): return frozenset({m}).union(*(closure(x) for x in snap['graph'][m] if x.split('.')[0] in ('GowersSzemeredi', 'OAI')))
    expected_files = {manifest['index']}; named = {x['target']: x for x in snap['named_scopes']}
    for row, links in zip(snap['own_rows'], index['records']):
        target = row['target']; assert links['target'] == target
        rp, mp = links['record'], links['source_inputs']; expected_files.update((rp, mp))
        assert links['record_sha256'] == manifest['files'][rp] and links['source_inputs_sha256'] == manifest['files'][mp]
        record, own = staged[rp], staged[mp]; modules = closure(target)
        expected = {path: snap['selected_source_hashes'][path] for path in sorted({ns['module_path'](m) for m in modules} | set(snap['configs']))}
        assert equal(own, expected) and len(own) == row['inputs'] and len(modules) == row['modules']
        fields = {'status': 'passed', 'target': target, 'source_commit': source, 'validation_mode': 'shared_invocation_member', 'shared_evidence_index': manifest['index'], 'selected_order': row['selected_order'], 'shared_root_position': row['selected_order'], 'fresh_native_result': True, 'own_root_counts_are_closure_metadata': True, 'per_root_native_outcomes_claimed': False, 'source_inputs': mp, 'input_manifest_sha256': manifest['files'][mp], 'own_closure_module_count': row['modules'], 'own_source_input_count': row['inputs'], 'own_source_lines': row['source_lines'], 'own_native_artifact_count_verified': len(modules)}
        assert all(equal(record[k], v) for k, v in fields.items())
        own_artifacts = {m: shared['artifacts_after'][m] for m in sorted(modules)}
        assert record['own_artifact_snapshot_sha256'] == hashlib.sha256(encode(own_artifacts)).hexdigest()
        if target in named:
            sc = named[target]; assert record['named_check_provider'] == sc['provider'] and equal(record['named_declarations'], sc['names']) and record['named_declaration_count'] == sc['count'] and equal(record['approved_axioms'], sc['approved_axioms'])
        else: assert not any(k in record for k in ('named_declarations', 'named_declaration_count', 'named_check_provider', 'approved_axioms'))
    assert expected_files == set(staged)
    read(Path(__file__).resolve(), role='archive staging executable text')
    archived = {path: data for path, data in cache.items() if path in roles}
    file_rows = [{'original_path': path, 'archive_relative_path': f'evidence/{i:03d}-{Path(path).name}', 'sha256': observed[path], 'roles': roles[path]} for i, path in enumerate(archived, 1)]
    summary = {'status': 'staged only; repository unmodified', 'source_commit': source, 'observed_metadata_head': head, 'files': file_rows,
               'attempts': {'core': cref, 'shared57': sref, 'supplemental25': {'path': a.supplemental_receipt[0], 'sha256': a.supplemental_receipt[1]}}, 'actual_launch_reviews': reviews,
               'recorder_manifest': {'path': str(manifest_path), 'sha256': mh}, 'recorder_outputs': manifest['files'], 'shared_evidence_index': {'path': manifest['index'], 'sha256': manifest['files'][manifest['index']]},
               'observed_command_footers': {'core': 603, 'shared57': 1904, 'supplemental25': 437}, 'combined_module_union': 1962,
               'current_inventory_sha256': inventory_sha, 'native_inventory_sha256': snap['protected_source_hashes'][snap['inventory']], 'explicit_inventory_files': inventory_files,
               'scope': 'Byte-preserving evidence archive. Shared and supplemental are distinct actual commands; no per-root exits. Inventory files are archived as explicitly supplied, without a new semantic normalization approval. The 115 recorder outputs are verified in place and are not rewritten or duplicated here.'}
    def stable():
        for path, h in observed.items(): assert sha(path) == h, path
        ns['freeze_check'](source_stamps); assert ns['head']() == head and ns['worker_check']() == idle
        assert equal(ns['artifact_snapshot']([sup['combined_modules']], sup['graph']), artifacts)
        for ref in (a.core_receipt, a.shared_receipt, a.supplemental_receipt): assert not (Path(ref[0]).parent / 'failure-after-receipt.json').exists()
    stable(); out = a.output_dir
    assert out.is_absolute() and out == out.resolve() and out.is_relative_to(Path('/tmp')) and out.parent.is_dir() and not out.exists()
    if not a.stage:
        print(json.dumps({'status': 'PASS: read-only preflight; nothing copied', 'archive_file_count': len(file_rows), 'verified_recorder_files': 115, 'source_commit': source})); return
    out.mkdir(); completed = []
    try:
        (out / 'evidence').mkdir()
        for row in file_rows:
            target = out / row['archive_relative_path']; new_file(target, archived[row['original_path']]); assert sha(target) == row['sha256']; completed.append(row['archive_relative_path'])
        stable(); new_file(out / 'evidence-map.json', encode(summary))
    except BaseException as exc:
        name = 'failure-after-map.json' if (out / 'evidence-map.json').exists() else 'failure.json'
        new_file(out / name, encode({'status': 'failed staging; preserve this directory', 'failure_type': type(exc).__name__, 'failure_detail': str(exc), 'completed_copies': completed})); raise
    print(json.dumps({'status': summary['status'], 'output_dir': str(out), 'evidence_map_sha256': sha(out / 'evidence-map.json'), 'archive_file_count': len(file_rows)}))
if __name__ == '__main__': main()
