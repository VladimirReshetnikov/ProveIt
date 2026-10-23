#!/usr/bin/env python3
"""Independent read-only phase22 capture review. Never extracts or runs captured code.

Root must read this complete source before authorizing its first execution. The
final accepted result hash and every rejected run root are explicit CLI inputs.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import re
import tarfile

ROOT = Path('/home/codex/.codex/worktrees/ec20/Proofs')
PREVIOUS = ROOT / 'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase21/lean'
CORE = {'README.md', 'capture-config.json', 'capture.json', 'capture.py', 'check-plan.json', 'check.py', 'evidence.tar.gz', 'index.json', 'result-review.json', 'result.json', 'review_actual.py'}
FORBIDDEN = {'.olean', '.ilean', '.o', '.obj', '.a', '.so', '.dylib', '.dll', '.exe'}
BASIS_SHA = 'a2e1a93317cac5531d20fcf6724628004dff7d5fe67fb9ebd16b16cba9fbdd57'
PLAN_SHA = '76838519fc4b0faa756eedbe9dd1eab7ea500fc8130c5d4b69cc1435d7000070'
EXPECTED_COUNTS = {'providers': 226, 'projects': 211, 'typed_clients': 15, 'fresh': 56, 'reuses': 170, 'audits': 2, 'absences': 16}
CHANGED = {'BusyBeaver.ZFC.ConstructibleAbs', 'BusyBeaver.ZFC.ProfileSyntax', 'BusyBeaver.ZFC.CompositionModel', 'BusyBeaver.ZFC.L2Root219', 'BusyBeaver.ZFC.KLowerRaw', 'BusyBeaver.ZFC.KLowerTag', 'BusyBeaver.ZFC.KLowerQHyp', 'BusyBeaver.ZFC.KQ1Model', 'BusyBeaver.ZFC.KQ1Basic'}
MANDATORY_FAILED_ROOTS = {Path('/tmp/k215-phase22-check'), Path('/tmp/k215-phase22-check-v2')}
RETIRED = {}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def pin(path):
    path = Path(path)
    return {'path': str(path), 'sha256': digest(path), 'bytes': path.stat().st_size}


def profiles(text):
    return [[name, sorted(set(atom.strip() for atom in axioms.split(',') if atom.strip()))]
            for name, axioms in re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", text)]


def structured_profiles(reports):
    assert isinstance(reports, list)
    normalized = []
    known_atoms = {'Classical.choice', 'Quot.sound', 'propext'}
    for row in reports:
        assert isinstance(row, list) and len(row) == 2
        name, axioms = row
        assert isinstance(name, str) and name and name == name.strip()
        if isinstance(axioms, str):
            atoms = [] if not axioms.strip() else [atom.strip() for atom in axioms.split(',')]
        else:
            assert isinstance(axioms, list)
            atoms = axioms
        assert all(isinstance(atom, str) and atom in known_atoms for atom in atoms)
        normalized.append([name, sorted(set(atoms))])
    return normalized


def safe(name):
    path = PurePosixPath(name)
    assert name and not path.is_absolute() and '..' not in path.parts
    assert str(path) == name and '\\' not in name and '\x00' not in name
    assert path.suffix not in FORBIDDEN and 'objects' not in path.parts
    return name


def main():
    parser = argparse.ArgumentParser()
    for key in ['packet', 'config', 'output']:
        parser.add_argument('--' + key, type=Path, required=True)
    parser.add_argument('--config-sha', required=True)
    parser.add_argument('--capture-helper-sha', required=True)
    parser.add_argument('--expected-result-sha', required=True)
    parser.add_argument('--expected-failed-root', type=Path, action='append', required=True)
    args = parser.parse_args()
    assert not args.output.exists() and not args.output.is_symlink()
    for value in [args.config_sha, args.capture_helper_sha, args.expected_result_sha]:
        assert re.fullmatch(r'[0-9a-f]{64}', value)
    failed_roots = [path.absolute() for path in args.expected_failed_root]
    assert len(failed_roots) == len(set(failed_roots))
    assert set(failed_roots) == MANDATORY_FAILED_ROOTS
    assert digest(args.config) == args.config_sha
    cfg = read(args.config)
    index = read(args.packet / 'index.json')
    capture = read(args.packet / 'capture.json')
    archive = args.packet / 'evidence.tar.gz'
    assert cfg['status'] == 'FROZEN_FOR_CAPTURE_AFTER_ACTUAL_PASS'
    assert cfg['expected_counts'] == EXPECTED_COUNTS
    assert capture['status'] == 'PASS_DETERMINISTIC_CAPTURE_AND_MEMBER_HASH_VERIFICATION'
    assert capture['config_sha256'] == args.config_sha
    assert cfg['capture_helper_sha256'] == capture['capture_helper_sha256'] == args.capture_helper_sha
    assert digest(archive) == index['archive_sha256'] == capture['archive_sha256']
    assert digest(args.packet / 'index.json') == capture['index_sha256']
    assert archive.stat().st_size == capture['archive_bytes']
    assert not capture['compiler_execution'] and not capture['supplied_code_execution'] and not capture['objects_copied']
    assert capture['current_runs'] == 1 and set(cfg['runs']) == {'candidate'}
    assert capture['preserved_failed_contexts'] == len(cfg['failed_contexts']) == len(failed_roots)
    raw = read(cfg['raw_copy_plan']['source'])
    assert digest(cfg['raw_copy_plan']['source']) == cfg['raw_copy_plan']['sha256']
    assert raw['status'] == 'DRAFT_COPY_PLAN_NO_MUTATION'
    assert raw['current_accepted_runs'] == 1 and raw['preserved_failed_context_count'] == len(failed_roots)
    expected_raw, historical, logical, sources, blobs, pins = {}, {}, {}, {}, {}, {}

    def require(source, destination, role, expected_hash=None, old_source=None):
        source = Path(source)
        safe(destination)
        assert destination not in expected_raw
        row = {'source': str(source), 'sha256': expected_hash or digest(source), 'destination': destination, 'bytes': source.stat().st_size, 'role': role}
        if old_source is not None:
            row['historical_source'] = old_source
        expected_raw[destination] = row

    def run_files(directory, paths, prefix, accepted):
        receipt_role = 'accepted_candidate_receipt' if accepted else 'preserved_unaccepted_run_receipt'
        for key, row in paths.items():
            if key != 'workspace':
                require(row['source'], prefix + '/receipts/' + key + Path(row['source']).suffix, receipt_role, row['sha256'])
        known = {row['source'] for key, row in paths.items() if key != 'workspace'}
        for key in ['before', 'inventory', 'completed', 'toolchain']:
            source = directory / (key + '.json')
            if source.is_file() and str(source) not in known:
                require(source, prefix + '/receipts/' + source.name, receipt_role)
        plan = read(paths['plan']['source'])
        rows = {row['module']: row for row in plan['modules']}
        assert len(rows) == len(plan['modules'])
        workspace = directory / 'workspace'
        actual_workspace = set()
        for source in sorted(workspace.rglob('*.lean')):
            relative = source.relative_to(workspace)
            module = '.'.join(relative.with_suffix('').parts)
            row = rows[module]
            assert digest(source) == row['source_sha256']
            require(source, prefix + '/workspace/' + relative.as_posix(), 'accepted_workspace_source' if accepted else 'preserved_unaccepted_workspace_source', row['source_sha256'], row['source'])
            actual_workspace.add(module)
            if accepted:
                historical[str(source)] = row['source']
        if accepted:
            assert actual_workspace == set(rows) and len(actual_workspace) == 226
        for source in sorted((directory / 'attempts').rglob('*')):
            if source.is_file():
                assert source.name in ['compiler.log', 'record.json', 'assumption-profile-discrepancy.json'] or source.suffix == '.lean'
                require(source, prefix + '/attempts/' + source.relative_to(directory / 'attempts').as_posix(), 'accepted_current_attempt_evidence' if accepted else 'preserved_unaccepted_attempt_evidence')
        for audit in sorted(directory.glob('audit-*')):
            for source in sorted(audit.iterdir()):
                if source.is_file() and source.suffix != '.olean':
                    assert source.name in ['compiler.log', 'record.json', 'assumption-profile-discrepancy.json'] or source.suffix == '.lean'
                    require(source, prefix + '/' + audit.name + '/' + source.name, 'accepted_endpoint_audit_evidence' if accepted else 'preserved_unaccepted_audit_evidence')

    def verify_outer(root, paths, accepted):
        outer = read(paths['outer']['source'])
        argv = outer['argv']
        assert argv[:2] == ['python3', '-B'] and argv[3] == '--map' and argv[5] == '--out' and len(argv) == 7
        assert Path(argv[6]) == root / 'candidate-build-run1'
        assert argv[2] == paths['runner']['source'] and argv[4] == paths['plan']['source']
        assert (outer['status'] == 'PASS_EXIT_ZERO' and outer['exit_code'] == 0) if accepted else (outer['status'] != 'PASS_EXIT_ZERO' and outer['exit_code'] != 0)
        for key, hash_key in [('stdout', 'stdout_sha256'), ('stderr', 'stderr_sha256'), ('freeze', 'freeze_sha256'), ('launcher', 'launcher_sha256')]:
            assert digest(paths[key]['source']) == paths[key]['sha256'] == outer[hash_key]
        return outer

    run = cfg['runs']['candidate']
    assert set(run) == {'workspace', 'plan', 'runner', 'result', 'inventory', 'completed', 'before', 'toolchain', 'stdout', 'stderr', 'outer', 'freeze', 'launcher'}
    directory = Path(run['result']['source']).parent
    accepted_root = directory.parent
    assert directory == accepted_root / 'candidate-build-run1' and accepted_root not in failed_roots
    assert run['workspace'] == str(directory / 'workspace')
    verify_outer(accepted_root, run, True)
    run_files(directory, run, 'candidate', True)
    plan = read(run['plan']['source'])
    result = read(run['result']['source'])
    done = read(run['completed']['source'])
    before = read(run['before']['source'])
    assert digest(run['result']['source']) == args.expected_result_sha
    assert digest(run['plan']['source']) == PLAN_SHA
    assert result['status'] == 'PASS' and result['provider_count'] == len(plan['modules']) == len(done) == 226
    assert (len(result['fresh_modules']), len(result['reused_modules']), len(result['audits'])) == (56, 170, 2)
    assert len(set(result['fresh_modules'])) == 56 and len(set(result['reused_modules'])) == 170
    assert set(result['fresh_modules']).isdisjoint(result['reused_modules'])
    assert set(result['fresh_modules']) | set(result['reused_modules']) == set(done)
    assert result['basis_result_sha256'] == BASIS_SHA == digest(PREVIOUS / 'result.json')
    assert result['map_sha256'] == before['plan_sha256'] == run['plan']['sha256']
    assert result['runner_sha256'] == before['runner_sha256'] == run['runner']['sha256']
    assert result['inventory_sha256'] == run['inventory']['sha256'] and result['completed_sha256'] == run['completed']['sha256']
    assert result['source_transitive_reuse_only'] and result['all_source_object_dependency_log_toolchain_inputs_postchecked']
    expected = plan['expected']
    assert (expected['provider_count'], expected['project_count'], expected['typed_client_count']) == (226, 211, 15)
    assert set(expected['changed_sources']) == CHANGED
    assert set(expected['fresh_by_source_transitivity']) == set(result['fresh_modules'])
    assert set(expected['affected_typed_clients']) == {'DirectSeed17Api', 'ProfileTC14Api', 'QuotientSharing15Api', 'QuotientUnified16Api', 'WFModelCompat12', 'ZFNativeCompat12'}
    assert set(expected['affected_typed_clients']).issubset(result['fresh_modules'])
    profile_log_pins = {}
    for row in plan['modules']:
        record = done[row['module']]
        assert digest(record['log']) == record['log_sha256']
        assert profiles(Path(record['log']).read_text()) == row['expected_reports']
        profile_log_pins[record['log']] = record['log_sha256']
        if 'reports' in record:
            assert structured_profiles(record['reports']) == row['expected_reports']

    for i, (context, root) in enumerate(zip(cfg['failed_contexts'], failed_roots), 1):
        assert context['name'] == 'failed-' + str(i) and context['accepted_as_current_result'] is False
        assert Path(context['outer']['source']) == root / 'candidate-build-outer.json'
        outer = read(context['outer']['source'])
        failed = Path(outer['argv'][6])
        assert failed == root / 'candidate-build-run1' and not (failed / 'result.json').exists()
        freezes = [path for path in root.glob('freeze*.json') if digest(path) == outer['freeze_sha256']]
        assert len(freezes) == 1
        local_paths = {'plan': Path(outer['argv'][4]), 'runner': Path(outer['argv'][2]), 'outer': root / 'candidate-build-outer.json', 'stdout': root / 'candidate-build.stdout', 'stderr': root / 'candidate-build.stderr', 'freeze': freezes[0], 'launcher': root / 'run_once.py'}
        paths = {key: {'source': str(path), 'sha256': digest(path)} for key, path in local_paths.items()}
        assert verify_outer(root, paths, False)['status'] == context['terminal_status']
        assert paths['runner']['sha256'] == run['runner']['sha256']
        run_files(failed, paths, context['name'], False)
        reconstructed = [row for name, row in expected_raw.items() if name.startswith(context['name'] + '/')]
        assert len(context['files']) == len(reconstructed)
        assert sorted((row['source'], row['sha256']) for row in context['files']) == sorted((row['source'], row['sha256']) for row in reconstructed)
    assert len(raw['files']) == len(expected_raw)
    assert {row['destination']: row for row in raw['files']} == expected_raw

    def expect(row, name, role, external=False):
        safe(name)
        assert name not in logical
        path = Path(row['source'])
        assert path.is_absolute() and '..' not in path.parts and path.is_file() and not path.is_symlink()
        assert path.suffix not in FORBIDDEN and 'objects' not in path.parts
        content = path.read_bytes()
        hashed = hashlib.sha256(content).hexdigest()
        assert hashed == row['sha256']
        pins[str(path)] = hashed
        item = {'source': str(path), 'sha256': hashed, 'bytes': len(content), 'role': role}
        if 'historical_source' in row:
            item['historical_source'] = row['historical_source']
        if external:
            item['external'] = True
        else:
            assert not path.is_relative_to(PREVIOUS) and not str(path).endswith(('.tar', '.tar.gz', '.tgz', '.zip'))
            item['blob'] = 'blobs/' + hashed
            blobs[hashed] = content
        logical[name] = item
        alias = sources.setdefault(str(path), {'sha256': hashed, 'bytes': len(content), 'external': external, 'logical': []})
        assert (alias['sha256'], alias['bytes'], alias['external']) == (hashed, len(content), external)
        alias['logical'].append(name)

    for row in raw['files']:
        item = dict(row)
        if item['source'] in historical:
            item['historical_source'] = historical[item['source']]
        expect(item, 'runtime/' + safe(item['destination']), item.get('role', 'accepted_candidate_raw'))
        assert logical['runtime/' + item['destination']]['bytes'] == item['bytes']
    for row in cfg['files']:
        expect(row, row['logical'], row['role'])
    assert len(cfg['external_boundaries']) == 11
    assert {row['source'] for row in cfg['external_boundaries']} == {str(PREVIOUS / name) for name in CORE}
    for row in cfg['external_boundaries']:
        expect(row, row['logical'], 'exact_phase21_leaf_boundary', True)
    for key, name in [('actual_review', 'capture/actual-review.json'), ('actual_review_helper', 'capture/review_actual.py'), ('raw_copy_plan', 'capture/raw-copy-plan.json')]:
        expect(cfg[key], name, key)
    expect({'source': index['logical']['capture/capture.py']['source'], 'sha256': args.capture_helper_sha}, 'capture/capture.py', 'owned_capture_helper')
    expect({'source': str(args.config.absolute()), 'sha256': args.config_sha}, 'capture/config.json', 'owned_capture_config')
    for alias in sources.values():
        alias['logical'].sort()
    assert index['format'] == 'phase22-explicit-evidence-blobs-v1'
    assert index['logical'] == logical and index['sources'] == sources
    assert index['external_boundaries'] == {row['source']: row['sha256'] for row in cfg['external_boundaries']}
    assert (len(blobs), len(logical), len(sources), len(raw['files'])) == (capture['blob_members'], capture['logical_entries'], capture['source_aliases'], capture['raw_plan_files'])
    assert capture['external_boundary_files'] == 11
    assert archive.read_bytes()[:8] == bytes([31, 139, 8, 0, 0, 0, 0, 0])
    with tarfile.open(archive, 'r:gz') as tar:
        members = tar.getmembers()
        assert [member.name for member in members] == sorted('blobs/' + hashed for hashed in blobs)
        for member in members:
            assert re.fullmatch(r'blobs/[0-9a-f]{64}', member.name) and safe(member.name) == member.name
            assert member.isfile() and not member.issym() and not member.islnk()
            assert (member.mode, member.uid, member.gid, member.mtime, member.uname, member.gname) == (0o644, 0, 0, 0, '', '')
            content = tar.extractfile(member).read()
            assert content == blobs[member.name[6:]] and hashlib.sha256(content).hexdigest() == member.name[6:] and len(content) == member.size

    assert len(plan['present_inputs']) == 68
    assert len(plan['absent_inputs']) == 16 and len(set(plan['absent_inputs'])) == 16
    for path, hashed in plan['present_inputs'].items():
        assert digest(path) == hashed and pins.get(path) == hashed
    for path in plan['absent_inputs']:
        assert not Path(path).exists() and not Path(path).is_symlink()
    assert len(plan['source_overlay']) == 9 and {row['module'] for row in plan['source_overlay']} == CHANGED
    for row in plan['source_overlay']:
        for key in ['candidate', 'before']:
            assert pins[row[key]['path']] == row[key]['sha256']
        assert pins[row['canonical']] == row['candidate']['sha256']
    retired_modules = plan['newly_retired_module_sources']
    assert retired_modules == []
    assert plan['newly_retired_producers'] == []
    retired = retired_modules + plan['newly_retired_producers']
    assert {row['canonical']: row['sha256'] for row in retired} == RETIRED
    for row in retired:
        assert pins[row['snapshot']] == row['sha256'] == digest(row['snapshot'])
        assert row['canonical'] in plan['absent_inputs'] and not Path(row['canonical']).exists()
    review = read(cfg['actual_review']['source'])
    assert review['status'] == 'PASS_INDEPENDENT_ACTUAL_CANDIDATE_READBACK'
    assert all(review[key] == EXPECTED_COUNTS[key] for key in ['providers', 'projects', 'typed_clients', 'fresh', 'reuses', 'audits'])
    assert (review['client_reports'], review['WFTheory_reports'], review['audit_reports']) == (93, 5, 10)
    assert review['exact_profiles_preserved'] and review['all_source_object_dependency_log_toolchain_bindings_checked'] and review['fresh_site_or_forward_certificate_batches'] == []
    assert review['auditor']['path'] == cfg['actual_review_helper']['source'] and review['auditor']['sha256'] == cfg['actual_review_helper']['sha256']
    assert review['result']['path'] == run['result']['source'] and review['result']['sha256'] == args.expected_result_sha
    assert review['basis_result']['sha256'] == BASIS_SHA and capture['actual_review_sha256'] == cfg['actual_review']['sha256']
    for module in result['fresh_modules']:
        row = done[module]
        record = Path(row['log']).with_name('record.json')
        assert read(record) == row and row['status'] == 'PASS' and row['exit_code'] == 0 and not row['timed_out'] and row['warnings'] == 0
        assert pins[row['log']] == row['log_sha256'] and pins[str(record)] == digest(record)
        assert pins[str(record.parent / (module.split('.')[-1] + '.lean'))] == row['source_sha256']
    for row in result['audits']:
        record = Path(row['log']).with_name('record.json')
        assert read(record) == row and row['status'] == 'PASS' and row['exit_code'] == 0 and not row['timed_out'] and row['warnings'] == 0
        assert pins[row['source']] == row['source_sha256'] and pins[row['log']] == row['log_sha256'] and str(record) in pins
    for path, hashed in pins.items():
        assert digest(path) == hashed
    for path, hashed in profile_log_pins.items():
        assert digest(path) == hashed
    report = {'status': 'PASS_INDEPENDENT_ARCHIVE_INDEX_AND_REQUIRED_COVERAGE_REVIEW', 'auditor': pin(__file__), 'archive': pin(archive), 'index': pin(args.packet / 'index.json'), 'capture_receipt': pin(args.packet / 'capture.json'), 'config': pin(args.config), 'accepted_result_sha256': args.expected_result_sha, 'blob_members': len(blobs), 'logical_entries': len(logical), 'source_aliases': len(sources), 'external_boundary_files': 11, 'raw_files': len(raw['files']), 'checked_current_workspace_sources': 226, 'accepted_fresh_attempt_triples': 56, 'candidate_audit_triples': 2, 'preserved_failed_contexts': len(failed_roots), 'expected_failed_roots': [str(path) for path in failed_roots], 'all_member_hashes_bytes_and_metadata_exact': True, 'complete_logical_and_source_alias_index_reconstructed': True, 'final_source_overlay_and_no_new_retirements_checked': True, 'all_current_candidate_present_pins_checked': len(plan['present_inputs']), 'all_required_absences_checked': len(plan['absent_inputs']), 'objects_copied': False, 'filesystem_archive_extraction': False, 'archived_code_Lean_generator_or_capture_helper_execution': False, 'scope': 'Independent in-memory archive inspection and complete index/source-alias reconstruction. One accepted phase22 run and its two explicitly required rejected prefixes are checked separately. Phase21 stays an exact eleven-file external boundary; its earlier rejected roots are not recopied.'}
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2)
        stream.write('\n')
    print(json.dumps({'status': report['status'], 'review': pin(args.output)}))


if __name__ == '__main__':
    main()
