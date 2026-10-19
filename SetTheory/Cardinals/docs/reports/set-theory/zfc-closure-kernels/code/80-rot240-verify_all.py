#!/usr/bin/env python3
"""Verify the sealed package and replay proofs on a disposable copy.

Default: fresh complete 240-state universal runtime plus all local/source/boot
checks. --quick skips only that final universal run. Historical full-runtime
receipts remain inherited; the frozen 241 companion is freshly run in quick
mode. No source evidence is overwritten. A failed replay retains its temporary
work directory and logs. Requires only Python's standard library.
"""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import zipfile

if not __debug__ or sys.flags.optimize or os.environ.get('PYTHONOPTIMIZE') not in (None, '', '0'):
    raise RuntimeError('Enabled assertions required; disable -O and PYTHONOPTIMIZE')

ROOT = Path(__file__).resolve().parent
COMPANION_SHA = 'c4599e2a51cc4ad925e22f84dca2cfc1ae9cc974d0db0e904deb519cdf1ea481'
BASELINE_TABLE_SHA = '1fa8526c3c971d5a48868599eaed890f614c5a79256e51622d3e32a64229f3a3'
BASELINE_SITES_SHA = '3ee984818f0bdfd2c4daae72aeb14340572e34d73f5cdb5616b6d29d78fcd7f4'
FINAL_TABLE_SHA = '547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f'
FINAL_CANONICAL_SHA = '508b55a6dfdf96a42f09c49e410e078ae7478a1d0257d78d25503b4da24541cd'
FINAL_SITES_SHA = '74b1e7f73cc3ffe7761e36ab2d57a26e0ba34d3ac624f2472799e6ac41d5a51d'
UPSTREAM_ENGINE_SHA = '709cad65521d34bf77ed216128666ca23f5e4e49468a5949f761d47761a59003'
HELPER_SHA = '0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346'
FINAL_CASES_SHA = '950883a2dcf058d35ee52beb6ad40cf6677cc5ffc4b806f8fa12efc003db6066'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text(encoding='utf-8'))


def relative_name(name):
    assert isinstance(name, str) and name and '\\' not in name and '\x00' not in name
    assert not name.startswith('/') and ':' not in name
    path = PurePosixPath(name)
    assert path.parts and all(part not in ('', '.', '..') for part in path.parts)
    assert path.as_posix() == name
    return path


def verify_manifest(root):
    manifest_path = root / 'MANIFEST.json'
    assert manifest_path.is_file() and not manifest_path.is_symlink(), 'Mandatory MANIFEST.json missing'
    manifest = load(manifest_path)
    assert isinstance(manifest, dict) and isinstance(manifest.get('files'), list)
    listed = set()
    for row in manifest['files']:
        assert isinstance(row, dict) and {'path', 'bytes', 'sha256'} <= row.keys()
        relative = relative_name(row['path'])
        assert row['path'] != 'MANIFEST.json' and row['path'] not in listed
        listed.add(row['path'])
        assert type(row['bytes']) is int and row['bytes'] >= 0
        assert isinstance(row['sha256'], str) and len(row['sha256']) == 64
        assert all(c in '0123456789abcdef' for c in row['sha256'])
        path = root.joinpath(*relative.parts)
        assert path.is_relative_to(root)
        assert all(not root.joinpath(*relative.parts[:i]).is_symlink() for i in range(1, len(relative.parts)+1))
        assert stat.S_ISREG(path.stat().st_mode), ('Not a regular file', row['path'])
        assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], ('Manifest mismatch', row['path'])
    actual = set()
    for path in root.rglob('*'):
        mode = path.lstat().st_mode
        assert not stat.S_ISLNK(mode), ('Symlink in package', str(path))
        if stat.S_ISREG(mode):
            actual.add(path.relative_to(root).as_posix())
        else:
            assert stat.S_ISDIR(mode), ('Special file in package', str(path))
    assert actual - {'MANIFEST.json'} == listed, ('Unlisted or missing package files', sorted(actual - listed - {'MANIFEST.json'}), sorted(listed - actual))
    return {'files_checked': len(listed), 'manifest_sha256': sha(manifest_path), 'complete_inventory': True}


def check_adapter(root):
    source = root / 'reference/upstream_symbolic_runtime.py'
    helper_source = root / 'reference/upstream_independent_runtime.py'
    engine = root / 'verification/symbolic_runtime.py'
    helper = root / 'verification/independent_runtime.py'
    assert sha(source) == UPSTREAM_ENGINE_SHA and sha(helper_source) == HELPER_SHA
    before = source.read_bytes()
    substitutions = [
        (b'len(sites)==6459', b'len(sites)==6455'),
        (BASELINE_SITES_SHA.encode(), FINAL_SITES_SHA.encode()),
        (b'exact_QT_source_pin', b'exact_rotated_source_pin'),
    ]
    expected = before
    for old, new in substitutions:
        assert expected.count(old) == 1
        expected = expected.replace(old, new)
    assert engine.read_bytes() == expected, 'Runtime adapter changes more than the count, source pin, and field label'
    assert helper.read_bytes() == helper_source.read_bytes(), 'Runtime helper changed'
    return {'status': 'EXACT_THREE_SUBSTITUTION_ADAPTER_PASS',
            'upstream_engine_sha256': UPSTREAM_ENGINE_SHA,
            'adapted_engine_sha256': sha(engine), 'helper_sha256': sha(helper),
            'substitutions': [[a.decode(), b.decode()] for a, b in substitutions],
            'helper_byte_identical': True}


def extract_companion(archive_path, destination):
    assert sha(archive_path) == COMPANION_SHA, 'Frozen 241 archive hash mismatch'
    destination.mkdir(parents=True, exist_ok=False)
    with zipfile.ZipFile(archive_path) as archive:
        records = archive.infolist()
        assert 0 < len(records) <= 10000
        assert sum(info.file_size for info in records) <= 256 * 1024 * 1024
        assert archive.testzip() is None
        seen = set()
        for info in records:
            name = info.filename.rstrip('/') if info.is_dir() else info.filename
            relative = relative_name(name)
            assert relative.parts[0] == 'busybeaver241-companion'
            assert name not in seen and not (info.flag_bits & 1)
            seen.add(name)
            mode = (info.external_attr >> 16) & 0o170000
            assert mode in (0, stat.S_IFREG, stat.S_IFDIR), ('Nonregular archive member', name)
            assert not (mode == stat.S_IFDIR and not info.is_dir())
        for info in records:
            name = info.filename.rstrip('/') if info.is_dir() else info.filename
            relative = relative_name(name)
            path = destination.joinpath(*relative.parts)
            assert path.is_relative_to(destination)
            if info.is_dir():
                path.mkdir(parents=True, exist_ok=True)
            else:
                path.parent.mkdir(parents=True, exist_ok=True)
                with archive.open(info) as source, path.open('xb') as output:
                    shutil.copyfileobj(source, output)
                assert path.stat().st_size == info.file_size
    return destination / 'busybeaver241-companion'


def read_table_keys(path):
    keys = set()
    for line in path.read_text().splitlines():
        if line and not line.startswith('#'):
            fields = line.split()
            assert len(fields) == 5
            key = int(fields[0]), int(fields[1])
            assert key not in keys
            keys.add(key)
    return keys


def validate_runtime(report, case_path, package):
    assert report['status'] == 'UNIVERSAL_MATHEMATICAL_PASS'
    assert report['cases'] == report['expected_cases'] == 8386
    assert report['symbolic_steps'] == 2322575 and report['minimum_actual_steps'] == 13
    assert report['table_sha256'] == FINAL_TABLE_SHA == sha(package / 'machines/zfc240_old.tm')
    assert report['sites_sha256'] == FINAL_SITES_SHA == sha(package / 'machines/sites_logical.json')
    assert report['checker_sha256'] == sha(package / 'verification/symbolic_runtime.py')
    assert report['helper_sha256'] == HELPER_SHA == sha(package / 'verification/independent_runtime.py')
    assert report['input_validation'] == {
        'working_states': 240, 'leaf_count': 6455, 'complete_binary_tree': True,
        'maximum_depth': 51, 'exact_rotated_source_pin': True,
        'source_equivalence_checked_separately': True,
    }
    rows = report['directly_used_rows']
    assert len(rows) == 480 and set(map(tuple, rows)) == read_table_keys(package / 'machines/zfc240_old.tm')
    assert sha(case_path) == FINAL_CASES_SHA
    cases = load(case_path)
    assert len(cases) == 8386
    assert sum(case['symbolic_steps'] for case in cases) == 2322575
    assert min(case['duration'][0] for case in cases) == 13
    assert report['execution']['optimization'] == 0 and report['execution']['debug_enabled'] is True
    return {'status': report['status'], 'cases': 8386, 'symbolic_steps': 2322575,
            'minimum_duration': 13, 'used_rows': 480, 'cases_sha256': FINAL_CASES_SHA}


def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n', encoding='utf-8')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--quick', action='store_true', help='Skip only the fresh complete 240-state runtime')
    parser.add_argument('--output', type=Path, default=ROOT.parent / 'zfc240_replay_result.json', help='Receipt outside the source package')
    args = parser.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(ROOT):
        parser.error('--output must be outside the package, so source evidence and its manifest remain unchanged')
    started = time.monotonic()
    work = None
    jobs = []
    try:
        print('Checking complete package manifest and exact runtime adapter', flush=True)
        original_manifest = verify_manifest(ROOT)
        adapter = check_adapter(ROOT)
        archive = ROOT / 'reference/BusyBeaver_241_Companion_2026-10-18.zip'
        assert sha(archive) == COMPANION_SHA
        assert sha(ROOT / 'reference/baseline241_old.tm') == BASELINE_TABLE_SHA
        assert sha(ROOT / 'reference/baseline_sites.json') == BASELINE_SITES_SHA
        assert sha(ROOT / 'machines/zfc240.tm') == FINAL_CANONICAL_SHA
        sealed_report = load(ROOT / 'evidence/runtime240.json')
        sealed_cases = (ROOT / 'evidence/runtime240_cases.json').read_bytes()
        preserved_runtime = validate_runtime(sealed_report, ROOT / 'evidence/runtime240_cases.json', ROOT)

        work = Path(tempfile.mkdtemp(prefix='zfc240-replay-')).resolve()
        package = work / 'package'
        shutil.copytree(ROOT, package)
        assert verify_manifest(package) == original_manifest
        assert check_adapter(package) == adapter
        fresh = work / 'fresh'
        fresh.mkdir()
        logs = work / 'logs'
        logs.mkdir()
        environment = {**os.environ, 'PYTHONOPTIMIZE': '', 'PYTHONDONTWRITEBYTECODE': '1'}
        environment.pop('PYTHONPATH', None)

        def run(script, *parameters):
            index = len(jobs) + 1
            log = logs / f'{index:02d}-{script.stem}.log'
            command = [sys.executable, '-B', str(script), *map(str, parameters)]
            print(f'Running {script.relative_to(work)}', flush=True)
            began = time.monotonic()
            with log.open('w', encoding='utf-8') as capture:
                completed = subprocess.run(command, cwd=script.parent, stdout=capture,
                                           stderr=subprocess.STDOUT, env=environment)
            job = {'script': script.relative_to(work).as_posix(),
                   'returncode': completed.returncode,
                   'seconds': round(time.monotonic() - began, 3),
                   'log': log.relative_to(work).as_posix(), 'log_sha256': sha(log)}
            jobs.append(job)
            if completed.returncode != 0:
                raise RuntimeError(f'{script.name} failed; log: {log}\n{log.read_text()[-6000:]}')

        def require(path, expected):
            assert path.is_file(), ('Fresh gate produced no receipt', str(path))
            result = load(path)
            assert result.get('status') == expected, ('Unexpected gate status', str(path), result.get('status'))
            return result

        run(package / 'build.py', '--output', fresh / 'build.json')
        build = require(fresh / 'build.json', 'BUILD_EXACT_RECONSTRUCTION_PASS')
        assert build['working_states'] == 240 and build['generated_tables_source_and_bijection_byte_identical'] is True
        verification = package / 'verification'
        run(verification / 'verify_local.py', '--output', fresh / 'local_root.json')
        local_root = require(fresh / 'local_root.json', 'ROOT_INDEPENDENT_LOCAL_ALL_TAPE_PASS')
        assert local_root['invariant_implications'] == local_root['positive_whole_tape_blocks'] == 7640
        run(verification / 'verify_boot.py', '--output', fresh / 'boot_root.json')
        boot_root = require(fresh / 'boot_root.json', 'ROOT_EXACT_BLANK_AND_CLOCK_PASS')
        assert boot_root['old_steps'] == 408941 and boot_root['new_steps'] == 409691 and boot_root['clock_extra'] == 750
        run(verification / 'verify_local_independent.py', '--root', package, '--output', fresh / 'local_independent.json')
        local_independent = require(fresh / 'local_independent.json', 'PASS_FINITE_LOCAL_ALL_TAPE_241_ROTATED_TO_240')
        run(verification / 'verify_boot_independent.py', '--root', package, '--output', fresh / 'boot_independent.json')
        boot_independent = require(fresh / 'boot_independent.json', 'PASS_EXACT_240_BLANK_SPARSE_DENSE')
        assert boot_independent['candidate240_steps'] == 409691
        source_dir = fresh / 'source'
        run(verification / 'verify_source.py', '--package-root', package, '--output-dir', source_dir)
        source = require(source_dir / 'rotation142_source_proof.json', 'SOURCE_CONTEXT_ROTATION142_PASS')
        source_boot = require(source_dir / 'rotation142_boot.json', 'ROTATION142_EXACT_BLANK_PASS')
        assert source['outside_guarded_edges'] == 8370 and source['macro_count'] == 4
        assert source_boot['steps'] == 408941
        run(verification / 'review_independent.py', '--root', package, '--output', fresh / 'review_independent.json')
        review = require(fresh / 'review_independent.json', 'INDEPENDENT_SOURCE_AND_LOCAL_REVIEW_PASS')
        run(package / 'theory/dense_order_filter.py', '--output', fresh / 'dense_order_results.json')
        theory = require(fresh / 'dense_order_results.json', 'PASS')
        assert theory == load(ROOT / 'evidence/dense_order_results.json')

        print('Checking frozen 241 companion and its inherited dependency chain in quick mode', flush=True)
        companion = extract_companion(package / 'reference/BusyBeaver_241_Companion_2026-10-18.zip', work / 'inherited')
        bindings = {
            'reference/baseline241_old.tm': 'runtime/candidate_1_old.tm',
            'reference/baseline_sites.json': 'runtime/sites_logical.json',
            'reference/upstream_symbolic_runtime.py': 'runtime/symbolic_runtime.py',
            'reference/upstream_independent_runtime.py': 'runtime/independent_runtime.py',
        }
        for ours, inherited in bindings.items():
            assert (package / ours).read_bytes() == (companion / inherited).read_bytes(), ('Inherited byte binding failed', ours)
        run(companion / 'verify_all.py', '--quick', '--output', fresh / 'companion_quick.json')
        historical = require(fresh / 'companion_quick.json', 'QUICK_COMPANION_REPLAY_PASS')
        assert historical['fresh_241_blank_steps'] == 408419
        assert historical['fresh_241_universal'] is None

        direct = None
        if not args.quick:
            runtime_output = fresh / 'runtime240.json'
            run(verification / 'symbolic_runtime.py', '--table', package / 'machines/zfc240_old.tm',
                '--sites', package / 'machines/sites_logical.json', '--output', runtime_output)
            actual = require(runtime_output, 'UNIVERSAL_MATHEMATICAL_PASS')
            direct = validate_runtime(actual, fresh / 'runtime240_cases.json', package)
            for key in ('table_sha256', 'sites_sha256', 'checker_sha256', 'helper_sha256',
                        'input_validation', 'symbolic_steps', 'minimum_actual_steps', 'blocks', 'directly_used_rows'):
                assert actual[key] == sealed_report[key], ('Sealed universal output differs', key)
            assert (fresh / 'runtime240_cases.json').read_bytes() == sealed_cases, 'Per-case output bytes differ from sealed evidence'
            direct['all_case_outputs_byte_identical'] = True
            direct['all_case_outputs_json_identical'] = load(fresh / 'runtime240_cases.json') == json.loads(sealed_cases)
            assert direct['all_case_outputs_json_identical'] is True
            direct['fresh_seconds'] = actual['seconds']

        assert verify_manifest(ROOT) == original_manifest, 'Source package changed during replay'
        assert verify_manifest(package) == original_manifest, 'A checker altered the disposable sealed package'
        assert check_adapter(ROOT) == adapter
        result = {
            'status': 'QUICK_ZFC240_REPLAY_PASS' if args.quick else 'FULL_FRESH_ZFC240_REPLAY_PASS',
            'manifest': original_manifest, 'runtime_adapter': adapter,
            'frozen_241_archive_sha256': COMPANION_SHA,
            'fresh_construction': build['status'],
            'fresh_local_proofs': [local_root['status'], local_independent['status']],
            'fresh_local_implications_each': 7640,
            'fresh_source_context': {'status': source['status'], 'macros': 4, 'outside_guarded_edges': 8370},
            'fresh_initialization': {'rotated241_steps': 408941, 'final240_steps': 409691,
                                     'independent_statuses': [boot_root['status'], boot_independent['status'], source_boot['status']]},
            'fresh_independent_review': review['status'], 'fresh_theory_filter': theory['status'],
            'fresh_frozen241_quick_chain': historical,
            'historical_universal_scope': 'The frozen 241/242/243 full-runtime receipts are inherited and byte-bound, not freshly rerun. The intermediate rotated241 complete-runtime receipt is also preserved; the final240 runtime is freshly rerun only in default full mode.',
            'preserved_final240_runtime': preserved_runtime,
            'fresh_final240_runtime': direct,
            'quick_mode_skips_only_fresh_final240_universal': bool(args.quick),
            'source_evidence_unchanged': True, 'jobs': jobs,
            'seconds': round(time.monotonic() - started, 3),
            'python': sys.version, 'optimization': sys.flags.optimize,
            'scope': 'Executable ordinary source and whole-tape mathematical proofs with exact construction, initialization, and universal unary/list induction. No new proof-assistant consistency endpoint is asserted.',
        }
        save(output, result)
        shutil.rmtree(work)
        work = None
        print(json.dumps(result, indent=2), flush=True)
    except BaseException as error:
        failure = {'status': 'ZFC240_REPLAY_FAILED', 'error': repr(error),
                   'temporary_work_directory': str(work) if work is not None else None,
                   'jobs': jobs, 'seconds': round(time.monotonic() - started, 3)}
        save(output, failure)
        print(json.dumps(failure, indent=2), file=sys.stderr, flush=True)
        if work is not None:
            print(f'Failed replay retained all temporary inputs and logs at: {work}', file=sys.stderr, flush=True)
        raise


if __name__ == '__main__':
    main()
