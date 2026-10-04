#!/usr/bin/env python3
"""Independent, presentation-only Report71 tool review; no scientific code execution."""
import argparse
import difflib
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import zipfile

BASE = Path('/workspace/shared/report71-independent-release-tools-review-20261004')
SOURCE = Path('/workspace/shared/report71-short-exactness-release-20261004')
REPORT70 = Path('/workspace/shared/report70-two-scale-radius-release-20261004')
TOOLS = {
    'release71.py': '283142424d8b0eeeaf289a0908a80896f76146efd64b3a54cfa004b28f1d167c',
    'build_report71.py': '3b391cc4490c117c631d877ef20e9387d75f8fa681cc4e66c0b59b23c13dbd9f',
    'selftest71.py': '7c399f7e661edeb7f15f4b80e9571035c89d4befff2f1d088e42869094d27bee',
    'provenance71.py': '61bd9df7642d1dc75258269217157108a8c25f7570919aca03d3a6ea0cffa789',
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def write(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')

def snapshot(root):
    rows = {}
    for p in [root, *sorted(root.rglob('*'))]:
        s = p.lstat()
        if not (stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode)):
            raise ValueError('Nonregular object ' + str(p))
        name = '.' if p == root else p.relative_to(root).as_posix()
        row = {'type': 'directory' if p.is_dir() else 'file', 'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns}
        if p.is_file():
            if s.st_nlink != 1:
                raise ValueError('Hardlinked object ' + str(p))
            data = p.read_bytes()
            row.update(bytes=len(data), sha256=sha(data))
        rows[name] = row
    return rows

def main():
    assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
    ap = argparse.ArgumentParser()
    ap.add_argument('--manuscript-pin', required=True)
    ap.add_argument('--pdf-pin', required=True)
    ap.add_argument('--flat-pin', required=True)
    ap.add_argument('--lock-pin', required=True)
    a = ap.parse_args()
    receipts = BASE / 'receipts'
    scratch = BASE / 'scratch'
    scratch.mkdir()
    for name, expected in TOOLS.items():
        assert sha((SOURCE / 'tools' / name).read_bytes()) == expected, ('Tool changed after full inspection', name)
    for name, expected in [('manuscript/MANUSCRIPT_PINS.json', a.manuscript_pin), ('Report71.pdf', a.pdf_pin), ('Report71.tex', a.flat_pin), ('tools/BUILD_DEPENDENCIES_LOCK.json', a.lock_pin), ('INPUT_PINS.json', 'ad643bd888c3a046c74d976d63c5753e65c3c72cbdf82ab7d6454c57483548e3')]:
        assert sha((SOURCE / name).read_bytes()) == expected, ('Stable pin mismatch', name)
    before = snapshot(SOURCE)
    write(receipts / 'SOURCE_BEFORE.json', before)
    original_roots = [Path('/workspace/shared') / n for n in ('short-exactness-radius-20261004', 'short-exactness-independent-audit-20261004', 'radius-frontier-20261004', 'report70-two-scale-radius-release-20261004')]
    originals_before = {str(p): snapshot(p) for p in original_roots}
    write(receipts / 'ORIGINALS_BEFORE.json', originals_before)
    old_raw = (REPORT70 / 'RELEASE_MANIFEST.json').read_bytes()
    assert sha(old_raw) == '0f96f8aa8bba3eb581070a3db48798ecba3ef0c49daa47a124e62b6754ee30e1'
    old = json.loads(old_raw)
    old_snapshot = originals_before[str(REPORT70)]
    old_files = {n: {k: v for k, v in row.items() if k != 'type'} for n, row in old_snapshot.items() if row['type'] == 'file' and n != 'RELEASE_MANIFEST.json'}
    old_dirs = {n: {k: v for k, v in row.items() if k != 'type'} for n, row in old_snapshot.items() if row['type'] == 'directory' and n != '.'}
    assert old_files == old['files'] and old_dirs == old['directories'], 'Sealed Report70 inventory differs'
    adaptations = {}
    for name in ('release', 'build_report', 'selftest'):
        old_name = name + '70.py'
        new_name = name + '71.py'
        old_data = (REPORT70 / 'tools' / old_name).read_text()
        new_data = (SOURCE / 'tools' / new_name).read_text()
        actual = ''.join(difflib.unified_diff(old_data.splitlines(True), new_data.splitlines(True), fromfile='Report70/tools/' + old_name, tofile='Report71/tools/' + new_name))
        retained = (SOURCE / 'qa' / ('ADAPTATION_' + new_name + '.diff')).read_text()
        assert actual == retained, ('Adaptation diff mismatch', new_name)
        adaptations[new_name] = {'source_sha256': sha(old_data.encode()), 'result_sha256': sha(new_data.encode()), 'diff_sha256': sha(actual.encode())}
    write(receipts / 'ADAPTATION_VERIFICATION.json', {'status': 'PASS', 'sealed_report70_manifest_sha256': sha(old_raw), 'adaptations': adaptations, 'report70_code_executed': False})
    fixture = scratch / 'release-clone'
    shutil.copytree(SOURCE, fixture, copy_function=shutil.copy2)
    assert snapshot(fixture) == before, 'Metadata-preserving source clone differs'
    commands = []
    def command(label, tool, args, root=fixture, good=True, flags=('-I', '-S', '-B')):
        argv = [sys.executable, *flags, str(root / 'tools' / tool), *args]
        result = subprocess.run(argv, cwd=BASE, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=600)
        log = receipts / (label + '.stdout')
        log.write_bytes(result.stdout)
        commands.append({'name': label, 'argv': argv, 'expected_success': good, 'exit_status': result.returncode, 'stdout_sha256': sha(result.stdout), 'status': 'PASS' if (result.returncode == 0) == good else 'FAIL'})
        write(receipts / 'COMMANDS.json', commands)
        assert (result.returncode == 0) == good, (label, result.stdout.decode(errors='replace')[-3000:])
        print(label + ': PASS', flush=True)
        return result
    command('input-authentication', 'release71.py', ['check-inputs'])
    prepared = scratch / 'prepared'
    command('deterministic-flatten', 'release71.py', ['prepare', '--output-dir', str(prepared)])
    assert (prepared / 'Report71.tex').read_bytes() == (fixture / 'Report71.tex').read_bytes()
    assert (prepared / 'MANUSCRIPT_PINS.json').read_bytes() == (fixture / 'manuscript/MANUSCRIPT_PINS.json').read_bytes()
    command('provenance-original-endpoints', 'provenance71.py', ['--compare-originals', '--output-dir', str(scratch / 'provenance')])
    for p in (scratch / 'provenance').iterdir():
        shutil.copy2(p, receipts / ('provenance-' + p.name))
    build_args = ['--pins-sha', a.manuscript_pin, '--dependency-lock-sha', a.lock_pin, '--require-packaged-match', '--render-dpi', '72']
    command('actual-locked-build', 'build_report71.py', [*build_args, '--output-dir', str(scratch / 'build')])
    command('synthetic-hostile-selftests', 'selftest71.py', ['--output-dir', str(scratch / 'selftests')])
    selftests = json.loads((scratch / 'selftests/SELFTEST_RECEIPT.json').read_bytes())
    assert selftests['status'] == 'PASS' and all(r['status'] == 'PASS' for r in selftests['tests'])
    shutil.copy2(scratch / 'selftests/SELFTEST_RECEIPT.json', receipts / 'SELFTEST_RECEIPT.json')
    assert snapshot(fixture) == before, 'Clone changed before intentional manifest installation'
    manifest_path = scratch / 'clone-manifest.json'
    command('test-manifest-generate', 'release71.py', ['manifest', '--output', str(manifest_path)])
    manifest_pin = sha(manifest_path.read_bytes())
    shutil.copy2(manifest_path, fixture / 'RELEASE_MANIFEST.json')
    command('test-manifest-verify', 'release71.py', ['verify', '--manifest-sha256', manifest_pin])
    for label in ('a', 'b'):
        command('test-deterministic-archive-' + label, 'release71.py', ['archive', '--manifest-sha256', manifest_pin, '--output', str(scratch / ('archive-' + label + '.zip'))])
    za = (scratch / 'archive-a.zip').read_bytes()
    assert za == (scratch / 'archive-b.zip').read_bytes(), 'Deterministic archives differ'
    extracted = scratch / 'extracted'
    command('test-authenticated-extraction', 'release71.py', ['extract', '--manifest-sha256', manifest_pin, '--archive', str(scratch / 'archive-a.zip'), '--output-dir', str(extracted)])
    command('test-relocated-verification', 'release71.py', ['verify', '--manifest-sha256', manifest_pin], root=extracted)
    command('actual-relocated-locked-build', 'build_report71.py', [*build_args, '--output-dir', str(scratch / 'relocated-build')], root=extracted)
    command('relocated-provenance', 'provenance71.py', ['--output-dir', str(scratch / 'relocated-provenance')], root=extracted)
    for label in ('build', 'relocated-build'):
        b = scratch / label
        for name in ('BUILD_RECEIPT.json', 'BUILD_DEPENDENCIES.json', 'RECORDER_INPUT_UNION.json', 'PREFLIGHT.json', 'PAGE_INVENTORY.json', 'format.fls', 'compile-1.fls', 'compile-2.fls', 'compile-3.fls'):
            shutil.copy2(b / name, receipts / (label + '-' + name))
        assert sha((b / 'Report71.pdf').read_bytes()) == a.pdf_pin
        assert (b / 'BUILD_DEPENDENCIES.json').read_bytes() == (fixture / 'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()
        union = json.loads((b / 'RECORDER_INPUT_UNION.json').read_bytes())
        lock = json.loads((fixture / 'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes())
        assert [x['pass'] for x in union['passes']] == ['format', 'compile-1', 'compile-2', 'compile-3']
        assert union['union'] == lock['system_inputs']
        recorded = set().union(*(set(x['system_inputs']) for x in union['passes']))
        extra = set(union['union']) - recorded
        assert all(p.endswith(('/lm.map', '/cm.map', '/cmextra.map', '/symbols.map', '/latxfont.map')) for p in extra)
    write(receipts / 'REPLAY_AND_ARCHIVE_EQUALITY.json', {'status': 'PASS', 'pdf_sha256': a.pdf_pin, 'test_clone_manifest_sha256': manifest_pin, 'test_archive_sha256': sha(za), 'archives_byte_equal': True, 'fresh_format_and_all_pass_union_verified': True, 'actual_and_relocated_pdf_equal': True, 'final_root_release_postseal_gate': False})
    with zipfile.ZipFile(scratch / 'archive-a.zip') as z:
        entries = [(info, z.read(info)) for info in z.infolist()]
    adversarial = []
    def malicious(label, change, pin=manifest_pin):
        path = scratch / (label + '.zip')
        with zipfile.ZipFile(path, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
            for index, (info, data) in enumerate(entries):
                info = zipfile.ZipInfo(info.filename, info.date_time)
                original_info = entries[index][0]
                info.create_system = original_info.create_system
                info.external_attr = original_info.external_attr
                changed = change(index, info, data)
                if changed is not None:
                    z.writestr(*changed)
            if label == 'zip-duplicate-entry':
                z.writestr(entries[0][0], entries[0][1])
        dest = scratch / ('refused-' + label)
        command(label, 'release71.py', ['extract', '--manifest-sha256', pin, '--archive', str(path), '--output-dir', str(dest)], good=False)
        assert not dest.exists(), ('Hostile extraction produced output', label)
        adversarial.append({'name': label, 'status': 'PASS', 'no_output_created': True, 'archive_sha256': sha(path.read_bytes())})
    def modify_kind(kind):
        def change(index, info, data):
            if index == 0:
                info.external_attr = (kind | 0o644) << 16
            return info, data
        return change
    malicious('zip-symlink-type', modify_kind(stat.S_IFLNK))
    malicious('zip-directory-type', modify_kind(stat.S_IFDIR))
    malicious('zip-fifo-type', modify_kind(stat.S_IFIFO))
    def mode_change(index, info, data):
        if index == 0:
            info.external_attr ^= 0o100 << 16
        return info, data
    malicious('zip-mode-mismatch', mode_change)
    def foreign_system(index, info, data):
        if index == 0:
            info.create_system = 0
        return info, data
    malicious('zip-foreign-platform', foreign_system)
    malicious('zip-payload-tamper', lambda index, info, data: (info, data + b'X' if index == 0 else data))
    malicious('zip-duplicate-entry', lambda index, info, data: (info, data))
    malicious('zip-wrong-manifest-pin', lambda index, info, data: (info, data), pin='0' * 64)
    def duplicate_json(index, info, data):
        if info.filename == 'Report71/RELEASE_MANIFEST.json':
            data = data.replace(b'{', b'{"format": "Report71 release manifest v1",', 1)
        return info, data
    duplicate_manifest = (fixture / 'RELEASE_MANIFEST.json').read_bytes().replace(b'{', b'{"format": "Report71 release manifest v1",', 1)
    malicious('zip-duplicate-json-key', duplicate_json, pin=sha(duplicate_manifest))
    for label, flags in [('reject-no-isolation', ('-S', '-B')), ('reject-site-enabled', ('-I', '-B')), ('reject-bytecode-enabled', ('-I', '-S')), ('reject-optimization', ('-I', '-S', '-B', '-O'))]:
        command(label, 'release71.py', ['check-inputs'], flags=flags, good=False)
        adversarial.append({'name': label, 'status': 'PASS'})
    write(receipts / 'EXTRA_ADVERSARIAL_RECEIPT.json', {'status': 'PASS', 'test_count': len(adversarial), 'tests': adversarial})
    after = snapshot(SOURCE)
    originals_after = {str(p): snapshot(p) for p in original_roots}
    write(receipts / 'SOURCE_AFTER.json', after)
    write(receipts / 'ORIGINALS_AFTER.json', originals_after)
    assert after == before, 'Release owner source changed during independent review'
    assert originals_before == originals_after, 'Original endpoint changed during review'
    write(receipts / 'PRESERVATION.json', {'status': 'PASS', 'source_endpoint_equal': True, 'originals_endpoint_equal': True, 'source_files': sum(row['type'] == 'file' for row in before.values()), 'original_counts': {root: len(rows) for root, rows in originals_before.items()}, 'scope': 'Bytes, object set, mode and nanosecond mtime; atime excluded; endpoint equality does not prove continuous immutability'})
    write(receipts / 'REVIEW_RESULT.json', {'status': 'PASS', 'tools_fully_read_before_execution': True, 'tool_pins': TOOLS, 'presentation_pins': vars(a), 'selftest_count': selftests['test_count'], 'extra_adversarial_count': len(adversarial), 'command_count': len(commands), 'scientific_programs_executed': False, 'historical_report70_live_additions': 49, 'historical_report70_existing_qa_mtime_change': True, 'fresh_audit_equal_endpoints_do_not_erase_history': True, 'final_postseal_gate_separate': True})
    print('INDEPENDENT REVIEW PASS', flush=True)

if __name__ == '__main__':
    main()
