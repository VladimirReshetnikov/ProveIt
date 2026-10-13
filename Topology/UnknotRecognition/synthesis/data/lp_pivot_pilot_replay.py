#!/usr/bin/env python3
"""Replay the frozen revision-973 LP pivot pilot without solver discovery.

Only the archived native snapshot is imported by the isolated child process.
The archive and every member are checked before manual safe extraction.
"""
import argparse
from hashlib import sha256
import io
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tarfile
import tempfile


if not __debug__:
    raise RuntimeError('Evidence replay requires assertions enabled')

ARCHIVE_NAME = 'lp-pivot-pilot-973c6fdee.tar.gz'
ARCHIVE_SHA256 = 'c894a7b69a3127ffba539290fabae1f95a6a5e0e297d1134aa99a9b743222867'
ARCHIVE_BYTES = 1063563
MEMBER_COUNT = 317
MEMBER_BYTES = 10673636
SNAPSHOT_MANIFEST_SHA256 = '1ad2f6de89875b2cfa8a5edba7d21b1bcffae752c23c203fc144cbfcbf0d1776'
REVISION = '973c6fdee7b9ee6239c16b8d325207b6f667e95e'
PREFIX = 'lp-pivot-pilot/'
SCRIPT_NAMES = (
    'common.py', 'prefix_template.py', 'prefix.py', 'checker.py',
    'pilot.py', 'PROTOCOL.json', 'DESIGN.md',
)
RESULT_NAMES = ('results/controls.json', 'results/capture.json', 'results/comparison.json')
LOG_NAMES = ('controls.log', 'capture.log', 'comparison.log', 'replay.log')
RESULT_SHA256 = {
    'results/controls.json': 'cea5d813d5c2a94da4501d8ed610f121e2d1092b1f12dcea0bc1f534092ec067',
    'results/capture.json': '375ce63fb33e7b7bca1b4f22e0f38b1920643ea50d68948738cbc3095e1eb620',
    'results/comparison.json': 'a807526cc2ab2652cbabdf1639a009d143e3feb826e2a9903ff4b6cf2471b2d3',
}
EXPECTED_RETURNED = {
    'command': 'check',
    'passed': True,
    'summary': {
        'controls': {'callback_arms': 3, 'queries': 21},
        'capture': {
            'authenticated_source': True,
            'cumulative': {'ellipsoid_iterations': 0, 'feasibility_calls': 0, 'pivots': 10000},
            'fresh_whole_call': False,
            'queries': 8,
            'status': 'INCONCLUSIVE',
        },
        'comparison': {
            'bland': {'INCONCLUSIVE': 1, 'NONPOSITIVE': 6, 'POSITIVE': 1,
                'fallback_used': 0, 'pivots': 10000, 'queries': 8, 'tableau_updates': 45184980},
            'dantzig': {'INCONCLUSIVE': 2, 'NONPOSITIVE': 5, 'POSITIVE': 1,
                'fallback_used': 0, 'pivots': 9187, 'queries': 8, 'tableau_updates': 46708475},
            'dantzig_lex': {'INCONCLUSIVE': 0, 'NONPOSITIVE': 7, 'POSITIVE': 1,
                'fallback_used': 0, 'pivots': 784, 'queries': 8, 'tableau_updates': 3943665},
        },
    },
}


def digest(data):
    return sha256(data).hexdigest()


def same(left, right):
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return left.keys() == right.keys() and all(same(left[k], right[k]) for k in left)
    if type(left) in (list, tuple):
        return len(left) == len(right) and all(same(a, b) for a, b in zip(left, right))
    return left == right


def save(path, result):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    temporary.replace(path)


def checked_members(archive_path):
    assert archive_path.stat().st_size == ARCHIVE_BYTES, 'Unexpected archive byte count'
    data = archive_path.read_bytes()
    assert digest(data) == ARCHIVE_SHA256, 'Unexpected archive digest'
    payloads = {}
    with tarfile.open(fileobj=io.BytesIO(data), mode='r:gz') as archive:
        members = archive.getmembers()
        assert len(members) == MEMBER_COUNT
        assert len({item.name for item in members}) == MEMBER_COUNT, 'Duplicate tar member'
        assert [item.name for item in members] == sorted(item.name for item in members)
        assert sum(item.size for item in members) == MEMBER_BYTES
        for item in members:
            name = PurePosixPath(item.name)
            assert item.name.startswith(PREFIX)
            assert not name.is_absolute() and '..' not in name.parts
            assert '\\' not in item.name and '\x00' not in item.name
            assert str(name) == item.name
            assert item.isfile() and item.type == tarfile.REGTYPE
            assert not item.pax_headers
            assert item.mode == 0o644 and item.uid == item.gid == item.mtime == 0
            assert item.uname == item.gname == ''
            assert 0 <= item.size <= MEMBER_BYTES
            stream = archive.extractfile(item)
            assert stream is not None
            content = stream.read()
            assert len(content) == item.size
            payloads[item.name] = content
    manifest_name = PREFIX + 'snapshot/manifest.json'
    assert digest(payloads[manifest_name]) == SNAPSHOT_MANIFEST_SHA256
    manifest = json.loads(payloads[manifest_name])
    assert manifest['schema'] == 'lp-pivot-source-snapshot-v1'
    assert manifest['revision'] == REVISION
    assert type(manifest['files']) is dict and len(manifest['files']) == 302
    expected = {PREFIX + 'snapshot/' + name for name in manifest['files']}
    expected.add(manifest_name)
    expected.update(PREFIX + name for name in SCRIPT_NAMES + RESULT_NAMES + LOG_NAMES)
    assert set(payloads) == expected, 'Archive inventory differs from the frozen pilot'
    for name, expected_hash in manifest['files'].items():
        assert digest(payloads[PREFIX + 'snapshot/' + name]) == expected_hash
    for name, expected_hash in RESULT_SHA256.items():
        assert digest(payloads[PREFIX + name]) == expected_hash
    return payloads


def replay(archive_path, json_out, text_out):
    result = dict(schema='lp-pivot-pilot-archive-replay-v1', passed=False,
        phase='archive_validation', failures=[],
        archive=dict(path=str(archive_path), sha256=ARCHIVE_SHA256, bytes=ARCHIVE_BYTES),
        archive_members={}, member_count=MEMBER_COUNT, member_bytes=MEMBER_BYTES,
        snapshot_manifest_sha256=SNAPSHOT_MANIFEST_SHA256, snapshot_revision=REVISION,
        replay_helper_sha256=digest(Path(__file__).read_bytes()),
        discovery_disabled=True, current_native_imported=False,
        archived_native_snapshot_only=True, timings_claimed=False,
        whole_call_shared_budget_claimed=False, general_quasipolynomial_claimed=False)
    save(json_out, result)
    try:
        payloads = checked_members(archive_path)
        result['archive_members'] = {
            name: dict(bytes=len(content), sha256=digest(content))
            for name, content in sorted(payloads.items())
        }
        result['phase'] = 'isolated_replay'
        save(json_out, result)
        with tempfile.TemporaryDirectory(prefix='lp-pivot-pilot-replay-') as temporary:
            directory = Path(temporary).resolve()
            # No extractall: accept only checked regular files and write their
            # already-verified bytes under a new private temporary directory.
            for name, content in payloads.items():
                target = directory / name
                assert target.resolve().is_relative_to(directory)
                target.parent.mkdir(parents=True, exist_ok=True)
                with target.open('xb') as output:
                    output.write(content)
            pilot_root = directory / PREFIX.rstrip('/')
            command = [sys.executable, '-B', '-S', str(pilot_root / 'pilot.py'), 'check',
                '--controls', str(pilot_root / 'results/controls.json'),
                '--capture', str(pilot_root / 'results/capture.json'),
                '--comparison', str(pilot_root / 'results/comparison.json')]
            result['command'] = command
            environment = os.environ.copy()
            environment.pop('PYTHONPATH', None)
            environment.pop('PYTHONHOME', None)
            process = subprocess.run(command, cwd=pilot_root, env=environment,
                capture_output=True, text=True, check=False)
            text_out.parent.mkdir(parents=True, exist_ok=True)
            text_out.write_text(process.stdout + (
                '\n--- stderr ---\n' + process.stderr if process.stderr else ''))
            result['subprocess'] = dict(returncode=process.returncode,
                stdout_sha256=digest(process.stdout.encode()),
                stderr_sha256=digest(process.stderr.encode()))
            assert process.returncode == 0, 'Archived independent replay failed'
            assert process.stderr == '', 'Unexpected stderr from archived replay'
            lines = process.stdout.splitlines()
            assert len(lines) == 1, 'Expected one complete replay summary'
            returned = json.loads(lines[0])
            assert same(returned, EXPECTED_RETURNED), 'Replay summary differs from frozen coverage/results'
            result['returned_summary'] = returned
            result['coverage'] = dict(control_queries=21, callback_arms=3,
                captured_queries=8, fixed_comparison_records=24)
            assert digest(archive_path.read_bytes()) == ARCHIVE_SHA256
        result['phase'] = 'complete'
        result['passed'] = True
        save(json_out, result)
    except BaseException as error:
        result['passed'] = False
        result['failures'].append(dict(phase=result['phase'],
            exception_class=type(error).__name__, message=str(error), work_complete=False))
        if not text_out.exists():
            text_out.parent.mkdir(parents=True, exist_ok=True)
            text_out.write_text(type(error).__name__ + ': ' + str(error) + '\n')
        save(json_out, result)
        raise
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive', type=Path,
        default=Path(__file__).with_name(ARCHIVE_NAME))
    parser.add_argument('--json-out', type=Path, required=True)
    parser.add_argument('--text-out', type=Path, required=True)
    args = parser.parse_args()
    archive, json_out, text_out = (p.resolve() for p in (args.archive, args.json_out, args.text_out))
    assert len({archive, json_out, text_out, Path(__file__).resolve()}) == 4
    for output in (json_out, text_out):
        if output.exists():
            raise FileExistsError('Refuse to overwrite retained replay output: ' + str(output))
    result = replay(archive, json_out, text_out)
    print(json.dumps(dict(passed=result['passed'], archive_sha256=ARCHIVE_SHA256,
        member_count=MEMBER_COUNT, coverage=result['coverage'],
        returned_summary=result['returned_summary']), sort_keys=True))


if __name__ == '__main__':
    main()
