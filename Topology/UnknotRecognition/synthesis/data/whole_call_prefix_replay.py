#!/usr/bin/env python3
"""Replay fourteen frozen whole-call LP prefix comparisons without discovery.

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

ARCHIVE_NAME = 'whole-call-prefix-4d1f76f06.tar.gz'
# Frozen after all fourteen calls and independent scratch replay passed.
# The archive preserves the original snapshot, scripts, results and logs.
ARCHIVE_SHA256 = '787a3240adf2e7e655b4dd8f26da058700c848c9bc5b08e419692cf564791138'
ARCHIVE_BYTES = 1385050
MEMBER_COUNT = 317
MEMBER_BYTES = 16604530
SNAPSHOT_MANIFEST_SHA256 = '3210a913e354fa10ca71763471477b8afc55bcfd31b0615a367b99e6d3e29f50'
REVISION = '4d1f76f061ac961ee75c4d7d8b067b5fa0ac30f7'
PREFIX = 'lp-whole-call-prefix-pilot/'
SCRIPT_NAMES = (
    'common.py', 'pivot_selectors.py', 'lp_check.py', 'observer.py',
    'check_evidence.py', 'controls.py', 'runner.py', 'inputs.json', 'PROTOCOL.md',
)
RESULT_NAMES = ('controls.json', 'audit.json')
LOG_NAMES = ('controls.log', 'controls-replay.log', 'audit.log', 'replay.log')
RESULT_SHA256 = {'audit.json': 'eae88675319d3e03d9f6e3d7321119458e4c15e3fc999206975d67355e8897d1',
 'controls.json': '8a6afe283b1af96eda56c24e69b79d1145a1b70182ff1e40e5566d3002f73981'}
EXPECTED_RETURNED = {'command': 'check',
 'passed': True,
 'summary': {'audit': {'arm_order': ['prepared_bland', 'prepared_dantzig_lex'],
                       'calls': 14,
                       'complete': 13,
                       'diagrams': 7,
                       'discovery_used': False,
                       'inconclusive': 1,
                       'queries': 449,
                       'whole_call_shared_budgets': True},
             'controls': {'callback_arms': 2,
                          'legacy_cases': 10,
                          'nested_cases': 96,
                          'polynomial_cases': 22,
                          'validation_cases': 8}}}
EXPECTED_CALL_SUMMARIES_SHA256 = '4e08addedfbd5b0aa0d21ab083b5e16c2265027daf8e70b36250fbcf14cbf178'
EXPECTED_COMPARISONS = [{'case_id': 'circle',
  'common_completed_verdict': 'UNKNOT',
  'common_labelled_source_prefix': 3,
  'exact_typed_endpoint_equality': True,
  'first_divergence': None,
  'h_transport_claimed': False,
  'source_path_lengths': [3, 3]},
 {'case_id': 'trefoil',
  'common_completed_verdict': 'KNOTTED',
  'common_labelled_source_prefix': 17,
  'exact_typed_endpoint_equality': True,
  'first_divergence': None,
  'h_transport_claimed': False,
  'source_path_lengths': [17, 17]},
 {'case_id': 'figure_eight',
  'common_completed_verdict': 'KNOTTED',
  'common_labelled_source_prefix': 21,
  'exact_typed_endpoint_equality': True,
  'first_divergence': None,
  'h_transport_claimed': False,
  'source_path_lengths': [21, 21]},
 {'case_id': 'TT',
  'common_completed_verdict': 'KNOTTED',
  'common_labelled_source_prefix': 33,
  'exact_typed_endpoint_equality': True,
  'first_divergence': None,
  'h_transport_claimed': False,
  'source_path_lengths': [33, 33]},
 {'case_id': 'T25',
  'common_completed_verdict': 'KNOTTED',
  'common_labelled_source_prefix': 31,
  'exact_typed_endpoint_equality': True,
  'first_divergence': None,
  'h_transport_claimed': False,
  'source_path_lengths': [31, 31]},
 {'case_id': 'T27',
  'common_completed_verdict': 'KNOTTED',
  'common_labelled_source_prefix': 45,
  'exact_typed_endpoint_equality': True,
  'first_divergence': None,
  'h_transport_claimed': False,
  'source_path_lengths': [45, 45]},
 {'case_id': 'W34',
  'common_completed_verdict': None,
  'common_labelled_source_prefix': 40,
  'exact_typed_endpoint_equality': True,
  'first_divergence': None,
  'h_transport_claimed': False,
  'source_path_lengths': [40, 40]}]
COVERAGE = dict(polynomial_control_cases=22, legacy_control_cases=10,
    nested_control_cases=96, callback_arms=2, invalid_control_cases=8,
    diagrams=7, whole_calls=14, arms=2)


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
    assert type(ARCHIVE_SHA256) is str and type(ARCHIVE_BYTES) is int, 'Archive constants not frozen'
    archive_path = Path(archive_path)
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
    assert manifest['schema'] == 'whole-call-prefix-source-snapshot-v1'
    assert manifest['revision'] == REVISION
    assert type(manifest['files']) is dict and len(manifest['files']) == 301
    expected = {PREFIX + 'snapshot/' + name for name in manifest['files']}
    expected.add(manifest_name)
    expected.update(PREFIX + name for name in SCRIPT_NAMES + RESULT_NAMES + LOG_NAMES)
    assert set(payloads) == expected, 'Archive inventory differs from the frozen pilot'
    for name, expected_hash in manifest['files'].items():
        assert digest(payloads[PREFIX + 'snapshot/' + name]) == expected_hash
    for name, expected_hash in RESULT_SHA256.items():
        assert digest(payloads[PREFIX + name]) == expected_hash
    return payloads


def call_summaries(audit):
    """Retained observations, accepted only after complete independent replay.

    Native reported work counters are diagnostic; conservation and caps are
    checked by the archived checker, not a reconstruction of execution.
    Source ledgers contain exact labelled source digests, not isomorphism IDs.
    """
    return [dict(case_id=call['case_id'], arm=call['arm'],
        status=call['result']['status'], reason=call['result'].get('reason'),
        result_sha256=call['result_sha256'], stats=call['result']['stats'],
        source_ledger=call['source_ledger'], replay=call['replay'])
        for call in audit['calls']]


def replay(archive_path, json_out, text_out):
    archive_path, json_out, text_out = (Path(p).resolve() for p in (archive_path, json_out, text_out))
    assert len({archive_path, json_out, text_out, Path(__file__).resolve()}) == 4
    for output in (json_out, text_out):
        if output.exists():
            raise FileExistsError('Refuse to overwrite retained replay output: ' + str(output))
    result = dict(schema='whole-call-prefix-archive-replay-v1', passed=False,
        phase='archive_validation', failures=[],
        archive=dict(path=str(archive_path), sha256=ARCHIVE_SHA256, bytes=ARCHIVE_BYTES),
        archive_members={}, member_count=MEMBER_COUNT, member_bytes=MEMBER_BYTES,
        snapshot_manifest_sha256=SNAPSHOT_MANIFEST_SHA256, snapshot_revision=REVISION,
        replay_helper_sha256=digest(Path(__file__).read_bytes()),
        discovery_disabled=True, current_native_imported=False,
        archived_native_snapshot_only=True, timings_claimed=False,
        whole_call_shared_budget_claimed=True, general_quasipolynomial_claimed=False)
    save(json_out, result)
    try:
        payloads = checked_members(archive_path)
        result['archive_members'] = {
            name: dict(bytes=len(content), sha256=digest(content))
            for name, content in sorted(payloads.items())
        }
        result['phase'] = 'isolated_replay'
        save(json_out, result)
        with tempfile.TemporaryDirectory(prefix='whole-call-prefix-replay-') as temporary:
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
            command = [sys.executable, '-B', '-S', str(pilot_root / 'runner.py'), 'check',
                '--controls', str(pilot_root / 'controls.json'),
                '--audit', str(pilot_root / 'audit.json')]
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
            audit = json.loads(payloads[PREFIX + 'audit.json'])
            summaries = call_summaries(audit)
            assert digest(json.dumps(summaries, sort_keys=True, separators=(',', ':')).encode()) == EXPECTED_CALL_SUMMARIES_SHA256
            assert same(audit['comparisons'], EXPECTED_COMPARISONS)
            result['call_summaries'] = summaries
            result['comparisons'] = audit['comparisons']
            result['coverage'] = COVERAGE
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
