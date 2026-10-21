"""Check saved phase-five source/record/log evidence without running Lean.

Default scope is the historical executed checkpoint. --repo additionally checks
current source bytes and provider paths. Neither mode inspects live objects.
"""
from pathlib import Path, PurePosixPath
import argparse
import json
import tarfile
from evidence import binary_name, digest, manifest_hash, save, sha, validate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists(), 'Refusing to overwrite a receipt'
    packet = args.packet.resolve()
    summary = json.loads((packet / 'result.json').read_text())
    index = json.loads((packet / 'index.json').read_text())
    archive = packet / 'execution.tar.gz'
    assert sha(archive) == summary['execution_archive_sha256']
    members = {}
    with tarfile.open(archive, 'r:gz') as stream:
        for entry in stream:
            path = PurePosixPath(entry.name)
            assert entry.isfile() and not path.is_absolute() and '..' not in path.parts
            assert not binary_name(path) and entry.name not in members
            data = stream.extractfile(entry).read()
            assert index[entry.name] == {'sha256': digest(data), 'bytes': len(data)}
            members[entry.name] = data
    assert set(members) == set(index) and len(index) == summary['archive_members']
    raw_result = json.loads(members['execution/result.json'])
    assert all(summary[key] == value for key, value in raw_result.items())
    live_bytes = members.pop('review/live-review.json')
    live = json.loads(live_bytes)
    assert live['status'] == 'PASS_LIVE_POST_AUDIT_REVIEW'
    assert digest(live_bytes) == summary['live_review_sha256']
    assert (packet / 'live-review.json').read_bytes() == live_bytes
    for name, key in [('review.py', 'reviewer_sha256'), ('evidence.py', 'validator_sha256'),
                      ('capture.py', 'capture_sha256')]:
        assert digest(members['review/' + name]) == live[key]
    for name in ('evidence.py', 'review_saved.py', 'phase4_evidence.py', 'phase3_evidence.py'):
        assert (packet / name).read_bytes() == members['review/' + name]
    assert manifest_hash(members) == live['evidence_manifest_sha256']
    assert live['all184_objects_rehashed_after_audits']
    assert live['all185_basis_objects_and_logs_unchanged']
    assert live['current_inventory_exact'] and live['toolchain_and_compiler_rehashed']
    checked = validate(members, args.repo)
    assert all(live[key] == value for key, value in checked.items())
    assert summary['compiled_objects_in_archive'] is False
    assert summary['audit_warnings'] == 0
    assert summary['project_warnings'] == checked['project_warnings']
    receipt = {'status': 'PASS_SAVED_EVIDENCE_REVIEW', **checked,
               'compiled_objects_in_archive': False, 'archive_members': len(index),
               'archive_sha256': sha(archive), 'summary_sha256': sha(packet / 'result.json'),
               'reviewer_sha256': sha(__file__), 'validator_sha256': sha(Path(__file__).with_name('evidence.py')),
               'current_checkpoint_sources_checked': args.repo is not None,
               'scope': 'Saved 184 source snapshots and exact imports, source/dependency/object hash '
                        'records, compiler commands and raw logs, complete 185-module immutable basis provenance and two '
                        'typed audits. No compiler execution, archived-code execution or live-object '
                        'verification. Later source changes do not rewrite this checkpoint.'}
    save(args.output, receipt)
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
