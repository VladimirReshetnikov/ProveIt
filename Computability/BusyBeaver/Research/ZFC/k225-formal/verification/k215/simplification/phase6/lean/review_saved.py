"""Read saved phase-six evidence and its exact published phase-five reference.

No Lean or archived runner is executed. Optional --repo checks current sources;
--basis-repo locates historical predecessor evidence without that extra claim.
"""
from pathlib import Path, PurePosixPath
import argparse
import json
import tarfile
import basis_reference
from evidence import binary_name, digest, manifest_hash, save, sha, validate


def read_members(archive, index):
    members = {}
    with tarfile.open(archive, 'r:gz') as stream:
        for entry in stream:
            path = PurePosixPath(entry.name)
            assert entry.isfile() and not path.is_absolute() and '..' not in path.parts
            assert not binary_name(path) and entry.name not in members
            data = stream.extractfile(entry).read()
            assert index[entry.name] == {'sha256': digest(data), 'bytes': len(data)}
            members[entry.name] = data
    assert set(members) == set(index)
    return members


def review(packet, repo=None, basis_repo=None):
    packet = packet.resolve()
    summary = json.loads((packet / 'result.json').read_text())
    index = json.loads((packet / 'index.json').read_text())
    archive = packet / 'execution.tar.gz'
    assert sha(archive) == summary['execution_archive_sha256']
    members = read_members(archive, index)
    assert len(index) == summary['archive_members']
    raw = json.loads(members['execution/result.json'])
    assert all(summary[k] == v for k, v in raw.items())
    live_bytes = members.pop('review/live-review.json')
    live = json.loads(live_bytes)
    assert live['status'] == 'PASS_LIVE_POST_AUDIT_REVIEW'
    assert digest(live_bytes) == summary['live_review_sha256']
    assert (packet / 'live-review.json').read_bytes() == live_bytes
    for name, key in [('review.py', 'reviewer_sha256'), ('evidence.py', 'validator_sha256'),
                      ('capture.py', 'capture_sha256')]:
        assert digest(members['review/' + name]) == live[key]
    for name in ('evidence.py', 'basis_reference.py', 'basis-reference.json', 'review_saved.py'):
        assert (packet / name).read_bytes() == members['review/' + name]
    assert manifest_hash(members) == live['evidence_manifest_sha256']
    assert live['all187_objects_rehashed_after_audits']
    assert live['all184_basis_objects_and_logs_unchanged']
    assert live['current_inventory_exact'] and live['toolchain_and_compiler_rehashed']
    assert live['basis_reference_sha256'] == basis_reference.REFERENCE_SHA256
    checked = validate(members, repo, basis_repo or repo)
    assert all(live[k] == v for k, v in checked.items())
    assert summary['compiled_objects_in_archive'] is False
    assert summary['audit_warnings'] == 0 and summary['project_warnings'] == checked['project_warnings']
    return {'status': 'PASS_SAVED_EVIDENCE_REVIEW', **checked,
            'compiled_objects_in_archive': False, 'archive_members': len(index),
            'archive_sha256': sha(archive), 'summary_sha256': sha(packet / 'result.json'),
            'reviewer_sha256': sha(__file__), 'validator_sha256': sha(Path(__file__).with_name('evidence.py')),
            'basis_reference_sha256': basis_reference.REFERENCE_SHA256,
            'current_checkpoint_sources_checked': repo is not None,
            'scope': 'Saved187 source snapshots, exact imports/dependency/object hash records, '
                     'compiler commands and raw logs, 184-module basis ledgers/logs bound to the '
                     'exact published phase5 checkpoint, and two unchanged named typed clients. '
                     'No proof execution, archived-code execution, or live-object inspection.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--repo', type=Path)
    parser.add_argument('--basis-repo', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists(), 'Refusing to overwrite a receipt'
    receipt = review(args.packet, args.repo, args.basis_repo)
    save(args.output, receipt)
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
