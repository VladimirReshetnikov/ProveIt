"""Stage a completed phase-three packet without modifying repository evidence.

Requires a matching independent live review; writes a new output directory.
Compiled objects are deliberately excluded. No compiler or archived code runs.
"""
from pathlib import Path
import argparse
import gzip
import io
import json
import tarfile
from capture import arguments, collect
from evidence import digest, manifest, manifest_hash, save, sha, validate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    arguments(parser)
    parser.add_argument('--live-review', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    assert not args.out.exists(), 'Refusing to overwrite a packet'
    members = collect(args)
    live_bytes = args.live_review.read_bytes()
    live = json.loads(live_bytes)
    assert live['status'] == 'PASS_LIVE_POST_AUDIT_REVIEW'
    assert live['evidence_manifest_sha256'] == manifest_hash(members)
    checked = validate(members)
    assert all(live[key] == value for key, value in checked.items())
    assert live['all185_objects_rehashed_after_audits']
    assert live['all185_basis_objects_and_logs_unchanged']
    assert live['run'] == str(args.run.resolve()) and live['basis'] == str(args.basis.resolve())
    assert digest(members['review/review.py']) == live['reviewer_sha256']
    assert digest(members['review/evidence.py']) == live['validator_sha256']
    assert digest(members['review/capture.py']) == live['capture_sha256']
    members['review/live-review.json'] = live_bytes
    index = manifest(members)
    out = args.out.resolve()
    out.mkdir()
    with (out / 'execution.tar.gz').open('xb') as raw:
        with gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as zipped:
            with tarfile.open(fileobj=zipped, mode='w') as archive:
                for name, data in sorted(members.items()):
                    info = tarfile.TarInfo(name)
                    info.size, info.mode, info.mtime = len(data), 0o644, 0
                    archive.addfile(info, io.BytesIO(data))
    save(out / 'index.json', index)
    result = json.loads(members['execution/result.json'])
    summary = {**result, 'project_warnings': checked['project_warnings'], 'audit_warnings': 0,
               'archive_members': len(index), 'execution_archive_sha256': sha(out / 'execution.tar.gz'),
               'live_review_sha256': digest(live_bytes), 'compiled_objects_in_archive': False,
               'source_checkpoint_scope': 'All 185 exact source snapshots are archived. Basis '
                                          'ledgers/logs remain unchanged; later corrections are additive.'}
    save(out / 'result.json', summary)
    (out / 'live-review.json').write_bytes(live_bytes)
    for name in ('review_saved.py', 'evidence.py'):
        (out / name).write_bytes(members['review/' + name])
    (out / 'README.md').write_text(f'''# Lean phase-three proof simplification

The 215-state endpoint passed with the complete 185-module project closure and only Lean's shipped `Init` boundary. This checkpoint freshly compiled {result['fresh_modules']} affected modules and reused {result['reused_modules']} phase-two objects after checking their source, direct dependencies, object and saved-log hashes. It is an incremental kernel check of the complete closure, not a new fresh compilation of every module.

Both typed endpoint audit clients passed: `EndpointAudit215` produced two axiom reports and `K215Audit` eight. Every report contains only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero audit warnings. The selected source-module logs contain {checked['project_warnings']} linter warnings. The independent live review checked all 185 private objects and the immutable 185-object phase-two basis after checking the audit objects and reports.

[result.json](result.json) and [live-review.json](live-review.json) record the final boundary. [index.json](index.json) binds each member of `execution.tar.gz`: all 185 source snapshots; exact source/import/object/dependency ledgers; every fresh attempt's source, command, raw log and record; both typed clients; original runners; and the read-only reviewers. Failed historical attempts, if present, remain separate from the selected PASS ledger. Compiled objects are excluded.

The archive's `basis/` directory preserves the original phase-two inventory, completed ledger, owner, result, raw selected logs and live review, together with the retained phase-one origin records. These are copied bytes, not rewritten histories. The copied toolchain file retains its original 204-module description; only its compiler and shipped-core identities are inherited here. The phase-three inventory and result establish the current 185-module scope. [Phase-two evidence](../../phase2/lean/README.md) and [phase-one evidence](../../lean/README.md) remain the predecessor checkpoints.

Run the portable saved-evidence check with:

```sh
python3 review_saved.py --output /tmp/k215-phase3-saved-review.json
```

This checks the archive without executing Lean or any archived runner. It verifies all 185 source snapshots and imports, exact dependency/object hash records, inherited log bindings, fresh compiler commands and the two audit reports. Optional `--repo /path/to/Proofs` additionally requires every checkpoint source and unique provider path to remain current. Neither mode rechecks live compiled objects; that claim belongs to the separately saved live review. The [maintained fresh-build driver](../../../lean/README.md) provides the independent full rebuild route. Original executed scripts retain their historical scratch paths.
''')
    print(json.dumps({'status': 'STAGED_SAVED_PACKET', 'path': str(out),
                      'members': len(index), 'archive_bytes': (out / 'execution.tar.gz').stat().st_size,
                      'summary_sha256': sha(out / 'result.json')}, indent=2))


if __name__ == '__main__':
    main()
