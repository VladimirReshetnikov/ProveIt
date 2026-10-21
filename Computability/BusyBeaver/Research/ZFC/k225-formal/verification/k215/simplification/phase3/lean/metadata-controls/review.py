"""Independently review a completed phase-three run and its live provider set.

Read-only: this script does not import any runner or execute any compiler.
"""
from pathlib import Path
import argparse
import json
from capture import arguments, collect, FORMAL
from evidence import digest, manifest_hash, save, sha, validate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    arguments(parser)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists(), 'Refusing to overwrite a receipt'
    members = collect(args)
    owner = json.loads(members['execution/owner.json'])
    repo = Path(owner['repo'])
    checked = validate(members, repo)
    run, basis = args.run.resolve(), args.basis.resolve()
    done = json.loads(members['execution/completed.json'])
    old = json.loads(members['basis/completed.json'])
    inventory = json.loads(members['execution/inventory.json'])
    toolchain = json.loads(members['execution/toolchain.json'])
    result = json.loads(members['execution/result.json'])
    basis_logs = json.loads(members['execution/basis-logs.json'])
    expected = {m.replace('.', '/') + '.olean' for m in done}
    for directory in (run / 'objects', basis / 'objects'):
        paths = list(directory.rglob('*'))
        assert all(not p.is_symlink() for p in paths)
        assert {p.relative_to(directory).as_posix() for p in paths if p.is_file()} == expected
    for key in ('lean', 'lake', 'Init.olean', 'project_toolchain'):
        assert sha(toolchain[key]['path']) == toolchain[key]['sha256']
    assert sha(repo / FORMAL / 'verification/k215/lean/build.py') == owner['helper_sha256']
    for row in result['audits']:
        folder = Path(row['log']).parent
        assert sha(folder / (row['module'] + '.olean')) == row['object_sha256']
        assert sha(folder / (row['module'] + '.lean')) == row['source_sha256']
        assert sha(row['source']) == row['source_sha256']
        assert sha(row['log']) == row['log_sha256']
    # Deliberately after both typed audit objects, saved reports and source checks.
    for entry in inventory['modules']:
        module = entry['module']
        row = done[module]
        assert sha(entry['source']) == row['source_sha256']
        assert sha(run / 'objects' / (module.replace('.', '/') + '.olean')) == row['object_sha256']
        assert sha(row['log']) == row['log_sha256']
        assert sha(basis / 'objects' / (module.replace('.', '/') + '.olean')) == old[module]['object_sha256']
        assert sha(basis_logs[module]) == old[module]['log_sha256']
    # Re-read all captured records, sources and raw logs after object inspection.
    assert collect(args) == members, 'Evidence changed during read-only review'
    receipt = {
        'status': 'PASS_LIVE_POST_AUDIT_REVIEW', **checked,
        'all185_objects_rehashed_after_audits': True,
        'all185_basis_objects_and_logs_unchanged': True,
        'current_inventory_exact': True,
        'toolchain_and_compiler_rehashed': True,
        'evidence_manifest_sha256': manifest_hash(members),
        'reviewer_sha256': sha(__file__),
        'validator_sha256': sha(Path(__file__).with_name('evidence.py')),
        'capture_sha256': sha(Path(__file__).with_name('capture.py')),
        'run': str(run), 'basis': str(basis),
        'scope': 'Read-only current sources/imports, exact 185 private providers, direct dependency '
                 'objects, compiler/toolchain, original logs and both audit objects. All current '
                 'and basis objects rehashed after the audit checks; no compiler rerun. The phase2 '
                 'and phase1 records retain their original identities and historical scopes.'}
    save(args.output, receipt)
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
