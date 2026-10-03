#!/usr/bin/env python3
"""Verify mandatory local manifest pins, relevant scientific bytes, and exact edits.

This does not reread excluded historical artifacts or external source packages.
The original baseline's seven table identities are materialized and verified.
"""
from pathlib import Path
import hashlib
import json
import sys
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
from verify_pins import verify_inputs, KNOWN_SHA256, SOURCE_SHA256
from baseline_support import regenerated_baseline, OUTPUTS as BASELINE_OUTPUTS
from run_checks import OUTPUTS


def require(ok, detail):
    if not ok:
        raise RuntimeError(detail)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def read_manifest(name):
    return json.loads((ROOT / 'historical/source-manifests' / name).read_text())


def check_record(path, rec):
    require(path.is_file() and not path.is_symlink(), 'Missing/nonregular manifest input: ' + path.name)
    raw = path.read_bytes()
    require(len(raw) == rec['bytes'] and sha(raw) == rec['sha256'], 'Manifest scientific bytes mismatch: ' + path.name)


def main():
    pin_count = verify_inputs()
    optimized = read_manifest('optimized-source-manifest.json')
    baseline = read_manifest('baseline-source-manifest.json')
    predecessor = read_manifest('report17-manifest.json')
    producer = read_manifest('cellular-clock-manifest.json')
    audit = read_manifest('cellular-clock-audit-manifest.json')
    require(optimized['source_sha256'] == predecessor['source_sha256'] == SOURCE_SHA256, 'Optimized manifest identity')
    require(baseline['source_sha256'] == '38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a', 'Baseline manifest identity')
    original_manifests = {'report17': predecessor, 'cellular-clock': producer}
    changes = json.loads((ROOT / 'historical/report18-adaptations.json').read_text())['adaptations']
    by_target = {}
    for change in changes:
        target = change['portable_file']
        require(target not in by_target, 'Duplicate adaptation target')
        by_target[target] = change
        raw = (ROOT / target).read_bytes()
        require(sha(raw) == change['portable_sha256'], 'Portable adaptation identity: ' + target)
        lines = raw.decode('utf-8').splitlines(keepends=True)
        original = []; cursor = 0
        for edit in change['reverse_edits']:
            a, b = edit['portable_line_range']
            require(cursor <= a <= b <= len(lines), 'Invalid edit range')
            require(lines[a:b] == edit['portable_lines'], 'Portable edit mismatch')
            original.extend(lines[cursor:a]); original.extend(edit['original_lines']); cursor = b
        original.extend(lines[cursor:])
        reconstructed = ''.join(original).encode('utf-8')
        require(sha(reconstructed) == change['original_sha256'], 'Original reconstruction identity')
        rec = original_manifests[change['origin']]['files'][change['original_file']]
        require(change['original_sha256'] == rec['sha256'] and len(reconstructed) == rec['bytes'], 'Original manifest/edit mismatch')
    # Full retained Report17 inventory, with generated outputs explicitly distinguished.
    inherited = []
    for name, rec in predecessor['files'].items():
        if name in OUTPUTS or name == 'replay-receipt.json':
            require((ROOT / name).is_file(), 'Missing inherited canonical output: ' + name)
            status = 'REGENERATED_AND_COMPARED_BY_AGGREGATE'
        elif name in by_target:
            require(by_target[name]['origin'] == 'report17', 'Wrong inherited provenance')
            status = 'EXACT_PORTABILITY_EDIT_VERIFIED'
        else:
            check_record(ROOT / name, rec)
            status = 'BYTE_IDENTICAL'
        inherited.append({'file': name, 'status': status})
    # Every retained producer note/checker is either identical or reverse-verifiable.
    producer_files = ['CA_CLOCK_DOMINATION.md', 'audit/AUDIT.md', 'clock_verify.py',
                      'compare_empty_startup.py', 'verify_manifests.py', 'audit/check_ca_clock.py',
                      'audit/check_proof_corollaries.py', 'audit/check_old_new_startup.py']
    for name in producer_files:
        target = 'cellular-clock/' + name
        if target not in by_target:
            check_record(ROOT / target, producer['files'][name])
        else:
            require(by_target[target]['origin'] == 'cellular-clock', 'Wrong producer provenance')
    require(producer['proof_sha256'] == sha((HERE / 'CA_CLOCK_DOMINATION.md').read_bytes()) == audit['reviewed_proof_sha256'], 'Proof/audit manifest linkage')
    audit_path = ROOT / 'historical/source-manifests/cellular-clock-audit-manifest.json'
    require(producer['audit_manifest_sha256'] == sha(audit_path.read_bytes()), 'Audit manifest linkage')
    # Read all bundled immutable source entries shared with the original manifest.
    scientific = []
    for name in sorted(set(KNOWN_SHA256) & set(optimized['files'])):
        # Proof-only orientation notes were added after this source manifest.
        check_record(ROOT / name, optimized['files'][name]); scientific.append(name)
    with regenerated_baseline() as old:
        for name in BASELINE_OUTPUTS:
            check_record(old / name, baseline['files'][name])
    receipt = {'status': 'PASS', 'scope': 'Local mandatory manifest identities, exact reverse-verifiable portability edits, retained Report17 inventory, pinned scientific inputs, and all seven regenerated baseline source outputs. Excluded upstream files are not reread.',
               'mandatory_input_pins': pin_count, 'source_sha256': SOURCE_SHA256,
               'manifest_sha256': {p.name: sha(p.read_bytes()) for p in sorted((ROOT / 'historical/source-manifests').iterdir())},
               'inherited_files': inherited, 'producer_proof_and_checker_files': producer_files,
               'portable_edit_count': len(changes), 'scientific_source_entries_compared': scientific,
               'baseline_source_entries_compared': list(BASELINE_OUTPUTS),
               'proof_only_shared_offset_reference_sha256': sha((ROOT / 'certificate-reference/SHARED_OFFSET_PROOF.md').read_bytes()),
               'limitations': 'Hash/inventory and finite replay checks do not mechanically prove the theorems. Shared-offset certificate proof is reference-only; no certificate executable or universal polynomial is evaluated.'}
    (HERE / 'portable-input-manifest-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
