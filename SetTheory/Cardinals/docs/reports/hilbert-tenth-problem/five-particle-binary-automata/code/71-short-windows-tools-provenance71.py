#!/usr/bin/env python3
"""Owned read-only Report71 provenance authentication and endpoint comparison.
No retained/source/audit scientific program is loaded, imported or executed.
Run with python3 -I -S -B; output must be a fresh external directory.
"""
import argparse
import hashlib
import io
import os
from pathlib import Path
import stat
import sys
import types
import zipfile

ROOT = Path(__file__).absolute().parent.parent
HELPER_SHA256 = '283142424d8b0eeeaf289a0908a80896f76146efd64b3a54cfa004b28f1d167c'
BASELINE_SHA256 = 'd47017623dd7104ed32a65a578a5ac65bb4143574dac3e82182c9864fa1535ad'
PIN_MAIN = '72f8024c49a364bfd26ccc9f0e89d128e4390c1bf045477aa3d584bba3eaea31'
PIN_PROOF = 'd2229bcae33affd26eefb513e942891edf1d09c8b8d9e32ab1f8220fd2ea9962'
PIN_AUDIT = 'befa9a29fd2c31a93bfecdda67794a830e5ebbedc71c4c76b85fd3fb4f161614'
PIN_AUDIT_TEXT = '09cca9ebcc31338b083a502f3345e7825869fcdf043350ce16421d4ef5f7b9bd'
PIN_OLD = 'f1c19ca86641cbf5ebaed81d0c78e82563258753bbf8f38f2f46229247b71fa0'
PIN_ACCEPTED = '3bfe65db1ad9c0aab9fd13641cfbad843a292d2c2dbec444fa0f7ebb856876b1'
ORIGINALS = tuple(Path('/workspace/shared') / n for n in ('short-exactness-radius-20261004', 'short-exactness-independent-audit-20261004', 'radius-frontier-20261004', 'report70-two-scale-radius-release-20261004'))


def helper():
    p = ROOT / 'tools/release71.py'
    for q in (p, *p.parents):
        if stat.S_ISLNK(q.lstat().st_mode):
            raise ValueError('Symlink helper path')
    s = p.lstat()
    if not stat.S_ISREG(s.st_mode) or s.st_nlink != 1:
        raise ValueError('Unsafe helper')
    with os.fdopen(os.open(p, os.O_RDONLY | os.O_NOFOLLOW), 'rb') as f:
        data = f.read()
    if hashlib.sha256(data).hexdigest() != HELPER_SHA256:
        raise ValueError('Changed inspected helper')
    h = types.ModuleType('report71_owned_release')
    h.__file__ = str(p)
    exec(compile(data, str(p), 'exec'), h.__dict__)
    return h


def main():
    if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize):
        raise ValueError('Use python3 -I -S -B without optimization')
    h = helper()
    h.canonical(Path(__file__).absolute())
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir', required=True)
    ap.add_argument('--compare-originals', action='store_true')
    a = ap.parse_args()
    out = h.new_output(a.output_dir)
    release_before = h.snapshot(allow_empty=True)
    h.check_inputs()
    counts = {}

    def pinned(p, pin):
        data = h.read(p)
        h.require(h.sha(data) == pin, 'Pinned document mismatch: ' + str(p))
        return h.parse(data)

    def entry(p, row):
        data = h.read(p)
        h.require(len(data) == row['bytes'] and h.sha(data) == row['sha256'], 'Manifest payload mismatch: ' + str(p))
        s = p.lstat()
        if 'mode_octal' in row:
            h.require(stat.S_IMODE(s.st_mode) == int(row['mode_octal'], 8), 'Manifest mode mismatch: ' + str(p))
        if 'mtime_ns' in row:
            h.require(s.st_mtime_ns == row['mtime_ns'], 'Manifest mtime mismatch: ' + str(p))

    mainroot = ROOT / 'science/proof-packet'
    auditroot = ROOT / 'audits/fresh-independent'
    oldroot = ROOT / 'science/predecessor-proof-packet'
    mainmanifest = pinned(mainroot / 'manifest.json', PIN_MAIN)
    auditmanifest = pinned(auditroot / 'MANIFEST.json', PIN_AUDIT)
    oldmanifest = pinned(oldroot / 'manifest.json', PIN_OLD)
    h.require(h.sha(h.read(mainroot / 'PROOF.md')) == PIN_PROOF, 'Main proof pin mismatch')
    h.require(h.sha(h.read(auditroot / 'AUDIT.md')) == PIN_AUDIT_TEXT, 'Audit text pin mismatch')
    for label, root, manifest, exclusions in (
            ('main_packet', mainroot, mainmanifest, {'manifest.json'}),
            ('fresh_audit', auditroot, auditmanifest, {'MANIFEST.json', 'MANIFEST.json.sha256'}),
            ('predecessor_packet', oldroot, oldmanifest, {'manifest.json'})):
        files = h.inventory(root)['files']
        h.require(set(files) == set(manifest['files']) | exclusions, 'Manifest object-set mismatch: ' + label)
        for name, row in manifest['files'].items():
            entry(root / h.relative_name(name), row)
        counts[label + '_entries'] = len(manifest['files'])
    h.require(h.read(auditroot / 'MANIFEST.json.sha256').decode().split() == [PIN_AUDIT, 'MANIFEST.json'], 'Audit digest sidecar mismatch')
    h.require(auditmanifest['source_manifest_sha256'] == PIN_MAIN and auditmanifest['status'] == 'PASS', 'Fresh audit source binding mismatch')
    accepted = pinned(ROOT / 'audits/accepted-static/AUDIT_MANIFEST.json', PIN_ACCEPTED)
    for name, row in accepted['files'].items():
        parts = h.relative_name(name).split('/', 1)
        h.require(len(parts) == 2 and parts[0] in ('fresh-audit-static', 'fresh-audit-radius2'), 'Unexpected accepted-audit path')
        location = 'accepted-static' if parts[0] == 'fresh-audit-static' else 'accepted-radius2'
        entry(ROOT / 'audits' / location / parts[1], row)
    counts['accepted_audit_entries'] = len(accepted['files'])

    sourcezip = ROOT / 'science/source-packet-seal/short-exactness-proof-packet-20261004.zip'
    seal = h.parse(h.read(ROOT / 'science/source-packet-seal/seal-receipt.json'))
    sourcebytes = h.read(sourcezip)
    h.require(h.sha(sourcebytes) == seal['archive_sha256'] == auditmanifest['source_zip_sha256'], 'Source archive pin mismatch')
    h.require(seal['manifest_sha256'] == PIN_MAIN, 'Seal/source manifest mismatch')
    with zipfile.ZipFile(io.BytesIO(sourcebytes)) as archive:
        expected = ['proof-packet/' + n for n in sorted(h.inventory(mainroot)['files'])]
        h.require(archive.namelist() == expected and archive.testzip() is None, 'Source ZIP object set or CRC mismatch')
        for n in expected:
            h.require(archive.read(n) == h.read(mainroot / n[len('proof-packet/'):]), 'Source ZIP bytes differ')
    counts['source_zip_files'] = len(expected)

    origins = h.parse(h.read(mainroot / 'dependency-origins.json'))
    retained_map = h.parse(h.read(ROOT / 'qa/SOURCE_ORIGINS.json'))
    def retained_origin(original):
        choices = [(Path(source), ROOT / target) for target, source in retained_map.items()]
        for source, retained in sorted(choices, key=lambda pair: -len(str(pair[0]))):
            if Path(original) == source or source in Path(original).parents:
                return retained / Path(original).relative_to(source)
        raise ValueError('No retained origin: ' + original)
    oldarchivebytes = h.read(oldroot / 'original/report26.zip')
    h.require(h.sha(oldarchivebytes) == oldmanifest['original_archive_sha256'], 'Report26 archive pin mismatch')
    with zipfile.ZipFile(io.BytesIO(oldarchivebytes)) as archive:
        names = archive.namelist()
        h.require(len(names) == len(set(names)) and archive.testzip() is None, 'Report26 ZIP duplicates or CRC failure')
        prefix = 'parallel-involution-report26/'
        for name in names:
            h.require(name.startswith(prefix), 'Unexpected Report26 prefix')
            h.relative_name(name)
        for name, row in origins.items():
            data = h.read(mainroot / 'dependencies' / h.relative_name(name))
            h.require(h.sha(data) == row['sha256'] and len(data) == row['bytes'], 'New dependency origin mismatch')
            if 'source_archive' in row:
                h.require(row['archive_sha256'] == h.sha(oldarchivebytes), 'Dependency archive pin mismatch')
                original = archive.read(row['member'])
            else:
                original = h.read(retained_origin(row['source']))
            h.require(original == data, 'Retained dependency/origin bytes mismatch')
        counts['new_dependency_origins'] = len(origins)
        release = h.parse(archive.read(prefix + 'release-manifest.json'))
        h.require(h.read(oldroot / 'dependencies/release-manifest.json') == archive.read(prefix + 'release-manifest.json'), 'Report26 manifest copy mismatch')
        h.require(set(names) == {prefix + n for n in release['files']} | {prefix + 'release-manifest.json', prefix + 'release-manifest.json.sha256'}, 'Report26 exact inventory mismatch')
        h.require(archive.read(prefix + 'release-manifest.json.sha256').decode().split()[0] == h.sha(archive.read(prefix + 'release-manifest.json')), 'Report26 manifest sidecar mismatch')
        for name, row in release['files'].items():
            data = archive.read(prefix + h.relative_name(name))
            h.require(len(data) == row['bytes'] and h.sha(data) == row['sha256'], 'Report26 release payload mismatch')
        pins = h.parse(archive.read(prefix + 'source-pins.json'))
        h.require(h.read(oldroot / 'dependencies/source-pins.json') == archive.read(prefix + 'source-pins.json'), 'Report26 source-pin copy mismatch')
        for name, pin in pins['files'].items():
            h.require(h.sha(archive.read(prefix + h.relative_name(name))) == pin, 'Report26 source pin mismatch')
        scientific = h.parse(archive.read(prefix + 'scientific/manifest.json'))
        for name, row in scientific['files'].items():
            data = archive.read(prefix + 'scientific/' + h.relative_name(name))
            h.require(len(data) == row['bytes'] and h.sha(data) == row['sha256'], 'Report26 scientific manifest mismatch')
        lines = archive.read(prefix + 'scientific/SHA256SUMS').decode().splitlines()
        for line in lines:
            pin, name = line.split(None, 1)
            h.require(h.sha(archive.read(prefix + 'scientific/' + h.relative_name(name))) == h.digest(pin), 'Report26 SHA256SUMS mismatch')
        old_dependencies = {'COMPILER_PROOF.md': 'scientific/COMPILER_PROOF.md', 'PROOF.md': 'scientific/PROOF.md', 'audit-preservation.md': 'scientific/audit-preservation.md', 'prior-art-audit.md': 'references/prior-art-audit.md', 'release-manifest.json': 'release-manifest.json', 'report19-audit-universal-count.json': 'references/report19-audit-universal-count.json', 'report19-universal-receipt.json': 'references/report19-universal-receipt.json', 'resource-ledger.json': 'scientific/resource-ledger.json', 'source-pins.json': 'source-pins.json'}
        for copy, member in old_dependencies.items():
            h.require(h.read(oldroot / 'dependencies' / copy) == archive.read(prefix + member), 'Predecessor dependency differs from archive')
        counts['predecessor_dependency_origins'] = len(old_dependencies)
        counts.update(report26_archive_files=len(names), report26_release_entries=len(release['files']), report26_source_pins=len(pins['files']), report26_scientific_entries=len(scientific['files']), report26_sha256sum_lines=len(lines))

    historical_before = h.parse(h.read(mainroot / 'evidence/before.json'))
    historical_after = h.parse(h.read(mainroot / 'evidence/after.json'))
    historical_receipt = h.parse(h.read(mainroot / 'evidence/preservation-receipt.json'))
    def delta(first, last):
        return {p: {'before': first.get(p), 'after': last.get(p)} for p in sorted(set(first) | set(last)) if first.get(p) != last.get(p)}
    historical_changes = {scope: delta(historical_before[scope], historical_after[scope]) for scope in ('frozen_inputs', 'separately_observed_live_report70')}
    h.require(historical_changes == historical_receipt['changes'] and not historical_changes['frozen_inputs'], 'Historical endpoint delta mismatch')
    live_changes = historical_changes['separately_observed_live_report70']
    h.require(len([p for p, row in live_changes.items() if row['before'] is None]) == 49 and len([p for p, row in live_changes.items() if row['before'] is not None]) == 1, 'Historical concurrent change qualification differs')
    audit_before = h.parse(h.read(auditroot / 'before.json'))
    audit_after = h.parse(h.read(auditroot / 'after.json'))
    audit_preservation = h.parse(h.read(auditroot / 'preservation.json'))
    audit_changes = {scope: delta(audit_before[scope], audit_after[scope]) for scope in ('frozen_inputs', 'live_report70')}
    h.require(audit_changes == audit_preservation['changes'] and not any(audit_changes.values()), 'Fresh audit endpoint evidence mismatch')
    counts.update(historical_frozen_entries=len(historical_before['frozen_inputs']), historical_live_added_entries=49, historical_live_changed_existing_entries=1, fresh_audit_frozen_entries=len(audit_before['frozen_inputs']))
    receipt = {'status': 'PASS', 'counts': counts, 'main_manifest_sha256': PIN_MAIN, 'proof_sha256': PIN_PROOF, 'audit_manifest_sha256': PIN_AUDIT, 'audit_text_sha256': PIN_AUDIT_TEXT, 'source_archive_sha256': h.sha(sourcebytes), 'scientific_programs_executed': False, 'scope': 'Read-only byte, metadata, archive and nested provenance authentication, not a scientific replay', 'historical_live_report70_was_not_static': True, 'fresh_audit_endpoint_equality_is_not_continuous_immutability': True}
    endpoint = None
    if a.compare_originals:
        baseline = pinned(ROOT / 'qa/ORIGINAL_ENDPOINT_BEFORE.json', BASELINE_SHA256)
        h.require(set(baseline['trees']) == {str(p) for p in ORIGINALS}, 'Unexpected original roots')
        current = {}
        for root in ORIGINALS:
            h.canonical(root)
            rows = {}
            for path in [root, *sorted(root.rglob('*'))]:
                s = path.lstat()
                h.require(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode), 'Nonregular original')
                row = {'mode': stat.S_IMODE(s.st_mode), 'mtime_ns': s.st_mtime_ns, 'type': 'directory' if stat.S_ISDIR(s.st_mode) else 'file'}
                if row['type'] == 'file':
                    data = h.read(path)
                    row.update(bytes=len(data), sha256=h.sha(data))
                rows[str(path)] = row
            current[str(root)] = rows
        changes = {root: delta(baseline['trees'][root], current[root]) for root in baseline['trees']}
        endpoint = {'status': 'PASS' if not any(changes.values()) else 'FAIL', 'baseline_sha256': BASELINE_SHA256, 'scope': baseline['scope'], 'changes': changes, 'trees': current}
        h.require(not any(changes.values()), 'Original endpoint changed: ' + str({k: list(v) for k, v in changes.items() if v}))
        receipt['original_endpoint_equality'] = True
    h.require(h.snapshot(allow_empty=True) == release_before, 'Release changed during provenance verification')
    out.mkdir(mode=0o700)
    h.write_new(out / 'SOURCE_MANIFEST_VERIFICATION.json', h.encoded(receipt))
    if endpoint is not None:
        h.write_new(out / 'ORIGINAL_ENDPOINT_AFTER.json', h.encoded(endpoint))
    print(h.encoded(receipt).decode())


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, KeyError, zipfile.BadZipFile) as error:
        print('PROVENANCE REFUSED: ' + str(error), file=sys.stderr)
        raise SystemExit(2)
