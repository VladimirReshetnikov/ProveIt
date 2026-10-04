#!/usr/bin/env python3
"""Owned final presentation seal. Execute only after final review approval.
No scientific program is imported or run. Receipts and replay stay external.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import runpy
import shutil
import stat
import subprocess
import sys

ROOT = Path('/workspace/shared/oeis-uniform-sectors-release-20261004')
OUT = Path('/workspace/shared/oeis-uniform-final-seal-20261004')
MANIFEST = Path('/workspace/shared/A196460-uniform-sectors-RELEASE_MANIFEST-20261004.json')
ZIP = Path('/workspace/shared/A196460-uniform-sectors-source-evidence-20261004.zip')
REPEAT = Path('/workspace/shared/A196460-uniform-sectors-source-evidence-repeat-20261004.zip')
PINS = '10ddbdee2fc822c63b437b3e4b84c57717d3ed7934f63aa05952f0e1aac19164'
LOCK = '6ee7f579ad072c7c57d76341d35c51742f8b976c40816ad305b12a9836f35d07'
PDF = 'e1689dc2ba86b8a1c01ac33897007bcafa3e6454f197b87920e56af87235b1df'
TEX = 'd0770c2f36b214204b13f7487f3d7299b2da96844de47f954cd717f5f78b3191'
PAGES = '4c6266dd79053b94a155b17b0148d23d6fb8ecb264f9d161b35420f29711decc'
MANUSCRIPT_REVIEW = 'c8099b42f7a758b7b1df4130ee3701ac56ccd9f17663237c8f5ad9c3dd95e58b'
TOOL_PINS = {
    'release.py': 'b98817cf30ce60dfb7aaac85b1633176225dec27b29698b25be95c065176ce87',
    'build_article.py': '881cdd3aa3658bed29b2ed70014285143f0ef1f2315eb1065b1f6aeef3f65072',
    'freeze_inputs.py': '30a5224ed75eb0a8b86f2f58b6dd7c4d508e824c63a6e2048472dcbd9e861782',
    'selftest.py': 'ea9ac2939a676bb2082966d979ed52cb3b4e6b4b909ce329bd201ccdebefbf53',
}
EXEMPT = ('inputs', 'qa/independent-manuscript-review', 'qa/independent-release-tool-review')


def need(test, message):
    if not test: raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def put(path, value):
    with path.open('x') as f:
        json.dump(value, f, sort_keys=True, indent=2); f.write('\n')


def main():
    need(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize, 'Use python3 -I -S -B')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--tools-review-manifest-name', required=True, choices=('MANIFEST.sha256', 'EVIDENCE_MANIFEST.json', 'REVIEW_MANIFEST.json'))
    ap.add_argument('--tools-review-pin', required=True)
    a = ap.parse_args()
    for name, pin in TOOL_PINS.items():
        p = ROOT / 'tools' / name
        for parent in [p, *p.parents]: need(not parent.is_symlink(), 'Symlink tool path')
        need(p.is_file() and p.stat().st_nlink == 1 and sha(p.read_bytes()) == pin, 'Reviewed tool differs: ' + name)
    api = runpy.run_path(str(ROOT / 'tools/release.py'), run_name='owned_uniform_seal_helpers')
    h = type('Helpers', (), {k: staticmethod(v) if callable(v) else v for k, v in api.items()})
    h.digest(a.tools_review_pin)
    for p in (OUT, MANIFEST, ZIP, REPEAT): h.new_output(str(p))
    h.check_inputs(); h.flatten(True, PINS)
    need(sha(h.read(ROOT / 'article.pdf')) == PDF and sha(h.read(ROOT / 'article.tex')) == TEX, 'Accepted article differs')
    need(sha(h.read(ROOT / 'tools/BUILD_DEPENDENCIES_LOCK.json')) == LOCK, 'Accepted dependency lock differs')
    need(sha(h.read(ROOT / 'qa/tool-build-v2/PAGE_INVENTORY.json')) == PAGES, 'Accepted page inventory differs')
    acceptance = h.parse(h.read(ROOT / 'qa/REVIEW_ACCEPTANCE.json'))
    expected = {'status': 'ACCEPTED', 'pdf_sha256': PDF, 'tex_sha256': TEX,
                'manuscript_review_manifest_sha256': MANUSCRIPT_REVIEW, 'tools_review_manifest_sha256': a.tools_review_pin}
    need(all(acceptance.get(k) == v for k, v in expected.items()), 'Final owner review acceptance missing/stale')
    visual = h.parse(h.read(ROOT / 'qa/OWNER_VISUAL_REVIEW.json'))
    need(visual['status'] == 'PASS' and visual['pdf_sha256'] == PDF and visual['tex_sha256'] == TEX and visual['pages_visually_inspected'] == list(range(1, 13)), 'Final all-page owner visual acceptance missing/stale')
    root_review = h.parse(h.read(ROOT / 'qa/ROOT_MANUSCRIPT_AND_VISUAL_ACCEPTANCE.json'))
    need(root_review['status'] == 'ACCEPTED' and root_review['pdf_sha256'] == PDF and root_review['tex_sha256'] == TEX and root_review['page_inventory_sha256'] == PAGES and root_review['pages_individually_inspected'] == list(range(1, 13)), 'Final root manuscript/visual acceptance missing/stale')

    def review(folder, manifest_name, pin):
        raw = h.read(folder / manifest_name); need(sha(raw) == pin, 'Review manifest digest differs')
        actual = h.inventory(folder); del actual['files'][manifest_name]
        if manifest_name.endswith('.json'):
            m = h.parse(raw)
            need(actual == {k: m[k] for k in ('files', 'directories')}, 'Review payload/metadata mismatch')
        else:
            records = {}
            for line in raw.decode().splitlines():
                match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line); need(match is not None, 'Malformed review manifest')
                digest, name = match.groups()
                if name.startswith('./'): name = name[2:]
                h.relative_name(name); need(name not in records, 'Duplicate review name')
                records[name] = digest
            need(set(actual['files']) == set(records), 'Review file set differs')
            need(all(actual['files'][name]['sha256'] == pin for name, pin in records.items()), 'Review file bytes differ')
    review(ROOT / EXEMPT[1], 'MANIFEST.sha256', MANUSCRIPT_REVIEW)
    review(ROOT / EXEMPT[2], a.tools_review_manifest_name, a.tools_review_pin)
    preserved = {name: h.snapshot(ROOT / name) for name in EXEMPT}
    OUT.mkdir(mode=0o700)
    put(OUT / 'PRESERVED_SUBTREES_BEFORE.json', preserved)
    put(OUT / 'OWNED_CONTENT_BEFORE_FREEZE.json', h.snapshot())

    def command(label, tool, args, root=ROOT):
        result = subprocess.run([sys.executable, '-I', '-S', '-B', str(root / 'tools' / tool), *args], stdin=subprocess.DEVNULL,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, cwd=OUT, timeout=600)
        (OUT / (label + '.stdout')).write_bytes(result.stdout)
        need(result.returncode == 0, 'Command failed ' + label + ': ' + result.stdout.decode(errors='replace')[-4000:])
        receipt = h.parse(result.stdout); put(OUT / (label + '.json'), receipt)
        return receipt

    before = command('ORIGINALS_BEFORE_SEAL', 'freeze_inputs.py', ['verify-originals'])
    def exempt(path):
        rel = path.relative_to(ROOT).as_posix()
        return any(rel == name or rel.startswith(name + '/') for name in EXEMPT)
    owned = [p for p in ROOT.rglob('*') if not exempt(p)]
    for p in sorted(owned, key=lambda p: (-len(p.parts), str(p))):
        s = p.lstat(); need(stat.S_ISREG(s.st_mode) or stat.S_ISDIR(s.st_mode), 'Unsafe owned entry')
        p.chmod(0o555 if stat.S_ISDIR(s.st_mode) else 0o444)
    need({name: h.snapshot(ROOT / name) for name in EXEMPT} == preserved, 'Frozen inputs/review metadata changed')
    generated = command('MANIFEST_GENERATION', 'release.py', ['manifest', '--output', str(MANIFEST)])
    pin = generated['manifest_sha256']
    shutil.copy2(MANIFEST, ROOT / 'RELEASE_MANIFEST.json')
    (ROOT / 'RELEASE_MANIFEST.json').chmod(0o444); ROOT.chmod(0o555)
    command('SEALED_VERIFY', 'release.py', ['verify', '--manifest-sha256', pin])
    first = command('ARCHIVE', 'release.py', ['archive', '--manifest-sha256', pin, '--output', str(ZIP)])
    second = command('ARCHIVE_REPEAT', 'release.py', ['archive', '--manifest-sha256', pin, '--output', str(REPEAT)])
    need(h.read(ZIP) == h.read(REPEAT), 'Repeated archive bytes differ')
    extracted = OUT / 'extracted'
    command('EXTRACTION', 'release.py', ['extract', '--manifest-sha256', pin, '--archive', str(ZIP), '--output-dir', str(extracted)])
    command('EXTRACTED_VERIFY', 'release.py', ['verify', '--manifest-sha256', pin], root=extracted)
    replay = OUT / 'replay'
    build = command('EXTRACTED_LOCKED_REPLAY', 'build_article.py', ['--pins-sha', PINS, '--dependency-lock-sha', LOCK,
                    '--require-packaged-match', '--output-dir', str(replay)], root=extracted)
    expected = ROOT / 'qa/tool-build-v2'
    need(h.read(replay / 'article.pdf') == h.read(ROOT / 'article.pdf'), 'Relocated PDF mismatch')
    need(h.read(replay / 'PAGE_INVENTORY.json') == h.read(expected / 'PAGE_INVENTORY.json'), 'Relocated page inventory mismatch')
    names = sorted(p.name for p in (expected / 'pages').iterdir()); need(len(names) == 12, 'Expected twelve pages')
    for name in names: need(h.read(replay / 'pages' / name) == h.read(expected / 'pages' / name), 'Relocated raster differs: ' + name)
    command('POST_REPLAY_SEALED_VERIFY', 'release.py', ['verify', '--manifest-sha256', pin])
    command('POST_REPLAY_EXTRACTED_VERIFY', 'release.py', ['verify', '--manifest-sha256', pin], root=extracted)
    after = command('ORIGINALS_AFTER_SEAL', 'freeze_inputs.py', ['verify-originals'])
    final_preserved = {name: h.snapshot(ROOT / name) for name in EXEMPT}
    need(final_preserved == preserved, 'Protected subtree changed during final gate')
    put(OUT / 'PRESERVED_SUBTREES_AFTER.json', final_preserved)
    for p in (MANIFEST, ZIP, REPEAT): p.chmod(0o444)
    receipt = {'status': 'PASS', 'scope': 'Owned final seal, deterministic archives, metadata-restoring extraction and presentation-only locked replay; independent post-seal terminal gate remains separate',
               'release_root': str(ROOT), 'article_tex_sha256': TEX, 'article_pdf_sha256': PDF, 'article_pdf_bytes': len(h.read(ROOT / 'article.pdf')),
               'manifest_path': str(MANIFEST), 'manifest_sha256': pin, 'manifest_files': generated['files'],
               'archive_path': str(ZIP), 'archive_sha256': first['zip_sha256'], 'archive_bytes': first['bytes'],
               'repeat_archive_path': str(REPEAT), 'repeat_archive_sha256': second['zip_sha256'], 'repeated_archives_identical': True,
               'extracted_root': str(extracted), 'locked_replay_root': str(replay), 'manuscript_pins_sha256': PINS, 'dependency_lock_sha256': LOCK,
               'all_12_raster_bytes_identical': True, 'packaged_pdf_equal_after_relocation': build['packaged_pdf_match'],
               'frozen_inputs_and_copied_review_metadata_preserved': True, 'scoped_original_entries': before['scoped_original_entries'],
               'scoped_original_fresh_interval_equal': after['fresh_interval_equal'], 'historical_audit_scope': 333, 'historical_source_scope': 51,
               'owned_content_read_only': True, 'permission_change_exempt_subtrees': list(EXEMPT), 'source_scientific_code_executed': False,
               'manuscript_review_manifest_sha256': MANUSCRIPT_REVIEW, 'tools_review_manifest_sha256': a.tools_review_pin,
               'coordinator_sha256': sha(Path(__file__).read_bytes()), 'post_seal_receipts_external': True}
    put(OUT / 'FINAL_SEAL_RECEIPT.json', receipt)
    detached = {'manifest_sha256': pin, 'zip_sha256': first['zip_sha256'], 'receipt_path': str(OUT / 'FINAL_SEAL_RECEIPT.json'),
                'receipt_sha256': sha((OUT / 'FINAL_SEAL_RECEIPT.json').read_bytes()), 'article_pdf_sha256': PDF, 'article_tex_sha256': TEX}
    put(OUT / 'DETACHED_PINS.json', detached)
    print(json.dumps(detached, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
