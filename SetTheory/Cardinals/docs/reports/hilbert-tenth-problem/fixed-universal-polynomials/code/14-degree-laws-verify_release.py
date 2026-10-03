#!/usr/bin/env python3
"""Check the exact Report 24 release and run its bundled data-only verification."""
import sys
sys.dontwritebytecode = True
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
SEALS = {'RELEASE_INVENTORY.json', 'RELEASE_INVENTORY.sha256'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1048576), b''):
            h.update(data)
    return h.hexdigest()


def snapshot(root):
    need(root.is_dir() and not root.is_symlink(), 'Missing or symlinked release')
    files, directories = {}, []
    for path in sorted(root.rglob('*')):
        name = path.relative_to(root).as_posix()
        need(not path.is_symlink(), 'Symlinked release entry: ' + name)
        if path.is_dir():
            directories.append(name)
        else:
            need(path.is_file(), 'Nonregular release entry: ' + name)
            files[name] = {'bytes': path.stat().st_size, 'sha256': digest(path)}
    return {'files': files, 'directories': directories}


def integrity(root=ROOT):
    current = snapshot(root)
    for name in SEALS:
        need(name in current['files'], 'Missing release seal: ' + name)
    anchor = (root / 'RELEASE_INVENTORY.sha256').read_text('ascii')
    need(re.fullmatch('[0-9a-f]{64}\\n', anchor) is not None, 'Malformed release seal')
    need(digest(root / 'RELEASE_INVENTORY.json') == anchor.strip(), 'Release seal mismatch')
    inv = json.loads((root / 'RELEASE_INVENTORY.json').read_text('utf-8'))
    files = {k: v for k, v in current['files'].items() if k not in SEALS}
    need(inv == {'files': files, 'directories': current['directories']}, 'Exact release inventory mismatch')
    review = (root / 'qa/MATH_REVIEW.md').read_text('utf-8')
    tex_hash = digest(root / 'article/report24.tex')
    need(tex_hash in review, 'Mathematical review does not match the article source')
    render = json.loads((root / 'qa/RENDER_QA.json').read_text('utf-8'))
    need(render['status'] == 'PASS' and render['all_pages_inspected'] is True,
         'Missing passing all-page render review')
    need(render['pdf_sha256'] == digest(root / 'article/report24.pdf') and
         render['tex_sha256'] == tex_hash, 'Render review does not match article files')
    need((root / 'article/report24.pdf').read_bytes().startswith(b'%PDF-'), 'Malformed PDF header')
    return {'status': 'PASS', 'files': len(current['files']), 'directories': len(current['directories']),
            'inventory_sha256': anchor.strip(), 'article_pages': render['page_count']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--integrity-only', action='store_true')
    parser.add_argument('--universal', action='store_true')
    parser.add_argument('--source-dir', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    need(args.universal == (args.source_dir is not None),
         '--universal and an explicit --source-dir are required together')
    need(not (args.integrity_only and args.universal), 'Conflicting replay modes')
    if args.output:
        dest = args.output.resolve()
        need(dest != ROOT and ROOT not in dest.parents, 'Output must be outside the release')
    before = snapshot(ROOT)
    result = {'status': 'PASS', 'integrity': integrity(), 'python_optimized': bool(sys.flags.optimize)}
    if not args.integrity_only:
        with tempfile.TemporaryDirectory(prefix='report24-replay-') as work:
            cert = Path(work) / 'receipt.json'
            command = [sys.executable, '-B'] + (['-O'] if sys.flags.optimize else [])
            command += [str(ROOT / 'reproducibility/verify.py'), '--output', str(cert)]
            if args.universal:
                command += ['--universal', '--source-dir', str(args.source_dir.resolve())]
            done = subprocess.run(command, cwd=work, capture_output=True, text=True,
                                  env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
            need(done.returncode == 0, 'Bundled replay failed with exit ' + str(done.returncode))
            result['replay'] = json.loads(cert.read_text('utf-8'))
            need(result['replay']['status'] == 'PASS', 'Bundled replay did not pass')
    need(snapshot(ROOT) == before, 'Release changed during verification')
    result['exact_inventory_unchanged'] = True
    text = json.dumps(result, indent=2, sort_keys=True) + '\n'
    if args.output:
        args.output.write_text(text, encoding='utf-8')
    print(text, end='')


if __name__ == '__main__':
    main()
