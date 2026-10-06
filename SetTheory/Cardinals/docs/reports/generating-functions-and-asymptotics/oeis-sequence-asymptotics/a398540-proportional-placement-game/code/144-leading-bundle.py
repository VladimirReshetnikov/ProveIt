#!/usr/bin/env python3
"""Verify, rebuild, and deterministically pack Report144. Run with python3 -I."""
import sys
if not sys.flags.isolated:
    raise SystemExit('Use python3 -I bundle.py; isolated startup is required.')
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parent
EPOCH = '1790985600'
MEMBERS = ('README.md', 'Report144.pdf', 'Report144.tex', 'SOURCES.md',
           'bundle.py', 'companion/README.md', 'companion/PROVENANCE.md', 'companion/SCHEMA.md',
           'companion/fixtures/rate_certificate.json',
           'companion/verify_certificate.py', 'companion/test_verifier.py')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def unique(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_path(path):
    require('..' not in Path(path).parts, 'Parent traversal in path')
    path = Path(os.path.abspath(path))
    for part in (path, *path.parents):
        require(not part.is_symlink(), 'Symlink in path: ' + str(part))
    return path


def verify_manifest():
    manifest_path = safe_path(ROOT / 'manifest.json')
    manifest = json.loads(manifest_path.read_text(encoding='utf-8'), object_pairs_hook=unique)
    require(type(manifest) is dict and set(manifest) == {'schema', 'files'}, 'Manifest schema keys differ')
    require(type(manifest['schema']) is int and manifest['schema'] == 1, 'Manifest schema must be integer 1')
    files = manifest['files']
    require(type(files) is dict and set(files) == set(MEMBERS), 'Manifest membership differs')
    for name in MEMBERS:
        path = safe_path(ROOT / name)
        require(path.is_file(), 'Missing package member: ' + name)
        claimed = files[name]
        require(type(claimed) is str and len(claimed) == 64 and all(c in '0123456789abcdef' for c in claimed), 'Malformed digest')
        require(digest(path) == claimed, 'Digest mismatch: ' + name)
    return manifest


def new_output(value):
    output = safe_path(value)
    require(output != ROOT and output not in ROOT.parents and ROOT not in output.parents,
            'Output must lie outside source package and its ancestors')
    require(not output.exists(), 'Output directory must be new')
    require(output.parent.is_dir(), 'Output parent must already exist')
    output.mkdir(mode=0o700)
    return output


def build_pdf(value):
    verify_manifest()
    output = new_output(value)
    shutil.copyfile(ROOT / 'Report144.tex', output / 'Report144.tex')
    env = {'PATH': os.defpath, 'SOURCE_DATE_EPOCH': EPOCH, 'FORCE_SOURCE_DATE': '1',
           'TZ': 'UTC', 'LC_ALL': 'C'}
    for key, folder in [('HOME', 'home'), ('TEXMFHOME', 'texmf-home'),
                        ('TEXMFVAR', 'texmf-var'), ('TEXMFCONFIG', 'texmf-config'),
                        ('TEXMFCACHE', 'texmf-cache'), ('XDG_CACHE_HOME', 'xdg-cache')]:
        directory = output / folder
        directory.mkdir()
        env[key] = str(directory)
    # The two standard Debian TeX Live trees used for the supplied PDF.
    # No inherited TEXINPUTS, TEXFORMATS, HOME, or cache setting is used.
    env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    env['TEXFORMATS'] = str(output) + '//:'
    pdftex = shutil.which('pdftex', path=os.defpath)
    pdflatex = shutil.which('pdflatex', path=os.defpath)
    require(pdftex is not None and pdflatex is not None, 'pdfTeX and pdfLaTeX are required')
    fmt = [pdftex, '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
           '-halt-on-error', '-jobname=pdflatex', 'pdflatex.ini']
    texinput = (r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}'
                r'\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report144.tex}')
    command = [pdflatex, '-no-shell-escape', '-interaction=nonstopmode',
               '-halt-on-error', '-file-line-error', texinput]
    with (output / 'build-console.txt').open('x', encoding='utf-8') as console:
        subprocess.run(fmt, cwd=output, env=env, stdout=console, stderr=subprocess.STDOUT, check=True)
        for unused in range(2):
            subprocess.run(command, cwd=output, env=env, stdout=console, stderr=subprocess.STDOUT, check=True)
    pdf = output / 'Report144.pdf'
    result = {'schema': 1, 'pdf_sha256': digest(pdf),
              'matches_supplied_pdf': pdf.read_bytes() == (ROOT / 'Report144.pdf').read_bytes()}
    (output / 'build-result.json').write_text(json.dumps(result, sort_keys=True, indent=2) + '\n', encoding='utf-8')
    return result


def pack(value):
    verify_manifest()
    output = new_output(value)
    path = output / 'Report144.zip'
    with zipfile.ZipFile(path, 'x', compression=zipfile.ZIP_STORED) as archive:
        for name in sorted((*MEMBERS, 'manifest.json')):
            source = safe_path(ROOT / name)
            entry = zipfile.ZipInfo('Report144/' + name, date_time=(2026, 10, 3, 0, 0, 0))
            entry.compress_type = zipfile.ZIP_STORED
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            archive.writestr(entry, source.read_bytes())
    return {'schema': 1, 'archive_sha256': digest(path), 'members': len(MEMBERS) + 1}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action', choices=['verify', 'build-pdf', 'pack'])
    parser.add_argument('--output-dir')
    args = parser.parse_args()
    require((args.action == 'verify') == (args.output_dir is None), 'Only build-pdf and pack require --output-dir')
    if args.action == 'verify':
        verify_manifest()
        result = {'schema': 1, 'manifest_verified': True, 'members': len(MEMBERS)}
    elif args.action == 'build-pdf':
        result = build_pdf(args.output_dir)
    else:
        result = pack(args.output_dir)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
