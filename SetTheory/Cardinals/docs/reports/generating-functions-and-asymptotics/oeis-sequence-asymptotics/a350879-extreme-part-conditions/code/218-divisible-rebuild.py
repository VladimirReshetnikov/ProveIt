#!/usr/bin/env python3
"""Offline, nondestructive full Report 218 rebuild and deterministic archive."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import zipfile

SOURCE_FILES = ('report218.tex', 'rebuild.py', 'README.md', 'code/reproduce.py', 'code/README.md', 'code/test_reproduce.py', 'code/uniform_certificates.py')
GENERATED_FILES = ('exact_values.csv', 'receipt.json', 'exact_counts.tex',
                   'radial_coefficients.tex', 'forward_coefficients.tex',
                   'finite_enclosure.tex', 'verification_summary.tex')
EPOCH = '1791072000'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args, cwd, env=None):
    result = subprocess.run(args, cwd=cwd, env=env, text=True, capture_output=True)
    require(result.returncode == 0, 'Command failed: '+str(args[0])+'\n'+result.stdout+'\n'+result.stderr)
    return result.stdout.strip()


def verify_manifest(source):
    path = source / 'MANIFEST.json'
    if not path.exists():
        return False
    data = json.loads(path.read_text(encoding='utf-8'))
    require(data.get('report') == 218 and isinstance(data.get('sha256'), dict), 'Invalid source manifest')
    for name, expected in data['sha256'].items():
        rel = Path(name)
        require(not rel.is_absolute() and '..' not in rel.parts, 'Unsafe manifest path')
        file = source / rel
        require(file.is_file() and sha(file) == expected, 'Source manifest mismatch: '+name)
    return True


def compile_pdf(package, work):
    work.mkdir()
    shutil.copyfile(package / 'report218.tex', work / 'report218.tex')
    shutil.copytree(package / 'generated', work / 'generated')
    env = dict(os.environ, SOURCE_DATE_EPOCH=EPOCH, FORCE_SOURCE_DATE='1', TZ='UTC', LC_ALL='C')
    # Construct a private format/map from the installed TeX tree, without
    # writing to a user's cache or downloading anything.
    dist = Path(command(['kpsewhich', '-var-value=TEXMFDIST'], work))
    require(dist.is_dir(), 'Installed TeX distribution not found')
    trees = [dist]
    sibling = dist.parent.parent / 'texmf'
    if sibling.is_dir():
        trees.append(sibling)
    env['TEXMF'] = '{'+','.join(map(str, trees))+'}'
    env['TEXFORMATS'] = str(work)+os.pathsep
    env['TEXMFVAR'] = str(work / 'texmf-var')
    env['TEXMFCONFIG'] = str(work / 'texmf-config')
    command(['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
             '-halt-on-error', '-jobname=pdflatex', 'pdflatex.ini'], work, env)
    maps = []
    for name in ('cm.map', 'cmextra.map', 'latxfont.map', 'symbols.map', 'lm.map'):
        path = Path(command(['kpsewhich', name], work, env))
        require(path.is_file(), 'Installed font map missing: '+name)
        maps.append(path.read_bytes())
    (work / 'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
    previous = None
    stable = False
    for iteration in range(6):
        log = command(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                       '-halt-on-error', '-file-line-error', 'report218.tex'], work, env)
        (work / ('pass-%d.log' % (iteration + 1))).write_text(log+'\n', encoding='utf-8')
        current = (work / 'report218.pdf').read_bytes()
        if iteration >= 2 and current == previous:
            stable = True
            break
        previous = current
    require(stable, 'PDF failed to reach byte stability within six passes')
    log = (work / 'report218.log').read_text(encoding='utf-8', errors='replace')
    require('Overfull \\hbox' not in log and 'Overfull \\vbox' not in log, 'Overfull box in PDF build')
    require('There were undefined references' not in log and 'undefined on input line' not in log,
            'Unresolved PDF reference')
    (package / 'Report218.pdf').write_bytes(current)
    return iteration + 1


def create_archive(package, output):
    files = sorted(p for p in package.rglob('*') if p.is_file())
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for p in files:
            name = 'Report218/' + p.relative_to(package).as_posix()
            info = zipfile.ZipInfo(name, date_time=(2026, 10, 4, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            info.create_system = 3
            archive.writestr(info, p.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True, help='new or empty output directory')
    parser.add_argument('--skip-pdf', action='store_true', help='exact checks only; do not package an incomplete archive')
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    output = args.out.resolve()
    require(output != source and output not in source.parents, 'Output cannot replace the source or an ancestor')
    require(not output.exists() or (output.is_dir() and not any(output.iterdir())),
            'Output must be new or empty; existing contents are never overwritten')
    checked = verify_manifest(source)
    for name in SOURCE_FILES:
        require((source / name).is_file(), 'Missing source: '+name)
    output.mkdir(parents=True, exist_ok=True)
    package = output / 'Report218'
    package.mkdir()
    for name in SOURCE_FILES:
        target = package / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source / name, target)
    # Preserve optimized execution in child arithmetic checks.
    python = [sys.executable] + (['-O'] if sys.flags.optimize else []) + ['-B']
    command(python + [str(package / 'code/test_reproduce.py')], output)
    command(python + [str(package / 'code/reproduce.py'), '--output', str(package / 'generated'), '--N', '1000'], output)
    checks = {}
    for name in GENERATED_FILES:
        current = package / 'generated' / name
        require(current.is_file(), 'Missing regenerated output: '+name)
        old = source / 'generated' / name
        if old.exists():
            require(current.read_bytes() == old.read_bytes(), 'Regenerated output differs: '+name)
            checks['generated/'+name] = 'byte-identical'
        else:
            checks['generated/'+name] = 'regenerated'
    passes = None
    if not args.skip_pdf:
        passes = compile_pdf(package, output / 'tex-work')
        old_pdf = source / 'Report218.pdf'
        checks['Report218.pdf'] = ('byte-identical' if old_pdf.exists() and
            old_pdf.read_bytes() == (package / 'Report218.pdf').read_bytes()
            else 'rebuilt; bytes may vary across TeX versions')
    # A manifest pins every packaged payload except the two manifest files.
    hashes = {p.relative_to(package).as_posix(): sha(p) for p in sorted(package.rglob('*')) if p.is_file()}
    manifest = {'schema': 1, 'report': 218, 'hash_algorithm': 'sha256',
                'manifest_excludes': ['MANIFEST.json', 'SHA256SUMS'], 'sha256': hashes}
    (package / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    checksum_payload = dict(hashes, **{'MANIFEST.json': sha(package / 'MANIFEST.json')})
    (package / 'SHA256SUMS').write_text(''.join(checksum_payload[name]+'  '+name+'\n'
                                             for name in sorted(checksum_payload)), encoding='utf-8')
    archive = output / 'Report218-reproducibility.zip'
    if not args.skip_pdf:
        create_archive(package, archive)
    receipt = {'schema': 1, 'report': 218, 'source_manifest_verified': checked,
               'exact_check_mode': 'optimized' if sys.flags.optimize else 'normal',
               'checks': checks, 'pdf_stable_passes': passes,
               'manifest_sha256': sha(package / 'MANIFEST.json'),
               'zip_sha256': sha(archive) if archive.exists() else None}
    (output / 'REBUILD_RECEIPT.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
