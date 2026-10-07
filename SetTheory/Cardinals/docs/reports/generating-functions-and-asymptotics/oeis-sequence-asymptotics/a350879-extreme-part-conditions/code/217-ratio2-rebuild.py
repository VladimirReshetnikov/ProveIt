#!/usr/bin/env python3
"""Offline, nondestructive Report 217 rebuild into a new directory."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command, cwd, env=None):
    result = subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)
    require(result.returncode == 0, 'Command failed: '+str(command[0])+'\n'+result.stdout+'\n'+result.stderr)
    return result.stdout.strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True, help='new or empty directory')
    parser.add_argument('--numerical', action='store_true', help='also rerun optional mpmath diagnostics')
    parser.add_argument('--skip-pdf', action='store_true', help='exact code checks only; no TeX needed')
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    output = args.out.resolve()
    require(output != source and output not in source.parents, 'Output must not replace the source or any ancestor')
    require(not output.exists() or (output.is_dir() and not any(output.iterdir())), 'Output must be new or empty; existing files are never overwritten')
    manifest_file = source/'MANIFEST.json'
    if manifest_file.exists():
        manifest = json.loads(manifest_file.read_text(encoding='utf-8'))
        for name, expected in manifest['sha256'].items():
            p = Path(name)
            require(not p.is_absolute() and '..' not in p.parts, 'Unsafe manifest path')
            require((source/p).is_file() and sha(source/p) == expected, 'Source manifest mismatch: '+name)
    output.mkdir(parents=True, exist_ok=True)
    exact = output/'generated'
    run([sys.executable, '-B', str(source/'code'/'build.py'), '--out', str(exact), '--order', '4', '--max-n', '10000'], output)
    checks = {}
    for file in sorted(exact.iterdir()):
        expected = source/'generated'/file.name
        require(expected.is_file() and file.read_bytes() == expected.read_bytes(), 'Generated exact artifact mismatch: '+file.name)
        checks['generated/'+file.name] = 'byte-identical'
    if args.numerical:
        diagnostic = exact/'numerical_diagnostics.json'
        run([sys.executable, '-B', str(source/'code'/'numerical.py'), '--max-n', '10000', '--dps', '80', '--radial', '--out', str(diagnostic)], output)
        reference = source/'generated'/'numerical_diagnostics.json'
        require(diagnostic.read_bytes() == reference.read_bytes(), 'Numerical diagnostics differ; check mpmath version and precision')
        checks['generated/numerical_diagnostics.json'] = 'byte-identical'
    if not args.skip_pdf:
        work = output/'tex-work'
        work.mkdir()
        shutil.copyfile(source/'article.tex', work/'article.tex')
        env = dict(os.environ, SOURCE_DATE_EPOCH='1791072000', FORCE_SOURCE_DATE='1', TZ='UTC', LC_ALL='C')
        # Locate the installed TeX tree rather than embedding host paths.
        dist = Path(run(['kpsewhich', '-var-value=TEXMFDIST'], work))
        require(dist.is_dir(), 'Installed TeX distribution not found')
        trees = [dist]
        sibling = dist.parent.parent/'texmf'
        if sibling.is_dir():
            trees.append(sibling)
        env['TEXMF'] = '{'+','.join(map(str, trees))+'}'
        env['TEXFORMATS'] = str(work)+os.pathsep
        env['TEXMFVAR'] = str(work/'texmf-var')
        env['TEXMFCONFIG'] = str(work/'texmf-config')
        # A private format and map make the build independent of user caches.
        run(['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error', '-jobname=pdflatex', 'pdflatex.ini'], work, env)
        maps = []
        for name in ('cm.map', 'cmextra.map', 'latxfont.map', 'symbols.map', 'lm.map'):
            path = Path(run(['kpsewhich', name], work, env))
            require(path.is_file(), 'Installed font map missing: '+name)
            maps.append(path.read_bytes())
        (work/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
        previous = None
        stable = False
        for iteration in range(5):
            run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error', '-file-line-error', 'article.tex'], work, env)
            current = (work/'article.pdf').read_bytes()
            if iteration >= 2 and current == previous:
                stable = True
                break
            previous = current
        require(stable, 'PDF did not reach byte stability in five passes')
        log = (work/'article.log').read_text(encoding='utf-8', errors='replace')
        require('Overfull \\hbox' not in log and 'Overfull \\vbox' not in log, 'Overfull box in PDF build')
        require('There were undefined references' not in log and 'Citation `' not in log, 'Unresolved PDF reference')
        (output/'Report217.pdf').write_bytes(current)
        reference = source/'Report217.pdf'
        checks['Report217.pdf'] = 'byte-identical' if reference.exists() and reference.read_bytes() == current else 'rebuilt (PDF bytes may differ across TeX versions)'
        checks['pdf_internal_stability'] = 'byte-identical consecutive passes'
    receipt = {'schema': 1, 'report': 217, 'offline': True, 'source_manifest_checked': manifest_file.exists(), 'checks': checks,
               'sha256': {str(p.relative_to(output)): sha(p) for p in sorted(output.rglob('*')) if p.is_file() and 'tex-work' not in p.parts}}
    (output/'REBUILD_RECEIPT.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    print('Report 217 rebuilt and checked in '+str(args.out))


if __name__ == '__main__':
    main()
