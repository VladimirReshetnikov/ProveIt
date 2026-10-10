#!/usr/bin/env python3
"""Build the article and optionally package the complete research supplement."""
import argparse
import hashlib
from pathlib import Path
import shutil
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parent.parent
EXCLUDE_SUFFIXES = {'.aux', '.log', '.out', '.toc', '.fls', '.fdb_latexmk', '.pyc'}


def deliverable_files():
    for path in sorted(ROOT.rglob('*')):
        rel = path.relative_to(ROOT)
        if not path.is_file() or any(p in {'build', '__pycache__'} for p in rel.parts):
            continue
        if path.suffix in EXCLUDE_SUFFIXES or path.suffix == '.zip':
            continue
        if any(p.startswith('.') for p in rel.parts):
            continue
        yield path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', action='store_true', help='also create the ZIP beside this folder')
    parser.add_argument('--package-only', action='store_true', help='package an already inspected PDF')
    args = parser.parse_args()
    if not args.package_only:
        if not shutil.which('pdflatex'):
            raise SystemExit('pdfLaTeX was not found. Install a TeX distribution first.')
        build = ROOT / 'build'
        build.mkdir(exist_ok=True)
        for run in range(1, 4):
            result = subprocess.run(
                ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                 '-file-line-error', '-output-directory=build', 'article.tex'],
                cwd=ROOT, capture_output=True, text=True)
            (build / f'pass_{run}.txt').write_text(result.stdout + result.stderr)
            if result.returncode:
                print(result.stdout[-7000:])
                raise SystemExit(f'LaTeX pass {run} failed; see build/pass_{run}.txt')
        log = (build / 'article.log').read_text(errors='replace')
        problems = [needle for needle in (
            'Overfull \\hbox', 'Overfull \\vbox', 'There were undefined references',
            'multiply defined', 'Rerun to get cross-references right') if needle in log]
        if problems:
            raise SystemExit('Build needs inspection: ' + ', '.join(problems))
        shutil.copy2(build / 'article.pdf', ROOT / 'article.pdf')
        print('Built article.pdf with resolved references and no overfull boxes.')
    if args.package or args.package_only:
        if not (ROOT / 'article.pdf').is_file():
            raise SystemExit('Build article.pdf before packaging.')
        paths = [p for p in deliverable_files() if p.name != 'MANIFEST.sha256']
        lines = [hashlib.sha256(p.read_bytes()).hexdigest() + '  ' + p.relative_to(ROOT).as_posix()
                 for p in paths]
        (ROOT / 'MANIFEST.sha256').write_text('\n'.join(lines) + '\n')
        archive = ROOT.parent / (ROOT.name + '.zip')
        with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as zf:
            for path in deliverable_files():
                name = ROOT.name + '/' + path.relative_to(ROOT).as_posix()
                item = zipfile.ZipInfo(name, date_time=(2026, 10, 10, 0, 0, 0))
                item.compress_type = zipfile.ZIP_DEFLATED
                item.external_attr = 0o100644 << 16
                zf.writestr(item, path.read_bytes())
        with zipfile.ZipFile(archive) as zf:
            if zf.testzip() is not None:
                raise SystemExit('ZIP integrity verification failed.')
        print(f'Packaged {archive.name} ({archive.stat().st_size:,} bytes).')


if __name__ == '__main__':
    main()
