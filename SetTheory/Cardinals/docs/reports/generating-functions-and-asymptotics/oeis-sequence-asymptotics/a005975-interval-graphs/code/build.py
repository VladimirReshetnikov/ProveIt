#!/usr/bin/env python3
"""Two clean, three-pass pdflatex builds; a NEW directory outside the bundle."""
import sys
sys.dont_write_bytecode = True
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from output_guard import external_output, create_external_directory

ROOT = Path(__file__).resolve().parent
SOURCE_EPOCH = '1790899200'  # 2026-10-02 00:00:00 UTC

def require(condition, message):
    if not condition:
        raise RuntimeError(message)

def run(command, directory, env, timeout=180):
    result = subprocess.run(command, cwd=directory, env=env,
                            capture_output=True, timeout=timeout)
    require(result.returncode == 0, 'TEX_COMMAND_FAILED: ' + command[0] + '\n' +
            (result.stdout + result.stderr).decode(errors='replace')[-12000:])
    return result.stdout + result.stderr

def build_once(directory, source):
    directory.mkdir()
    (directory / 'report133.tex').write_bytes(source)
    env = os.environ.copy()
    for key in ('TEXINPUTS', 'TEXFORMATS', 'TEXMFCNF', 'TEXMFOUTPUT'):
        env.pop(key, None)
    env.update(SOURCE_DATE_EPOCH=SOURCE_EPOCH, FORCE_SOURCE_DATE='1',
               TZ='UTC', LC_ALL='C', openout_any='p', shell_escape='f')
    # This Debian layout needs an explicit distribution tree in minimal images.
    if Path('/usr/share/texlive/texmf-dist').is_dir():
        env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    env['TEXMFVAR'] = str(directory / 'texmf-var')
    env['TEXMFCONFIG'] = str(directory / 'texmf-config')
    env['TEXFORMATS'] = str(directory) + '//:'
    run(['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
         '-halt-on-error', '-jobname=pdflatex', 'pdflatex.ini'], directory, env)
    # Stabilize PDF metadata independently of the host clock and temporary path.
    source_command = (r'\pdfinfoomitdate=1\pdftrailerid{}\pdfsuppressptexinfo=15'
                      r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}'
                      r'\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}'
                      r'\input{report133.tex}')
    command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
               '-halt-on-error', '-file-line-error', '-jobname=report133', source_command]
    for number in (1, 2, 3):
        run(command, directory, env)
    log = (directory / 'report133.log').read_text(errors='replace')
    forbidden = (r'Overfull \\[hv]box|undefined references|undefined citations|'
                 r'LaTeX Warning: (?:Reference|Citation)|Label\(s\) may have changed|'
                 r'Rerun to get|rerunfilecheck Warning')
    problems = [line for line in log.splitlines() if re.search(forbidden, line)]
    require(not problems, 'TEX_QUALITY_GATE_FAILED:\n' + '\n'.join(problems))
    pdf = (directory / 'report133.pdf').read_bytes()
    require(pdf.startswith(b'%PDF-'), 'TEX_OUTPUT_NOT_PDF')
    return pdf

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path, help='NEW external output DIRECTORY')
    parser.add_argument('--author-unsealed', action='store_true',
                        help='bootstrap only: MANIFEST absent; PDF may be absent')
    args = parser.parse_args()
    try:
        destination = external_output(args.output, ROOT)  # Before reads, checks or temp/output writes.
        from verify import inventory, verify, run_math, check_inventory
        if args.author_unsealed:
            before = inventory(ROOT, author_unsealed=True)
            run_math(ROOT)
        else:
            verify(ROOT)
            before = check_inventory(ROOT)
        require(shutil.which('pdftex') is not None and shutil.which('pdflatex') is not None,
                'PDFTEX_OR_PDFLATEX_NOT_FOUND')
        create_external_directory(destination, ROOT)
        with tempfile.TemporaryDirectory(prefix='clean-', dir=destination) as temporary:
            work = Path(temporary)
            first = build_once(work / 'a', before['report133.tex'])
            second = build_once(work / 'b', before['report133.tex'])
        require(first == second, 'CLEAN_PDF_BUILDS_DIFFER')
        if not args.author_unsealed:
            require(first == before['report133.pdf'], 'SUPPLIED_PDF_BYTES_DIFFER_TOOLCHAIN_OR_SOURCE')
            require(check_inventory(ROOT) == before, 'BUNDLE_CHANGED_DURING_BUILD')
        else:
            require(inventory(ROOT, author_unsealed=True) == before, 'BUNDLE_CHANGED_DURING_BUILD')
        with (destination / 'report133.pdf').open('xb') as stream:
            stream.write(first)
        result = {'status': 'PASS', 'clean_builds': 2, 'pdflatex_passes_per_build': 3,
                  'author_unsealed': args.author_unsealed,
                  'supplied_pdf_bytes_match': not args.author_unsealed,
                  'pdf_sha256': sha256(first).hexdigest()}
        data = (json.dumps(result, indent=2, sort_keys=True) + '\n').encode()
        with (destination / 'build-results.json').open('xb') as stream:
            stream.write(data)
        sys.stdout.buffer.write(data)
    except (ValueError, RuntimeError, OSError, subprocess.SubprocessError) as exc:
        print('BUILD_FAIL: ' + str(exc), file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
