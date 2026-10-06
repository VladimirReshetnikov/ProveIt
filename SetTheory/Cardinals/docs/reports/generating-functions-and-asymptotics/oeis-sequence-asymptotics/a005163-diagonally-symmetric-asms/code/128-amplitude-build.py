#!/usr/bin/env python3
"""Build both reader articles in clean directories, twice, without networking.
The main PDF is an author-side output; the unchanged earlier PDF must match.
Run replay.py to perform the complete build in an immutable clean copy.
"""
import sys
sys.dont_write_bytecode = True
from hashlib import sha256
from pathlib import Path
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def run_bounded(command, *, timeout, **kwargs):
    try:
        return subprocess.run(command, timeout=timeout, **kwargs)
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError(f'SUBPROCESS_TIMEOUT after {timeout}s: {command[0]}') from exc


def build_once(destination, source_root=ROOT, stem='report128'):
    destination.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.update(SOURCE_DATE_EPOCH='1790899200', FORCE_SOURCE_DATE='1', TZ='UTC', LC_ALL='C')
    if Path('/usr/share/texlive/texmf-dist').is_dir():
        env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    env['TEXMFVAR'] = str(destination/'texmf-var')
    env['TEXMFCONFIG'] = str(destination/'texmf-config')
    env['TEXFORMATS'] = str(destination)+'//:'
    fmt = ['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
           '-halt-on-error', '-jobname=pdflatex', 'pdflatex.ini']
    cp = run_bounded(fmt, timeout=120, cwd=destination, env=env, capture_output=True)
    (destination/'format.stdout').write_bytes(cp.stdout+cp.stderr)
    require(cp.returncode == 0, 'TeX format generation failed: '+(cp.stdout+cp.stderr).decode(errors='replace')[-8000:])
    source = (r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}'
              r'\pdfmapfile{+lm.map}\input{' + stem + '.tex}')
    command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error',
               '-file-line-error', f'-output-directory={destination}', source]
    for number in range(1, 4):
        cp = run_bounded(command, timeout=180, cwd=source_root, env=env, capture_output=True)
        (destination/f'pass{number}.stdout').write_bytes(cp.stdout+cp.stderr)
        require(cp.returncode == 0, f'PDF build pass {number} failed: '+(cp.stdout+cp.stderr).decode(errors='replace')[-8000:])
    log = (destination/(stem+'.log')).read_text(errors='replace')
    forbidden = (r'Overfull \\[hv]box|undefined references|undefined citations|'
                 r'LaTeX Warning: (?:Reference|Citation)|Label\(s\) may have changed|Missing character:')
    matches = re.findall(forbidden, log)
    require(not matches, f'TeX quality gate failed: {matches}\n'+
            '\n'.join(line for line in log.splitlines() if re.search(forbidden, line)))
    return (destination/(stem+'.pdf')).read_bytes()


def main():
    receipts = []
    for source_root, stem, preserved in ((ROOT, 'report128', False),
                                         (ROOT/'earlier_input', 'report124', True)):
        with tempfile.TemporaryDirectory(prefix=stem+'-build-a-') as tmp:
            first = build_once(Path(tmp), source_root, stem)
        with tempfile.TemporaryDirectory(prefix=stem+'-build-b-') as tmp:
            second = build_once(Path(tmp), source_root, stem)
        require(first == second, stem+': PDF is not byte-identical across clean builds')
        target = source_root/(stem+'.pdf')
        if preserved:
            require(target.read_bytes() == first, 'EARLIER_INPUT_PDF_CHANGED')
        else:
            target.write_bytes(first)
        receipts.append(stem+' '+sha256(first).hexdigest())
    print('PASS: two clean builds per article; unchanged earlier input verified\n'+'\n'.join(receipts))


if __name__ == '__main__':
    main()
