"""Build a standalone TeX source and its PDF, without shell escape.

The optional TeX-cache bootstrap is adapted from the attributed
generated-assumptions build helper. It uses installed TeX files only.
"""
from pathlib import Path
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = 'ipra_flat_computation'


def environment(work):
    env = dict(os.environ)
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], env=env,
                           capture_output=True, text=True)
    if probe.returncode == 0 and probe.stdout.strip():
        return env
    trees = [Path('/usr/share/texmf'), Path('/usr/share/texlive/texmf-dist')]
    if not all(p.is_dir() for p in trees):
        raise SystemExit('Install a PDFLaTeX distribution before rebuilding.')
    cache = work / 'texcache'
    cache.mkdir(exist_ok=True)
    env['TEXMF'] = '{' + ','.join(map(str, [cache, *trees])) + '}'
    target = cache / 'web2c/pdftex/pdflatex.fmt'
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        run = subprocess.run(['pdftex', '-ini', '-etex', '-no-shell-escape',
            '-interaction=nonstopmode', '-halt-on-error', '-jobname=pdflatex',
            '-progname=pdflatex', 'pdflatex.ini'], cwd=cache, env=env,
            capture_output=True, text=True)
        if run.returncode:
            raise SystemExit(run.stdout[-6000:] + run.stderr)
        shutil.move(cache / 'pdflatex.fmt', target)
    maps = [trees[0] / 'fonts/map/dvips/lm/lm.map']
    maps.extend(sorted((trees[1] / 'fonts/map/dvips/amsfonts').glob('*.map')))
    fontmap = cache / 'fonts/map/pdftex/local/pdftex.map'
    fontmap.parent.mkdir(parents=True, exist_ok=True)
    fontmap.write_text('\n'.join(p.read_text() for p in maps))
    return env


def flatten(text):
    text = re.sub(r'\\input\{([^}]+)\}',
                  lambda m: flatten((ROOT / m.group(1)).read_text()), text)
    def listing(match):
        options = match.group(1) or ''
        return ('\\begin{lstlisting}' + options + '\n'
                + (ROOT / match.group(2)).read_text() + '\\end{lstlisting}')
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}', listing, text)


def main():
    standalone = ROOT / (STEM + '.tex')
    standalone.write_text(flatten((ROOT / 'report.tex').read_text()))
    work = ROOT / '.build'
    work.mkdir(exist_ok=True)
    env = environment(work)
    command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
               '-halt-on-error', '-file-line-error', '-output-directory',
               str(work), str(standalone)]
    for pass_number in range(1, 4):
        result = subprocess.run(command, cwd=ROOT, env=env,
                                capture_output=True, text=True)
        (work / f'pass{pass_number}.txt').write_text(result.stdout + result.stderr)
        if result.returncode:
            raise SystemExit((result.stdout + result.stderr)[-9000:])
    shutil.copyfile(work / (STEM + '.pdf'), ROOT / (STEM + '.pdf'))
    log = (work / (STEM + '.log')).read_text(errors='replace')
    warnings = [line for line in log.splitlines() if any(word in line for word in
                ['Overfull', 'undefined', 'Rerun to get', 'multiply defined'])]
    record = {'engine': 'PDFLaTeX', 'passes': 3, 'shell_escape': False,
              'standalone_source': standalone.name, 'pdf': STEM + '.pdf',
              'warnings': warnings}
    (ROOT / 'evidence/build.json').write_text(json.dumps(record, indent=2) + '\n')
    (ROOT / 'evidence/latex_build.log').write_text(log)
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
