"""Build the report and expand an independently compilable LaTeX source."""
from pathlib import Path
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
INPUT = re.compile(r'\\input\{([^}]+)\}')
LISTING = re.compile(r'\\lstinputlisting(?:\[([^\]]*)\])?\{([^}]+)\}')


def environment(work):
    """Use installed TeX sources if the distribution lacks a prebuilt format.

    Fallback adapted from the pinned unparenthesized three-schema archive's
    build.py, which attributes its predecessor in the feedback archive.
    """
    env = dict(os.environ)
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], env=env,
                           capture_output=True, text=True)
    if probe.returncode == 0 and probe.stdout.strip():
        return env
    trees = [Path('/usr/share/texmf'), Path('/usr/share/texlive/texmf-dist')]
    if not all(path.is_dir() for path in trees):
        raise SystemExit('An installed PDFLaTeX format or TeX source tree is required.')
    cache = work / 'texcache'
    cache.mkdir(exist_ok=True)
    env['TEXMF'] = '{' + ','.join(map(str, [cache, *trees])) + '}'
    target = cache / 'web2c/pdftex/pdflatex.fmt'
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        run = subprocess.run(['pdftex', '-ini', '-etex', '-no-shell-escape',
                              '-interaction=nonstopmode', '-halt-on-error',
                              '-jobname=pdflatex', '-progname=pdflatex', 'pdflatex.ini'],
                             cwd=cache, env=env, capture_output=True, text=True)
        if run.returncode:
            raise SystemExit(run.stdout[-9000:] + run.stderr)
        shutil.move(cache / 'pdflatex.fmt', target)
    maps = [trees[0] / 'fonts/map/dvips/lm/lm.map']
    maps.extend(sorted((trees[1] / 'fonts/map/dvips/amsfonts').glob('*.map')))
    fontmap = cache / 'fonts/map/pdftex/local/pdftex.map'
    fontmap.parent.mkdir(parents=True, exist_ok=True)
    fontmap.write_text('\n'.join(path.read_text() for path in maps))
    return env


def expand(path, stack=()):
    path = path.resolve()
    if path in stack:
        raise ValueError('Recursive TeX input')
    text = path.read_text()
    def sub(match):
        child = ROOT / match.group(1)
        if not child.suffix:
            child = child.with_suffix('.tex')
        return expand(child, stack + (path,))
    text = INPUT.sub(sub, text)
    def listing(match):
        options = '[' + match.group(1) + ']' if match.group(1) else ''
        body = (ROOT / match.group(2)).read_text()
        return '\\begin{lstlisting}' + options + '\n' + body + '\\end{lstlisting}'
    return LISTING.sub(listing, text)


def main():
    executable = shutil.which('pdflatex')
    if not executable:
        raise SystemExit('PDFLaTeX is required; the compiled report is already included.')
    target = ROOT / 'ipra_named_specialization.tex'
    target.write_text(expand(ROOT / 'report.tex'))
    build = ROOT / '.build'
    build.mkdir(exist_ok=True)
    env = environment(build)
    for turn in range(3):
        command = [executable, '-no-shell-escape', '-interaction=nonstopmode',
                   '-halt-on-error', '-file-line-error', '-output-directory=' + str(build),
                   'report.tex']
        run = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True)
        (build / ('pass_' + str(turn + 1) + '.txt')).write_text(run.stdout + run.stderr)
        if run.returncode:
            raise SystemExit(run.stdout[-9000:] + run.stderr)
    shutil.copy2(build / 'report.pdf', ROOT / 'report.pdf')
    log = (build / 'report.log').read_text(errors='replace')
    warnings = [line for line in log.splitlines()
                if 'Warning' in line or 'Overfull' in line or 'Underfull' in line]
    (ROOT / 'evidence/build.json').write_text(json.dumps({
        'pdf': 'report.pdf', 'standalone_tex': target.name,
        'latex_passes': 3, 'shell_escape': False, 'warnings': warnings,
        'scope': 'Compilation receipt; visual review is recorded separately.'}, indent=2) + '\n')
    print(json.dumps({'pdf_bytes': (ROOT / 'report.pdf').stat().st_size,
                      'standalone_tex_bytes': target.stat().st_size,
                      'warnings': warnings}, indent=2))


if __name__ == '__main__':
    main()
