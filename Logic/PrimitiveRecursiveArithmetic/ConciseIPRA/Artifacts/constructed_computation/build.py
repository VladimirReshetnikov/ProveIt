"""Build the self-contained TeX source and its PDF; no network is used."""
from pathlib import Path
import hashlib
import json
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
NAME = 'ipra_constructed_computation'


def latex_environment(build):
    """Use normal TeX settings, or bootstrap formats on a stripped Debian install."""
    env = os.environ.copy()
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], capture_output=True, text=True, env=env)
    if probe.returncode == 0 and probe.stdout.strip():
        return env
    distribution = Path('/usr/share/texlive/texmf-dist')
    fonts = Path('/usr/share/texmf')
    ini = distribution / 'tex/latex/tex-ini-files/pdflatex.ini'
    if not ini.is_file():
        return env
    runtime = build / 'tex-runtime'
    runtime.mkdir(exist_ok=True)
    env.update(TEXMFCNF=str(distribution / 'web2c'),
               TEXMF='{' + str(distribution) + ',' + str(fonts) + '}',
               TEXFORMATS=str(runtime), TEXFONTMAPS=str(runtime))
    if not (runtime / 'pdflatex.fmt').is_file():
        result = subprocess.run(['pdftex', '-ini', '-etex', '-interaction=nonstopmode',
                                 '-halt-on-error', '-jobname=pdflatex', '-progname=pdflatex', str(ini)],
                                cwd=runtime, env=env, capture_output=True, text=True)
        (runtime / 'format-build.txt').write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError('Could not prepare the installed LaTeX format; see .build/tex-runtime.')
    maps = [fonts / 'fonts/map/dvips/lm/lm.map']
    maps += [distribution / 'fonts/map/dvips/amsfonts' / name
             for name in ['cm.map', 'symbols.map', 'latxfont.map', 'cmextra.map']]
    (runtime / 'pdftex.map').write_text('\n'.join(path.read_text() for path in maps if path.is_file()))
    return env


def expand(text):
    def include(match):
        path = ROOT / match.group(1)
        if not path.suffix:
            path = path.with_suffix('.tex')
        return '% BEGIN ' + str(path.relative_to(ROOT)) + '\n' + expand(path.read_text()) + '\n% END include\n'
    text = re.sub(r'\\input\{([^}]+)\}', include, text)
    def listing(match):
        options = match.group(1) or ''
        path = ROOT / match.group(2)
        return '\\begin{lstlisting}' + options + '\n' + path.read_text().rstrip() + '\n\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}', listing, text)


def main():
    source = ROOT / (NAME + '.tex')
    source.write_text(expand((ROOT / 'report.tex').read_text()))
    build = ROOT / '.build'
    build.mkdir(exist_ok=True)
    env = latex_environment(build)
    for run in range(3):
        result = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                                 '-file-line-error', '-output-directory=' + str(build), source.name],
                                cwd=ROOT, env=env, capture_output=True, text=True)
        (build / ('pass' + str(run + 1) + '.txt')).write_text(result.stdout + result.stderr)
        if result.returncode:
            print(result.stdout[-6000:])
            raise SystemExit(result.returncode)
    log = (build / (NAME + '.log')).read_text(errors='replace')
    warnings = [line for line in log.splitlines()
                if 'Overfull' in line or 'undefined' in line or 'multiply defined' in line]
    if warnings:
        print('\n'.join(warnings))
        raise SystemExit('Resolve layout/reference warnings before delivery.')
    pdf = ROOT / (NAME + '.pdf')
    shutil.copy2(build / pdf.name, pdf)
    receipt = {'source': source.name, 'pdf': pdf.name, 'pdflatex_passes': 3,
               'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
               'pdf_sha256': hashlib.sha256(pdf.read_bytes()).hexdigest(),
               'source_bytes': source.stat().st_size, 'pdf_bytes': pdf.stat().st_size,
               'overfull_or_reference_warnings': warnings}
    (ROOT / 'evidence/build.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
