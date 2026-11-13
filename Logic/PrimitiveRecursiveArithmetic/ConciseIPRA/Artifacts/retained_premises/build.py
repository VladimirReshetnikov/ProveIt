"""Build a self-contained LaTeX source and its PDF using installed pdflatex."""
import re
import os
import shutil
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NAME = 'ipra_retained_premises'


def tex_environment(build):
    """Initialize installed TeX assets locally if their format is missing."""
    env = os.environ.copy()
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], capture_output=True, env=env)
    if probe.returncode == 0 and probe.stdout.strip():
        return env
    trees = [Path('/usr/share/texlive/texmf-dist'), Path('/usr/share/texmf')]
    if not all(p.is_dir() for p in trees):
        raise RuntimeError('Install a complete TeX distribution with pdflatex and the packages used in paper.tex')
    runtime = build / 'texruntime'
    runtime.mkdir(exist_ok=True)
    env['TEXMF'] = '{' + ','.join(map(str, trees)) + '}'
    if not (runtime / 'pdflatex.fmt').exists():
        result = subprocess.run(['pdftex', '-ini', '-interaction=nonstopmode',
            '-jobname=pdflatex', '-progname=pdflatex', '-etex', 'pdflatex.ini'],
            cwd=runtime, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (runtime / 'format-build.log').write_bytes(result.stdout)
        if result.returncode:
            raise RuntimeError('Local TeX format initialization failed; see build/texruntime/format-build.log')
    maps = [trees[1] / 'fonts/map/dvips/lm/lm.map',
            *sorted((trees[0] / 'fonts/map/dvips/amsfonts').glob('*.map'))]
    (runtime / 'pdftex.map').write_bytes(b'\n'.join(p.read_bytes() for p in maps))
    env['TEXFORMATS'] = str(runtime) + os.pathsep
    env['TEXFONTMAPS'] = str(runtime) + os.pathsep
    return env


def expand(text):
    text = re.sub(r'\\input\{([^}]+)\}',
                  lambda m: expand((ROOT / m[1]).read_text()), text)
    return re.sub(r'\\lstinputlisting(?:\[([^]]*)\])?\{([^}]+)\}',
                  lambda m: '\\begin{lstlisting}' + ('[' + m[1] + ']' if m[1] else '') + '\n'
                  + (ROOT / m[2]).read_text().rstrip() + '\n\\end{lstlisting}', text)


def main():
    source = ROOT / (NAME + '.tex')
    source.write_text(expand((ROOT / 'paper.tex').read_text()))
    build = ROOT / 'build'
    build.mkdir(exist_ok=True)
    env = tex_environment(build)
    for _ in range(3):
        result = subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
            '-halt-on-error', '-file-line-error', '-output-directory=' + str(build), str(source)],
            cwd=ROOT, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            print(result.stdout.decode(errors='replace')[-12000:])
            raise SystemExit(result.returncode)
    shutil.copyfile(build / (NAME + '.pdf'), ROOT / (NAME + '.pdf'))
    print(ROOT / (NAME + '.pdf'))


if __name__ == '__main__':
    main()
