"""Flatten the LaTeX source and build the supplied article with pdfLaTeX."""
from pathlib import Path
import os
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
NAME = 'ipra_checked_presentation'
TEX_ENV = os.environ.copy()


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, env=TEX_ENV,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise RuntimeError(result.stdout[-14000:])
    return result.stdout


def flatten(text):
    text = re.sub(r'\\input\{([^}]+)\}',
                  lambda m: flatten((ROOT / m.group(1)).read_text()), text)
    return re.sub(r'\\lstinputlisting\{([^}]+)\}',
                  lambda m: '\\begin{lstlisting}\n' +
                  (ROOT / m.group(1)).read_text().rstrip() +
                  '\n\\end{lstlisting}', text)


def main():
    (ROOT / (NAME + '.tex')).write_text(flatten((ROOT / 'paper_source.tex').read_text()))
    latex = shutil.which('pdflatex')
    pdftex = shutil.which('pdftex')
    kpse = shutil.which('kpsewhich')
    if not all((latex, pdftex, kpse)):
        raise SystemExit('Install TeX Live with pdfLaTeX to rebuild this PDF.')
    ini_lookup = subprocess.run([kpse, 'pdflatex.ini'], text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if not ini_lookup.stdout.strip():
        # Some container images have installed TeX trees but absent filename databases.
        # Scan the existing trees directly, only for these child processes.
        trees = [str(p) for p in map(Path, ['/usr/share/texlive/texmf-dist',
                                          '/usr/share/texmf', '/var/lib/texmf']) if p.exists()]
        if trees:
            TEX_ENV['TEXMF'] = '{' + ','.join(trees) + '}'
    build = ROOT / '.build'
    build.mkdir(exist_ok=True)
    flags = []
    found = subprocess.run([kpse, 'pdflatex.fmt'], text=True, env=TEX_ENV,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout.strip()
    if not found:
        fmt = build / 'pdflatex.fmt'
        if not fmt.exists():
            run([pdftex, '-ini', '-etex', '-interaction=nonstopmode', '-halt-on-error',
                 '-jobname=pdflatex', '-progname=pdflatex',
                 '-output-directory=' + str(build), 'pdflatex.ini'])
        flags = ['-fmt=' + str(fmt)]
    output = ''
    for _ in range(3):
        output = run([latex, *flags, '-interaction=nonstopmode', '-halt-on-error',
                      '-output-directory=' + str(build), NAME + '.tex'])
    shutil.copyfile(build / (NAME + '.pdf'), ROOT / (NAME + '.pdf'))
    (ROOT / 'evidence/latex_build.txt').write_text(output)
    warnings = [line for line in output.splitlines()
                if any(key in line for key in ['Overfull', 'Underfull', 'undefined', 'Warning'])]
    print('\n'.join(warnings) if warnings else 'PDF compiled; no layout or reference warnings.')
    print(NAME + '.pdf')


if __name__ == '__main__':
    main()
