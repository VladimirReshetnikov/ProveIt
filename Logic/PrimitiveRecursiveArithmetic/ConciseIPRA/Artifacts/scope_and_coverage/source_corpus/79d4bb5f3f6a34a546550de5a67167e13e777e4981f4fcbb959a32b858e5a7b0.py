"""Expand the standalone TeX and compile the complete report, without shell escape."""
import argparse
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def expand(text):
    text = re.sub(r'\\input\{([^}]+)\}',
                  lambda m: expand((ROOT / m.group(1)).read_text()), text)
    text = re.sub(r'\\lstinputlisting\{([^}]+)\}',
                  lambda m: '\\begin{lstlisting}\n' + (ROOT / m.group(1)).read_text()
                  + '\\end{lstlisting}', text)
    return text


def compile_tex(source, directory, jobname):
    command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
               '-halt-on-error', '-file-line-error', '-output-directory=' + str(directory),
               '-jobname=' + jobname, str(source)]
    logs = []
    for _ in range(3):
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        logs.append(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(logs[-1][-12000:])
    return logs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-standalone', action='store_true')
    args = parser.parse_args()
    standalone = ROOT / 'ipra_affine_supply.tex'
    standalone.write_text(expand((ROOT / 'report.tex').read_text()))
    directory = ROOT / 'build'
    directory.mkdir(exist_ok=True)
    logs = compile_tex(ROOT / 'report.tex', directory, 'ipra_affine_supply')
    shutil.copyfile(directory / 'ipra_affine_supply.pdf', ROOT / 'ipra_affine_supply.pdf')
    (ROOT / 'evidence/latex_build.txt').write_text('\n'.join(logs))
    if args.check_standalone:
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            shutil.copyfile(standalone, tmp / standalone.name)
            # Its source has no local TeX/code inputs; compile from the isolated directory.
            for _ in range(3):
                p = subprocess.run(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                                    '-halt-on-error', standalone.name], cwd=tmp,
                                   text=True, capture_output=True)
                if p.returncode:
                    raise RuntimeError(p.stdout[-12000:] + p.stderr)
            (ROOT / 'evidence/standalone_build.txt').write_text(p.stdout)
    print(ROOT / 'ipra_affine_supply.pdf')


if __name__ == '__main__':
    main()
