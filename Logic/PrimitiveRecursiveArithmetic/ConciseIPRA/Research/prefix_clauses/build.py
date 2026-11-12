"""Flatten the report and build its PDF using a local TeX installation."""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def flatten(path):
    source = path.read_text()
    return re.sub(r'\\input\{([^}]+)\}',
                  lambda m: flatten(ROOT / m.group(1)), source)


def main():
    target = ROOT / 'ipra_prefix_clauses.tex'
    target.write_text(flatten(ROOT / 'report.tex'))
    with tempfile.TemporaryDirectory(prefix='ipra-prefix-build-') as temp:
        command = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                   '-output-directory', temp, str(target)]
        logs = []
        for _ in range(2):
            run = subprocess.run(command, cwd=ROOT, text=True,
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            logs.append(run.stdout)
            if run.returncode:
                raise RuntimeError(run.stdout[-6000:])
        shutil.copyfile(Path(temp) / 'ipra_prefix_clauses.pdf',
                        ROOT / 'ipra_prefix_clauses.pdf')
        (ROOT / 'evidence' / 'latex_build.log').write_text('\n'.join(logs))
    print('Built ipra_prefix_clauses.tex and ipra_prefix_clauses.pdf')


if __name__ == '__main__':
    main()
