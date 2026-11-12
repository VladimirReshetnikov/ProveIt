"""Build the paper and its fully expanded single-file LaTeX source."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def expand(text):
    text = re.sub(r"\\input\{([^{}]+)\}",
                  lambda m: expand((ROOT / m.group(1)).read_text()), text)
    return re.sub(r"\\lstinputlisting(?:\[[^]]*\])?\{([^{}]+)\}",
                  lambda m: "\\begin{lstlisting}[language=Python]\n"
                  + (ROOT / m.group(1)).read_text()
                  + "\n\\end{lstlisting}", text)


def main():
    (ROOT / 'report_standalone.tex').write_text(expand((ROOT / 'report.tex').read_text()))
    directory = ROOT / '_build'
    directory.mkdir(exist_ok=True)
    # Start from fresh auxiliary data, including after an interrupted build.
    for suffix in ('aux', 'out', 'toc'):
        (directory / ('report.' + suffix)).unlink(missing_ok=True)
    command = ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
               '-halt-on-error', '-output-directory=' + str(directory), 'report.tex']
    passes = []
    for _ in range(3):
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        passes.append(result.returncode)
        if result.returncode:
            print(result.stdout[-7000:])
            print(result.stderr[-2000:])
            raise SystemExit(result.returncode)
    log = (directory / 'report.log').read_text(errors='replace')
    bad = [line for line in log.splitlines()
           if 'undefined' in line.lower() or 'Overfull' in line
           or 'multiply defined' in line.lower()]
    shutil.copy2(directory / 'report.pdf', ROOT / 'report.pdf')
    receipt = {'passes': passes, 'warnings_requiring_review': bad,
               'pdf_bytes': (ROOT / 'report.pdf').stat().st_size,
               'pdf_sha256': hashlib.sha256((ROOT / 'report.pdf').read_bytes()).hexdigest(),
               'standalone_source_bytes': (ROOT / 'report_standalone.tex').stat().st_size}
    (ROOT / 'evidence/build.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
