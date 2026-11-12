"""Create a standalone TeX source and compile the complete report, no shell escape."""
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def expand(path):
    text = path.read_text()
    def input_file(match):
        child = ROOT / match.group(1)
        if not child.suffix:
            child = child.with_suffix('.tex')
        return '\n% BEGIN INCLUDED ' + match.group(1) + '\n' + expand(child) + '\n% END INCLUDED ' + match.group(1) + '\n'
    text = re.sub(r'\\input\{([^}]+)\}', input_file, text)
    def listing(match):
        options = match.group(1) or ''
        return '\\begin{lstlisting}' + options + '\n' + (ROOT / match.group(2)).read_text().rstrip() + '\n\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}', listing, text)


def main():
    standalone = ROOT / 'ipra_uniform_premise.tex'
    standalone.write_text(expand(ROOT / 'report.tex'))
    with tempfile.TemporaryDirectory(prefix='ipra_report_build_') as folder:
        temporary = Path(folder)
        shutil.copy2(standalone, temporary / standalone.name)
        logs = []
        for _ in range(3):
            command = ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                       '-no-shell-escape', standalone.name]
            result = subprocess.run(command, cwd=temporary, text=True, capture_output=True)
            logs.append(result.stdout + result.stderr)
            if result.returncode:
                (ROOT / 'evidence/build.log').write_text('\n'.join(logs))
                raise SystemExit('TeX compilation failed; see evidence/build.log')
        shutil.copy2(temporary / standalone.with_suffix('.pdf').name,
                     ROOT / standalone.with_suffix('.pdf').name)
        (ROOT / 'evidence/build.log').write_text((temporary / standalone.with_suffix('.log').name).read_text())
    print(str(ROOT / 'ipra_uniform_premise.pdf'))


if __name__ == '__main__':
    main()
