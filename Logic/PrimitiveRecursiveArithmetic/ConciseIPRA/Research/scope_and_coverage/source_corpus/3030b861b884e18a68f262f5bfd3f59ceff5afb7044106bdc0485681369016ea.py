"""Build a standalone TeX source and its PDF using installed TeX only."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
NAME = 'ipra_elimination_assumptions_2026-11-09'


def flatten(path):
    source = path.read_text()
    source = re.sub(r'\\input\{([^}]+)\}',
                    lambda m: flatten(ROOT / m.group(1)), source)
    def listing(match):
        options, filename = match.group(1), match.group(2)
        return ('\\begin{lstlisting}' + (options or '') + '\n'
                + (ROOT / filename).read_text().rstrip() + '\n'
                + '\\end{lstlisting}')
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}', listing, source)


def main():
    source = ROOT / (NAME + '.tex')
    source.write_text(flatten(ROOT / 'report.tex'))
    engine = shutil.which('pdflatex')
    if not engine:
        raise SystemExit('pdflatex is needed; install a standard TeX distribution.')
    # Compile the flattened file in an isolated directory. No appendix,
    # code file or source-tree input is available to this TeX process.
    with tempfile.TemporaryDirectory(prefix='ipra-tex-') as scratch:
        build = Path(scratch)
        shutil.copyfile(source, build / source.name)
        last_output = ''
        for _ in range(3):
            run = subprocess.run([engine, '-no-shell-escape',
                                  '-interaction=nonstopmode', '-halt-on-error',
                                  source.name], cwd=build,
                                 text=True, capture_output=True)
            last_output = run.stdout + run.stderr
            if run.returncode:
                (ROOT / 'evidence/tex_failure.txt').write_text(last_output)
                raise SystemExit(last_output[-10000:])
        log = (build / (NAME + '.log')).read_text(errors='replace')
        warnings = [line for line in log.splitlines()
                    if any(x in line for x in ('Warning:', 'Overfull', 'Underfull'))]
        unresolved = [line for line in warnings
                      if 'undefined' in line.lower() or 'rerun' in line.lower()]
        if unresolved:
            raise SystemExit('Unresolved references after three passes: ' + repr(unresolved))
        pdf = ROOT / (NAME + '.pdf')
        shutil.copyfile(build / pdf.name, pdf)
    receipt = {
        'status': 'PASS',
        'source': source.name,
        'pdf': pdf.name,
        'standalone_source_compiled_in_isolated_directory': True,
        'shell_escape': False,
        'passes': 3,
        'engine': subprocess.run([engine, '--version'], text=True,
                                 capture_output=True).stdout.splitlines()[0],
        'warnings': warnings,
        'unresolved_references': unresolved,
        'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
        'pdf_sha256': hashlib.sha256(pdf.read_bytes()).hexdigest(),
        'pdf_bytes': pdf.stat().st_size,
    }
    (ROOT / 'evidence/build_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    (ROOT / 'evidence/tex_failure.txt').unlink(missing_ok=True)
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
