"""Build standalone LaTeX and the two complete PDFs without network access."""
from pathlib import Path
import json
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent

def flatten(text):
    def include(match):
        name = match.group(1)
        return flatten((ROOT / (name if name.endswith('.tex') else name + '.tex')).read_text())
    text = re.sub(r'\\input\{([^}]+)\}', include, text)
    def listing(match):
        options, filename = match.groups()
        return '\\begin{lstlisting}' + (options or '') + '\n' + (ROOT / filename).read_text() + '\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}', listing, text)

def compile_pdf(source, destination):
    with tempfile.TemporaryDirectory(prefix='ipra_tex_') as temporary:
        out = Path(temporary)
        logs = []
        for _ in range(3):
            result = subprocess.run(
                ['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                 '-no-shell-escape', '-output-directory', str(out), str(source)],
                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            logs.append(result.stdout)
            if result.returncode:
                (ROOT/'evidence/build_failure.txt').write_text(result.stdout)
                raise RuntimeError('LaTeX failed; see evidence/build_failure.txt')
        logfile = (out/(source.stem+'.log')).read_text()
        warnings = [line for line in logfile.splitlines()
                    if 'Overfull' in line or 'undefined' in line or 'multiply defined' in line]
        if warnings:
            (ROOT/'evidence/build_warnings.txt').write_text('\n'.join(warnings)+'\n')
            raise RuntimeError('Unresolved LaTeX warnings: '+repr(warnings))
        destination.write_bytes((out/(source.stem+'.pdf')).read_bytes())
        return {'source':str(source.relative_to(ROOT)),
                'pdf':str(destination.relative_to(ROOT)),
                'bytes':destination.stat().st_size,
                'overfull_or_unresolved_warnings':warnings}

def main():
    source = ROOT/'ipra_successor_recursion.tex'
    source.write_text(flatten((ROOT/'report.tex').read_text()))
    results = [compile_pdf(source, ROOT/'ipra_successor_recursion.pdf'),
               compile_pdf(ROOT/'supplement/seed_shift_bridge.tex',
                           ROOT/'supplement/seed_shift_bridge.pdf')]
    (ROOT/'evidence/build.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__ == '__main__':
    main()
