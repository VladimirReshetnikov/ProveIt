"""Expand the paper to one .tex file and compile it without shell escape."""
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def expand(text):
    def include(match):
        return expand((ROOT / match.group(1)).read_text())
    text = re.sub(r'\\input\{([^}]+)\}', include, text)
    def listing(match):
        options, path = match.group(1), match.group(2)
        return '\\begin{lstlisting}' + (options or '') + '\n' + (ROOT / path).read_text() + '\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}', listing, text)


def main():
    standalone = ROOT / 'ipra_witness_rule.tex'
    standalone.write_text(expand((ROOT / 'main.tex').read_text()))
    environment = dict(os.environ)
    records = []
    with tempfile.TemporaryDirectory(prefix='ipra-tex-') as temp:
        work = Path(temp)
        compiler = shutil.which('pdflatex')
        if not compiler:
            raise RuntimeError('Install a TeX distribution providing pdflatex.')
        fmt = subprocess.run(['kpsewhich', 'pdflatex.fmt'], text=True, capture_output=True)
        extra = []
        if not fmt.stdout.strip():
            # Some preinstalled distributions have source packages but no
            # generated search database or format. Build an isolated format;
            # no system configuration or user home directory is modified.
            trees = [p for p in ['/usr/share/texlive/texmf-dist', '/usr/share/texmf'] if Path(p).is_dir()]
            if not trees:
                raise RuntimeError('TeX format missing; configure the installed TeX distribution.')
            environment['TEXMF'] = '{' + ','.join(trees) + '}'
            init = subprocess.run(['pdftex', '-ini', '-etex', '-jobname=pdflatex',
                                   '-progname=pdflatex', '-interaction=nonstopmode',
                                   'pdflatex.ini'], cwd=work, env=environment,
                                  text=True, capture_output=True)
            if init.returncode:
                raise RuntimeError('Isolated TeX format creation failed:\n' + init.stdout[-5000:])
            extra = ['-fmt=' + str(work / 'pdflatex.fmt')]
        # Latin Modern's map is explicit in the source so this also works
        # when system font-map caches have not been generated.
        for pass_number in range(1, 4):
            run = subprocess.run([compiler, *extra, '-no-shell-escape',
                                  '-interaction=nonstopmode', '-halt-on-error',
                                  '-file-line-error', '-output-directory=' + str(work),
                                  str(standalone)], cwd=ROOT, env=environment,
                                 text=True, capture_output=True)
            records.append({'pass': pass_number, 'returncode': run.returncode})
            if run.returncode:
                (ROOT / 'evidence/build_failure.txt').write_text(run.stdout + run.stderr)
                raise RuntimeError('PDF compilation failed:\n' + run.stdout[-7000:])
        log = (work / 'ipra_witness_rule.log').read_text(errors='replace')
        warnings = [line for line in log.splitlines()
                    if any(word in line for word in ['Warning:', 'Overfull', 'Underfull'])]
        shutil.copyfile(work / 'ipra_witness_rule.pdf', ROOT / 'ipra_witness_rule.pdf')
        (ROOT / 'evidence/build.json').write_text(json.dumps({
            'passes': records, 'warnings': warnings, 'shell_escape': False,
            'standalone': standalone.name, 'pdf': 'ipra_witness_rule.pdf'}, indent=2) + '\n')
    print(json.dumps({'pdf': str(ROOT / 'ipra_witness_rule.pdf'), 'warnings': warnings}))


if __name__ == '__main__':
    main()
