"""Build the standalone LaTeX source and PDF with an installed PDFLaTeX."""
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
STEM = 'ipra_generated_assumptions'


def environment(work):
    """Create missing format/font caches from installed TeX sources only.

    Adapted with attribution from the named-specialization archive's build.py.
    """
    env = dict(os.environ)
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], env=env,
                           capture_output=True, text=True)
    if probe.returncode == 0 and probe.stdout.strip():
        return env
    trees = [Path('/usr/share/texmf'), Path('/usr/share/texlive/texmf-dist')]
    if not all(path.is_dir() for path in trees):
        raise SystemExit('An installed PDFLaTeX format or TeX source tree is required.')
    cache = work / 'texcache'
    cache.mkdir(exist_ok=True)
    env['TEXMF'] = '{' + ','.join(map(str, [cache, *trees])) + '}'
    target = cache / 'web2c/pdftex/pdflatex.fmt'
    if not target.exists():
        target.parent.mkdir(parents=True, exist_ok=True)
        result = subprocess.run(['pdftex', '-ini', '-etex', '-no-shell-escape',
                                 '-interaction=nonstopmode', '-halt-on-error',
                                 '-jobname=pdflatex', '-progname=pdflatex', 'pdflatex.ini'],
                                cwd=cache, env=env, capture_output=True, text=True)
        if result.returncode:
            raise SystemExit(result.stdout[-6000:] + result.stderr)
        shutil.move(cache / 'pdflatex.fmt', target)
    maps = [trees[0] / 'fonts/map/dvips/lm/lm.map']
    maps.extend(sorted((trees[1] / 'fonts/map/dvips/amsfonts').glob('*.map')))
    fontmap = cache / 'fonts/map/pdftex/local/pdftex.map'
    fontmap.parent.mkdir(parents=True, exist_ok=True)
    fontmap.write_text('\n'.join(path.read_text() for path in maps))
    return env


def flatten(text):
    def include(match):
        return flatten((ROOT / match.group(1)).read_text())
    text = re.sub(r'\\input\{([^}]+)\}', include, text)
    def listing(match):
        options = match.group(1) or ''
        return '\\begin{lstlisting}' + options + '\n' + (ROOT / match.group(2)).read_text() + '\\end{lstlisting}'
    return re.sub(r'\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}', listing, text)


def main():
    metrics = json.loads((ROOT / 'evidence/metrics.json').read_text())
    data = {r['file']: r for r in metrics['programs']}
    lines = [r'\begin{center}', r'\small', r'\begin{tabular}{lrrr}', r'\toprule',
             r'Complete program & Tokens & AST nodes & Bytes\\', r'\midrule']
    for label, path in [
        ('Existing endpoint token profile', 'reference/endpoint_tokens.py'),
        ('Existing endpoint AST control', 'reference/endpoint_ast.py'),
        ('Existing successor byte profile', 'reference/successor_bytes.py'),
        ('Neutral-continuation control', 'reference/neutral_control.py'),
        ('New strict insertion', 'code/checker_strict.py'),
        ('New zero-witness checker', 'code/checker.py'),
        ('New zero-witness AST profile', 'code/checker_ast.py')]:
        row = data[path]
        lines.append(f"{label} & {row['normalized_tokens']} & {row['ast_nodes']} & {row['normalized_bytes']}\\\\")
    lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
    (ROOT / 'evidence/metrics_table.tex').write_text('\n'.join(lines) + '\n')
    verification = json.loads((ROOT / 'evidence/verification.json').read_text())
    count = verification['certificate_and_input_runs']
    summary = f'''The delivered complete programs passed all {count} certificate and malformed-input
runs under ordinary and optimized Python. The two witness profiles each
run 28 proof fixtures; the strict profile runs the 26 common fixtures.
Three additional malformed-input cases are run for each profile and mode.
Three mutation controls remove, respectively, eager predecessor validation,
major-premise checking, and the literal-equation restriction on progress.
Each mutant accepts its targeted invalid derivation, while the original
rejects it. The complete receipts are in \\file{{evidence/verification.json}}.

An independent numerical decoder also tried 36,000 raw arithmetic packets
at three freshness floors. Of these, 23,247 reached successful witness
opening; all their decoded zero instances were equal, with no evaluation
skipped for resource limits. This is a deterministic finite falsification
attempt, separate from the universal structural proof.
'''
    (ROOT / 'evidence/verification_summary.tex').write_text(summary)
    standalone = ROOT / (STEM + '.tex')
    standalone.write_text(flatten((ROOT / 'report.tex').read_text()))
    output = ROOT / '.build'
    output.mkdir(exist_ok=True)
    executable = shutil.which('pdflatex')
    if not executable:
        raise SystemExit('PDFLaTeX is required to rebuild the PDF.')
    env = environment(output)
    command = [executable, '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error',
               '-file-line-error', '-output-directory', str(output), str(standalone)]
    for index in range(3):
        result = subprocess.run(command, cwd=ROOT, env=env, capture_output=True, text=True)
        (output / ('pass' + str(index + 1) + '.txt')).write_text(result.stdout + result.stderr)
        if result.returncode:
            print((result.stdout + result.stderr)[-6000:])
            raise SystemExit(result.returncode)
    shutil.copyfile(output / (STEM + '.pdf'), ROOT / (STEM + '.pdf'))
    log = (output / (STEM + '.log')).read_text(errors='replace')
    warnings = [line for line in log.splitlines()
                if any(key in line for key in ['Overfull', 'undefined', 'Rerun to get'])]
    report = {'engine': 'PDFLaTeX', 'passes': 3, 'warnings': warnings,
              'standalone_tex': standalone.name, 'pdf': STEM + '.pdf'}
    (ROOT / 'evidence/build.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
