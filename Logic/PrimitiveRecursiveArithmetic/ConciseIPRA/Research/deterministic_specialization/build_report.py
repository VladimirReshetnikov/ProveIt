"""Assemble one standalone LaTeX source from reviewed prose and actual evidence."""
import argparse
import ast
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent


def tex_environment():
    """Use configured TeX Live or construct local format/font-map caches.

    The fallback follows the inherited uniform-Step build helper and only
    uses the installed distribution; no network download is performed.
    """
    env = os.environ.copy()
    probe = subprocess.run(['kpsewhich', 'pdflatex.fmt'], capture_output=True, text=True)
    if probe.returncode == 0 and probe.stdout.strip():
        return env
    roots = [Path('/usr/share/texlive/texmf-dist'), Path('/usr/share/texmf')]
    if not all(p.is_dir() for p in roots):
        raise RuntimeError('A configured TeX Live installation is required')
    local = ROOT / 'tmp/tex'
    local.mkdir(parents=True, exist_ok=True)
    env['TEXMF'] = '{' + ','.join(map(str, roots)) + '}'
    env['TEXFORMATS'] = str(local) + os.pathsep
    env['TEXFONTMAPS'] = str(local) + os.pathsep
    if not (local / 'pdflatex.fmt').exists():
        result = subprocess.run(['pdftex', '-ini', '-etex', '-jobname=pdflatex',
                                 '-progname=pdflatex', '-interaction=nonstopmode',
                                 '-halt-on-error', '-output-directory', str(local),
                                 'pdflatex.ini'], cwd=ROOT, env=env,
                                capture_output=True, text=True)
        (local / 'initialization.log').write_text(result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError('Local TeX format generation failed')
    maps = [roots[1] / 'fonts/map/dvips/lm/lm.map']
    maps += [roots[0] / ('fonts/map/dvips/amsfonts/' + name) for name in
             ['cm.map', 'cmextra.map', 'symbols.map', 'latxfont.map']]
    (local / 'pdftex.map').write_text('\n'.join(p.read_text() for p in maps))
    return env


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--pdf', action='store_true')
    args = parser.parse_args()
    text = (ROOT / 'paper/manuscript.tex').read_text()
    replacements = {
        'DETERMINISTIC_THEOREM': 'paper/deterministic_theorem.tex',
        'INHERITED_CHOICE': 'reference/inherited_choice_basis.tex',
        'INHERITED_ORDINARY': 'reference/inherited_ordinary_bridge.tex',
        'INHERITED_PREDECESSOR': 'reference/scalar_predecessor.tex',
        'INHERITED_REFLECTION': 'reference/equality_reflection.tex',
        'INHERITED_RECURSION': 'reference/primitive_recursion.tex',
    }
    for key, path in replacements.items():
        text = text.replace('%<' + key + '>', (ROOT / path).read_text())
    tree = ast.parse((ROOT / 'code/checker.py').read_text())
    if ast.get_docstring(tree) is not None:
        tree.body.pop(0)
    text = text.replace('%<CHECKER_CODE>', ast.unparse(tree))
    metrics = json.loads((ROOT / 'evidence/metrics.json').read_text())['programs']
    by_path = {item['file']: item for item in metrics}
    table = [r'\begin{center}', r'\begin{tabular}{lrrrr}', r'\toprule',
             r'Complete checker & Bytes & Tokens & AST & Gzip-9\\', r'\midrule']
    for label, path in [
        ('Unrestricted, explicit scope', 'reference/unrestricted_explicit.py'),
        ('Deterministic, explicit scope', 'reference/deterministic_explicit.py'),
        ('Unrestricted, scope from context', 'reference/unrestricted_implicit.py'),
        ('Deterministic, scope from context', 'code/checker.py')]:
        m = by_path[path]
        table.append(f"{label} & {m['normalized_bytes']} & {m['significant_tokens']} & {m['ast_nodes']} & {m['gzip9_normalized_bytes']} " + r'\\')
    table += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
    text = text.replace('%<METRICS_TABLE>', '\n'.join(table))
    rows = json.loads((ROOT / 'evidence/translations.json').read_text())['cases']
    rows = sorted(rows, key=lambda x: x['target_json_bytes'], reverse=True)
    table = [r'\begin{center}', r'\small', r'\begin{tabular}{lrr}', r'\toprule',
             r'Example & Source JSON bytes & Target JSON bytes\\', r'\midrule']
    selected = rows[:3]
    selected += [next(x for x in rows if x['case'] == 'induction_uses_hypothesis')]
    for row in selected:
        name = row['case'].replace('_', r'\_')
        table.append(f"{name} & {row['source_json_bytes']} & {row['target_json_bytes']} " + r'\\')
    table += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
    text = text.replace('%<GROWTH_TABLE>', '\n'.join(table))
    if '%<' in text:
        raise ValueError('Unfilled manuscript placeholder')
    (ROOT / 'report.tex').write_text(text)
    print('Assembled standalone report.tex')
    if args.pdf:
        build = ROOT / 'tmp/build'
        build.mkdir(parents=True, exist_ok=True)
        env = tex_environment()
        for number in range(1, 4):
            result = subprocess.run(['pdflatex', '-interaction=nonstopmode',
                                     '-halt-on-error', '-output-directory', str(build),
                                     'report.tex'], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            (build / ('pass' + str(number) + '.log')).write_text(result.stdout + result.stderr)
            if result.returncode:
                raise RuntimeError('LaTeX failed; inspect tmp/build/pass' + str(number) + '.log')
        shutil.copy2(build / 'report.pdf', ROOT / 'report.pdf')
        print('Compiled report.pdf')


if __name__ == '__main__':
    main()
