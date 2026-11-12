"""Reproduce complete-module sizes and check the finite evidence suite.

These tests validate implementations and sample proof translations. The
universal equivalence and bi-interpretation are proved in the paper.
"""
import ast
import copy
import gzip
import hashlib
import io
import json
from pathlib import Path
import platform
import subprocess
import sys
import tokenize
import zlib

import checker
import control
import translate as tr
import adversarial

ROOT = Path(__file__).resolve().parent.parent
EVIDENCE = ROOT / 'evidence'
EXAMPLES = ROOT / 'code' / 'examples'


def accept(module, c):
    try:
        module.check(c)
        return True
    except (ValueError, TypeError, IndexError, KeyError, RecursionError):
        return False


def cli(module, c, optimized=False):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(module)]
    run = subprocess.run(command, input=json.dumps(c), text=True,
                         capture_output=True, timeout=20)
    return run.returncode == 0 and run.stdout == 'ACCEPT\n'


def metrics(path):
    raw = path.read_bytes()
    normalized = (ast.unparse(ast.parse(raw)) + '\n').encode()
    skip = {tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
            tokenize.DEDENT, tokenize.COMMENT, tokenize.ENDMARKER}
    gz = gzip.compress(normalized, compresslevel=9, mtime=0)
    return dict(path=str(path.relative_to(ROOT)), raw_bytes=len(raw),
                normalized_bytes=len(normalized),
                significant_tokens=sum(t.type not in skip for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)),
                ast_nodes=sum(1 for _ in ast.walk(ast.parse(normalized))),
                gzip9_bytes=len(gz), sha256_raw=hashlib.sha256(raw).hexdigest(),
                sha256_normalized=hashlib.sha256(normalized).hexdigest()), normalized, gz


def run():
    EVIDENCE.mkdir(exist_ok=True)
    EXAMPLES.mkdir(exist_ok=True)
    records = []
    checks = {'inherited_positive': 0, 'inherited_negative': 0,
              'translation_round_trips': 0, 'successor_round_trips': 0,
              'congruence_round_trips': 0, 'adversarial_cases': 0,
              'cli_executions': 0}
    for path in sorted((ROOT / 'reference' / 'fixtures').glob('*.json')):
        c = json.loads(path.read_text())
        expected = not path.name.startswith('reject_')
        if accept(control, c) != expected:
            raise RuntimeError('Control regression: ' + path.name)
        checks['inherited_positive' if expected else 'inherited_negative'] += 1
        for optimized in (False, True):
            if cli(ROOT / 'code' / 'control.py', c, optimized) != expected:
                raise RuntimeError('Control CLI regression: ' + path.name)
            checks['cli_executions'] += 1
        if not expected:
            continue
        d = tr.certificate(c)
        e = tr.certificate(d, False)
        if (e['variables'], e['context'], e['goal']) != (c['variables'], c['context'], c['goal']):
            raise RuntimeError('Changed sequent endpoint')
        before, after = tr.node_count(c['proof']), tr.node_count(d['proof'])
        if after > 9 * before:
            raise RuntimeError('Ninefold node bound violated')
        records.append(dict(case=path.name, original_nodes=before, translated_nodes=after))
        (EXAMPLES / path.name).write_text(json.dumps(d, separators=(',', ':')) + '\n')
        for optimized in (False, True):
            if not cli(ROOT / 'code' / 'checker.py', d, optimized):
                raise RuntimeError('New CLI regression: ' + path.name)
            checks['cli_executions'] += 1
        checks['translation_round_trips'] += 1

    # All counter forms, including literal zero and a symbolic predecessor;
    # updates include a nested binder referring to its outer state.
    for c in [tr.Z, tr.V, ['s', tr.Z]]:
        for a in [tr.Z, tr.V]:
            for h in [tr.Z, tr.V, ['s', tr.V], ['i', tr.V, ['v', 1], ['s', tr.V]]]:
                p = ['succ', c, a, h]
                cert = dict(variables=1, context=[], proof=p, goal=control.infer(p, [], 1))
                tr.certificate(tr.certificate(cert), False)
                checks['successor_round_trips'] += 1

    # Arbitrary fixed templates, repeated variables, and state occurrences
    # under nested binders. Both equality sources are entirely arbitrary.
    g = [tr.eq(['v', 0], ['v', 1])]
    for h in [tr.Z, tr.V, ['s', tr.V], ['i', tr.V, tr.V, ['v', 1]],
              ['i', ['v', 1], tr.V, ['i', ['v', 1], ['v', 0], ['v', 2]]]]:
        p = tr.new_congruence(['hyp', 0], h, g, 2)
        goal = tr.eq(checker.sub(h, ['v', 0]), checker.sub(h, ['v', 1]))
        cert = dict(variables=2, context=g, goal=goal, proof=p)
        checker.check(cert)
        tr.certificate(tr.certificate(cert, False))
        if tr.node_count(p) != 9:
            raise RuntimeError('Eight-added-node congruence bound violated')
        checks['congruence_round_trips'] += 1

    independent = adversarial.run()
    if independent['failed']:
        raise RuntimeError('Independent adversarial tests failed')
    for name, expected, cert in adversarial.cases:
        for optimized in (False, True):
            if cli(ROOT / 'code' / 'checker.py', cert, optimized) != expected:
                raise RuntimeError('Adversarial CLI regression: ' + name)
            checks['cli_executions'] += 1
        checks['adversarial_cases'] += 1

    rows = []
    for path in [ROOT / 'reference' / 'control_seven.py', ROOT / 'code' / 'control.py', ROOT / 'code' / 'checker.py']:
        row, normalized, compressed = metrics(path)
        rows.append(row)
        if path.parent.name == 'code':
            path.with_name(path.stem + '.normalized.py').write_bytes(normalized)
            path.with_name(path.stem + '.normalized.py.gz').write_bytes(compressed)
    (EVIDENCE / 'metrics.json').write_text(json.dumps(rows, indent=2) + '\n')
    table_rows = []
    for label, row in zip(['Archived seven-rule control', 'Matched seven-rule control', 'Computational equality'], rows):
        table_rows.append(label + ' & ' + ' & '.join(str(row[k]) for k in ['normalized_bytes', 'significant_tokens', 'ast_nodes', 'gzip9_bytes']) + r' \\')
    table = '\\begin{tabular}{@{}lrrrr@{}}\n\\toprule\nComplete module & Bytes & Tokens & AST nodes & Gzip 9 \\\\\n\\midrule\n'
    table += '\n'.join(table_rows) + '\n\\bottomrule\n\\end{tabular}\n'
    (EVIDENCE / 'metrics_table.tex').write_text(table)
    summary = dict(python=platform.python_version(), zlib=zlib.ZLIB_VERSION,
                   checks=checks, unexpected_outcomes=0,
                   boundary='Finite implementation and translation checks; not a machine proof of the metatheorems.')
    (EVIDENCE / 'verification.json').write_text(json.dumps(summary, indent=2) + '\n')
    (EVIDENCE / 'translations.json').write_text(json.dumps(records, indent=2) + '\n')
    (EVIDENCE / 'adversarial_results.json').write_text(json.dumps(independent, indent=2) + '\n')
    (EVIDENCE / 'counts.tex').write_text('\\newcommand{\\clicount}{' + str(checks['cli_executions']) + '}\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    run()
