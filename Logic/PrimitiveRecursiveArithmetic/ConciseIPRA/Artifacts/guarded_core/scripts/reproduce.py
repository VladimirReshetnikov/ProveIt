"""Reproduce measurements and finite CLI evidence. No checker imports this file."""
import ast
import csv
import gzip
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parents[1]
PROFILES = [
    ('reference/baseline_bytes.py', 'local_neutral', True, False, 'Current byte profile'),
    ('reference/baseline_tokens.py', 'global_plain', True, False, 'Current token profile'),
    ('reference/baseline_ast.py', 'local_neutral', True, False, 'Current AST profile'),
    ('code/checker.py', 'local_neutral', False, False, 'Direct guarded checker'),
    ('code/checker_bytes.py', 'local_neutral', False, False, 'Guarded byte profile'),
    ('code/checker_tokens.py', 'global_plain', False, False, 'Guarded token profile'),
    ('code/checker_ast.py', 'local_neutral', False, False, 'Guarded AST profile'),
    ('code/readable_checker.py', 'local_neutral', False, False, 'Readable guarded checker'),
    ('code/strict_checker.py', 'local_neutral', False, True, 'Guarded strict-goal checker'),
    ('reference/baseline_strict_goal.py', 'local_neutral', True, True, 'Current core plus strict goal parser'),
]


class RemoveDocstrings(ast.NodeTransformer):
    def strip(self, node):
        self.generic_visit(node)
        if (node.body and isinstance(node.body[0], ast.Expr)
                and isinstance(node.body[0].value, ast.Constant)
                and isinstance(node.body[0].value.value, str)):
            node.body.pop(0)
        return node
    visit_Module = visit_FunctionDef = visit_AsyncFunctionDef = visit_ClassDef = strip


def measure(relative, label):
    path = ROOT / relative
    raw = path.read_bytes()
    normalized = (ast.unparse(RemoveDocstrings().visit(ast.parse(raw))) + '\n').encode()
    ignored = {tokenize.COMMENT, tokenize.NL, tokenize.NEWLINE,
               tokenize.INDENT, tokenize.DEDENT, tokenize.ENDMARKER}
    significant = [t for t in tokenize.generate_tokens(io.StringIO(normalized.decode()).readline)
                   if t.type not in ignored]
    row = dict(source=relative, label=label, raw_bytes=len(raw),
               normalized_bytes=len(normalized), tokens=len(significant),
               ast_nodes=sum(1 for _ in ast.walk(ast.parse(normalized))),
               gzip9_bytes=len(gzip.compress(normalized, compresslevel=9, mtime=0)),
               raw_gzip9_bytes=len(gzip.compress(raw, compresslevel=9, mtime=0)),
               sha256=hashlib.sha256(raw).hexdigest())
    (ROOT / 'evidence' / (path.name + ('.reference' if relative.startswith('reference/') else '')
                        + '.normalized.gz')).write_bytes(gzip.compress(normalized, compresslevel=9, mtime=0))
    return row


def run(relative, name, payload, expected, optimized):
    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / relative)]
    try:
        result = subprocess.run(command, input=payload, capture_output=True,
                                text=True, timeout=15)
        accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
        error = result.stderr[-1800:]
    except subprocess.TimeoutExpired:
        accepted, error = False, 'Timeout (not acceptance)'
    row = dict(profile=relative, case=name, optimized=optimized,
               expected=expected, accepted=accepted, ok=accepted == expected)
    if not row['ok']:
        row['stderr'] = error
    return row


def main():
    fixtures = json.loads((ROOT / 'tests/root_cases/cases.json').read_text())
    inherited = json.loads((ROOT / 'tests/cases.json').read_text())
    negative = [r for r in inherited if not r['accept']]
    for name in ('context_leak_attack', 'future_witness_capture'):
        negative.append(dict(name=name, packet=json.loads((ROOT / 'tests' / (name + '.json')).read_text())))
    malformed = ['', '{}', 'null', 'true', '42', '"x"', '["x"]',
                 '[[true,0,0,0],[0,[0]]]', '[[[0,3.0]]]', '[[[],0,0,0,0],[0,[0]]]']
    rows, metrics = [], []
    for relative, protocol, baseline, strict, label in PROFILES:
        metrics.append(measure(relative, label))
        for case in fixtures:
            payload = (ROOT / 'tests/root_cases' / case['packets'][protocol]['filename']).read_text()
            expected = case['expected'] or baseline
            if strict:
                expected = expected and (case['canonical_goal'] or
                           baseline and case['name'] == 'old_atomic_case_D_y_eq_one')
            for optimized in (False, True):
                rows.append(run(relative, case['name'], payload, expected, optimized))
        for case in negative:
            retired = case['name'] == 'induction_step_with_base_only_context'
            expected = retired and not baseline and not strict
            for optimized in (False, True):
                rows.append(run(relative, ('retired_mode_' if retired else 'negative_') + case['name'],
                                json.dumps(case['packet']), expected, optimized))
        for j, payload in enumerate(malformed):
            for optimized in (False, True):
                rows.append(run(relative, 'malformed_' + str(j), payload, False, optimized))
    summary = dict(profiles=len(PROFILES), cli_checks=len(rows),
                   mismatches=sum(not r['ok'] for r in rows),
                   canonical_named_examples=sum(c['canonical_goal'] for c in fixtures),
                   caveat='Finite executable evidence; universal metatheorems are proved in report.tex.')
    environment = dict(python=sys.version, zlib=zlib.ZLIB_RUNTIME_VERSION,
                       normalization='Remove actual docstrings; ast.unparse; one final newline',
                       compression='gzip.compress(source, compresslevel=9, mtime=0), wrapper included')
    evidence = ROOT / 'evidence'
    (evidence / 'validation.json').write_text(json.dumps(dict(summary=summary, results=rows), indent=2) + '\n')
    (evidence / 'metrics.json').write_text(json.dumps(dict(environment=environment, programs=metrics), indent=2) + '\n')
    with (evidence / 'metrics.csv').open('w', newline='') as output:
        writer = csv.DictWriter(output, fieldnames=metrics[0].keys())
        writer.writeheader()
        writer.writerows(metrics)
    tex = ['\\begin{center}\\small', '\\begin{tabular}{lrrrr}', '\\toprule',
           'Standalone program & Bytes & Tokens & AST & Gzip 9\\\\', '\\midrule']
    for i, row in enumerate(metrics[:7]):
        if i == 3:
            tex.append('\\midrule')
        tex.append(f"{row['label']} & {row['normalized_bytes']} & {row['tokens']} & {row['ast_nodes']} & {row['gzip9_bytes']}\\\\")
    tex += ['\\bottomrule', '\\end{tabular}', '\\end{center}']
    (evidence / 'metrics_table.tex').write_text('\n'.join(tex) + '\n')
    strict = {r['source']: r for r in metrics}
    extra = '\n'.join([
        '\\begin{center}\\small\\begin{tabular}{lrrrr}\\toprule',
        'Additional whole module & Bytes & Tokens & AST & Gzip 9\\\\\\midrule',
        *[f"{r['label']} & {r['normalized_bytes']} & {r['tokens']} & {r['ast_nodes']} & {r['gzip9_bytes']}\\\\"
          for r in metrics[7:]],
        '\\bottomrule\\end{tabular}\\end{center}', ''])
    (evidence / 'extra_metrics_table.tex').write_text(extra)
    (evidence / 'validation_summary.tex').write_text(
        f"The delivered verification ran {len(rows)} command-line checks across {len(PROFILES)} whole programs, "
        f"in ordinary and optimized Python, with {summary['mismatches']} mismatches. "
        f"There are {summary['canonical_named_examples']} canonical named examples, including a "
        "guarded induction derivation whose hypothesis is used, together with an administrative "
        "example and an old atomic case theorem that the deterministic checker rejects.\n")
    print(json.dumps(summary, indent=2))
    if summary['mismatches']:
        print(json.dumps([r for r in rows if not r['ok']], indent=2))
        raise SystemExit(1)


if __name__ == '__main__':
    main()
