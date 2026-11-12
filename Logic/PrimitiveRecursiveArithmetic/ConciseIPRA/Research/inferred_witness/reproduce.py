"""Reproduce the complete checker measurements and validation evidence."""
from pathlib import Path
import ast
import hashlib
import importlib.util
import json
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CODE = ROOT / 'code'
EVIDENCE = ROOT / 'evidence'
sys.path.insert(0, str(CODE))
from verify import metrics


def run(command):
    completed = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if completed.returncode:
        print(completed.stdout)
        print(completed.stderr, file=sys.stderr)
        raise SystemExit(completed.returncode)
    return completed.stdout


def main():
    EVIDENCE.mkdir(exist_ok=True)
    run([sys.executable, str(CODE / 'verify.py')])
    verification = json.loads((CODE / 'verification.json').read_text())
    (EVIDENCE / 'verification.json').write_text(json.dumps(verification, indent=2) + '\n')
    run([sys.executable, str(CODE / 'independent_validation.py'),
         str(CODE / 'checker.py'), str(EVIDENCE / 'independent_validation_results.json')])
    independent = json.loads((EVIDENCE / 'independent_validation_results.json').read_text())
    rows = [
        ('Inferred opening (selected)', CODE / 'checker.py'),
        ('Matched equality opening', CODE / 'control.py'),
        ('Matched equality output', CODE / 'output_control.py'),
        ('Incoming witness discharge', ROOT / 'reference/upstream_witness.py'),
        ('Incoming uniform binding', ROOT / 'reference/upstream_uniform_binding.py'),
        ('Incoming clause contexts', ROOT / 'reference/upstream_clause_contexts.py'),
        ('Inferred opening with fuel', CODE / 'checker_fuel.py'),
        ('Incoming witness with fuel', ROOT / 'reference/upstream_witness_fuel.py'),
    ]
    comparison = []
    for label, path in rows:
        data = metrics(path)
        comparison.append(dict(label=label, path=str(path.relative_to(ROOT)), **data))
        if path.parent == CODE:
            tree = ast.parse(path.read_text())
            normalized = ast.unparse(tree) + '\n'
            path.with_name(path.stem + '.normalized.py').write_text(normalized)
    report = {
        'python': platform.python_version(),
        'normalization': 'remove leading module docstring; ast.unparse; append one newline',
        'token_exclusions': ['ENCODING', 'ENDMARKER', 'NEWLINE', 'NL', 'INDENT', 'DEDENT', 'COMMENT'],
        'gzip': {'compresslevel': 9, 'mtime': 0, 'input': 'normalized source'},
        'rows': comparison,
    }
    (EVIDENCE / 'comparison.json').write_text(json.dumps(report, indent=2) + '\n')
    header = 'label,normalized_bytes,significant_tokens,ast_nodes,gzip9_bytes\n'
    csv = header + ''.join(','.join(str(row[key]) for key in
        ['label', 'normalized_bytes', 'significant_tokens', 'ast_nodes', 'gzip9_bytes']) + '\n'
        for row in comparison)
    (EVIDENCE / 'comparison.csv').write_text(csv)
    table = [r'\begin{table}[htbp]', r'\centering\small',
             r'\begin{tabular}{@{}lrrrr@{}}', r'\toprule',
             r'Complete program & Bytes & Tokens & AST & Gzip 9\\', r'\midrule']
    for row in comparison:
        table.append(row['label'] + ' & ' + ' & '.join(f'{row[key]:,}' for key in
            ['normalized_bytes', 'significant_tokens', 'ast_nodes', 'gzip9_bytes']) + r'\\')
    table += [r'\bottomrule', r'\end{tabular}',
              r'\caption{Complete programs under one reproducible source-measurement convention.}',
              r'\label{tab:metrics}', r'\end{table}']
    (EVIDENCE / 'metrics_table.tex').write_text('\n'.join(table) + '\n')
    (EVIDENCE / 'summary_macros.tex').write_text(
        r'\newcommand{\NewBytes}{' + f"{comparison[0]['normalized_bytes']:,}" + '}\n')
    (EVIDENCE / 'metrics.json').write_text(json.dumps(verification['metrics'], indent=2) + '\n')
    summary = {
        'python': platform.python_version(),
        'primary_sha256': hashlib.sha256((CODE / 'checker.py').read_bytes()).hexdigest(),
        'accepted_certificates': len(verification['accepted']),
        'rejected_adversarial_objects': len(verification['rejected']),
        'cli_checks': verification['cli_checks'],
        'control_translations': verification['control_translations'],
        'fuel_boundary_checks': verification['fuel_exact_and_one_less_checks'],
        'independent_checks': independent['total_checks'],
        'independent_failures': len(independent['failures']),
        'guard_creation_regression': verification['guard_creation_regression'],
    }
    (EVIDENCE / 'reproduction_summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
