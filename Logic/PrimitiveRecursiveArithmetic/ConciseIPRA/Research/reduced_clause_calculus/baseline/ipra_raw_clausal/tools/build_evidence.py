"""Build report tables from the executed validation evidence."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
evidence = ROOT / 'evidence'
rows = json.loads((evidence / 'metrics.json').read_text())
metrics = {row['program']: row for row in rows}
labels = {
    'matched_canonical': 'Matched canonical five-rule control',
    'matched_control': 'Matched raw six-rule control',
    'clausal_eval': r'\textbf{Raw five-rule checker}',
}
lines = [r'\begin{center}', r'\small',
         r'\begin{tabular}{@{}lrrrr@{}}', r'\toprule',
         r'Complete program & \shortstack{Normalized\\bytes} & Tokens & AST & Gzip-9\\',
         r'\midrule']
for key in ('matched_canonical', 'matched_control', 'clausal_eval'):
    row = metrics[key]
    values = [row[k] for k in ('normalized_bytes', 'significant_tokens',
                              'ast_nodes', 'gzip9_bytes')]
    lines.append(labels[key] + ' & ' + ' & '.join(f'{v:,}' for v in values) + r'\\')
lines += [r'\midrule',
          r'Upstream canonical checker (reference) & 3,305 & 946 & 1,072 & 1,073\\',
          r'\bottomrule', r'\end{tabular}', r'\end{center}']
base, new = metrics['matched_canonical'], metrics['clausal_eval']
delta = {key: base[key] - new[key] for key in
         ('normalized_bytes', 'significant_tokens', 'ast_nodes', 'gzip9_bytes')}
lines.append(
    'Relative to the matched canonical control, the new checker saves '
    f"{delta['normalized_bytes']} normalized bytes "
    f"({100 * delta['normalized_bytes'] / base['normalized_bytes']:.1f}\\%), "
    f"{delta['significant_tokens']} significant tokens, and "
    f"{delta['ast_nodes']} AST nodes. Its normalized gzip-9 file is "
    f"{delta['gzip9_bytes']} bytes smaller.")
(evidence / 'metrics_table.tex').write_text('\n'.join(lines) + '\n')
checks = json.loads((evidence / 'verification.json').read_text())
summary = (
    f"The final execution accepted {checks['positive_examples']} representative "
    'positive proofs and verified both raw proof-translation directions with '
    'identical end formulas. It rejected '
    f"{checks['negative_examples']} adversarial certificates. All "
    f"{checks['public_cli_runs']} public command-line runs, including runs with "
    'Python optimization enabled, returned the expected status and output. '
    'The canonical control also passed its representative reflexivity, '
    'introduction, and canonical-syntax checks.\n\n'
    'The accepted corpus includes both iterator computation equations, '
    'nested term templates, a used induction hypothesis, clause specialization, '
    'compound binder nesting, and capture-avoiding witness insertion. '
    'The raw six-to-five translation satisfied the stated bound of at most '
    'nine times as many inference nodes on every executed example; this '
    'does not bound term-label sizes or JSON length.\n')
(evidence / 'validation_summary.tex').write_text(summary)
print(json.dumps({'canonical_delta': delta, 'verification_counts': {
    k: checks[k] for k in ('positive_examples', 'negative_examples', 'public_cli_runs')
}}, indent=2))
