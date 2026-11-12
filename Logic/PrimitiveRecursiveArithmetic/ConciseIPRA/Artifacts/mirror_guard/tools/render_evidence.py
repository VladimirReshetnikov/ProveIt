"""Render already measured evidence as tables; no checker imports this file."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    metrics = json.loads((ROOT / 'evidence/metrics.json').read_text())
    rows = {row['file']: row for row in metrics['programs']}
    selected = [
        ('Source dispatch: tokens', 'reference/checkers/source_tokens.py'),
        ('Mirror: tokens', 'code/checker_tokens.py'),
        ('Source dispatch: AST', 'reference/checkers/source_ast.py'),
        ('Mirror: AST', 'code/checker_ast.py'),
        ('Source dispatch: bytes', 'reference/checkers/source_bytes.py'),
        ('Mirror: bytes', 'code/checker_bytes.py'),
        ('Mirror: readable', 'code/readable_checker.py'),
        ('Source: strict derivative', 'reference/checkers/source_strict_derived.py'),
        ('Mirror: strict', 'code/strict_checker.py'),
    ]
    lines = [r'\begin{center}\small', r'\begin{tabular}{lrrrr}',
             r'\toprule', r'Complete program & Tokens & AST nodes & Bytes & Gzip-9\\',
             r'\midrule']
    for i, (name, path) in enumerate(selected):
        row = rows[path]
        if i in (2, 4, 6, 7):
            lines.append(r'\midrule')
        vals = [str(row[k]) for k in ('tokens', 'ast_nodes', 'normalized_bytes', 'gzip9_normalized_bytes')]
        lines.append(name + ' & ' + ' & '.join(vals) + r'\\')
    lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}',
              'All byte and gzip columns use normalized UTF-8 source. '
              'The JSON evidence also records raw-source sizes, raw gzip sizes, hashes, '
              'and exact runtime versions. The strict source derivative is constructed '
              'for this comparison; it is not an upstream frontier claim.']
    (ROOT / 'evidence/metrics_table.tex').write_text('\n'.join(lines) + '\n')
    validation = json.loads((ROOT / 'evidence/validation.json').read_text())
    central = next(row for row in validation['results'] if row['name'] == 'derived_literal_zero_transport')
    cases = json.loads((ROOT / 'evidence/cases.json').read_text())
    central_case = next(row for row in cases if row['name'] == 'derived_literal_zero_transport')
    contextual = next(row for row in cases if row['name'] == 'contextual_zero_source_bootstrap')
    audit = central['audit']
    lines = [
        f"The reproduction run executed {validation['checker_runs']} checker invocations "
        f"on {validation['tests']} distinct fixtures; {validation['passed_runs']} outcomes "
        "matched their declared expectations. Every fixture was checked in both ordinary "
        "and Python optimization mode on each of the five implementations.",
        f"There are {validation['positive_named_proof_trees']} positive named proof trees. "
        "Their structural audit found no nonmirrored atomic introduction and no "
        "primitive transport with literal-zero source.",
        f"The zero-source normalization example has {audit['nodes']} distinct named "
        f"nodes, {audit['atomic_DI']} atomic introductions, and "
        f"{audit['compound_DI']} compound introductions. It has "
        f"{central_case['files']['local']['instructions']} certificate instructions. Its local and global "
        "certificates are retained in the archive.",
        "A second closed certificate proves the shared-left implication "
        r"$(0=1)\Rightarrow(0=2)$, using the variable-left invariant "
        r"$n=I(n,1;u.Su)$. It has "
        f"{contextual['audit']['nodes']} distinct named nodes and "
        f"{contextual['files']['local']['instructions']} instructions, with "
        f"{contextual['audit']['atomic_DI']} mirrored atomic introductions and "
        "no primitive zero-source transport.",
        "One inherited negative control changed only the retired introduction-mode "
        "field; the compact profiles now correctly accept its provable administrative "
        "closure goal, while the strict profile rejects that noncanonical public "
        "formula. This expected change is recorded separately, not counted as an "
        "unchanged rejection.",
    ]
    (ROOT / 'evidence/validation_summary.tex').write_text('\n\n'.join(lines) + '\n')


if __name__ == '__main__':
    main()
