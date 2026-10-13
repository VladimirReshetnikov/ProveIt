"""Render the article's inline tables from retained machine-readable results."""
from __future__ import annotations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def replace_region(text: str, name: str, body: str) -> str:
    start, end = f'% BEGIN {name}', f'% END {name}'
    region = start + '\n' + body + '\n' + end
    if start in text:
        before, tail = text.split(start, 1)
        _, after = tail.split(end, 1)
        return before + region + after
    marker = f'% {name}'
    if text.count(marker) != 1:
        raise ValueError(f'Cannot identify unique table region: {name}')
    return text.replace(marker, region)


def main() -> None:
    val = json.loads((ROOT / 'results/validation.json').read_text())
    bench = json.loads((ROOT / 'results/benchmark.json').read_text())
    article = ROOT / 'article/article.tex'
    text = article.read_text()
    rows = [r'\begin{center}\small',
            r'\begin{tabular}{lrrrr}\toprule',
            r'Audit & Trials & Positive & Exact negative & Unknown\\\midrule']
    for key, name in [('exhaustive_4_by_2', 'Exhaustive $4\times2$'),
                      ('random_matrix_graph', 'Random matrix/graph'),
                      ('planted_generic_positive', 'Planted generic positives')]:
        a = val[key]
        rows.append(f"{name} & {a['cases']:,} & {a['SUCCESS']:,} & {a.get('BLOCKED_EXACT', 0):,} & {a.get('UNKNOWN', 0):,}" + r'\\')
    rows += [r'\bottomrule\end{tabular}', r'\end{center}',
             r'\begin{center}\small\begin{tabular}{lr}\toprule',
             r'Additional algebraic audit & Queries or samples\\\midrule']
    for name, count in [
        ('Forced matroid extensions', val['forced_matroid_intersection']['queries']),
        ('Horn closure versus literal peeling', val['horn_closure_vs_literal_queries']),
        ('Sampled-independence soundness', val['sampled_independence_soundness_queries']),
        ('Projected representative DP versus literal sets', val['representative_dp_vs_literal']),
        ('Complete small-field sample spaces', sum(a['samples'] for a in val['exact_small_field_spaces']))]:
        rows.append(f'{name} & {count:,}' + r'\\')
    rows += [r'\bottomrule\end{tabular}\end{center}']
    text = replace_region(text, 'VALIDATION_TABLE', '\n'.join(rows))
    names = dict(parallel_negative_3='Parallel negative, 3',
                 parallel_negative_5='Parallel negative, 5',
                 parallel_negative_6='Parallel negative, 6',
                 repository_loop='Maintained loop matrix',
                 choice_arms_2='Nonlinear choice, 2 arms',
                 choice_arms_5='Nonlinear choice, 5 arms',
                 generic_positive='Generic positive')
    rows = [r'\begin{center}\small\setlength{\tabcolsep}{5pt}',
            r'\begin{tabular}{lrrrr}\toprule',
            r'Local input & Prior (ms) & New (ms) & Prior/new & Literal (ms)\\\midrule']
    for a in bench['cases']:
        h, l = a['historical_over_proposed'], a['literal_over_proposed']
        rows.append(f"{names[a['name']]} & {h['left_median_ms']:.4f} & {h['right_median_ms']:.4f} & {h['median_paired_ratio']:.3g} & {l['left_median_ms']:.4f}" + r'\\')
    rows += [r'\bottomrule\end{tabular}\end{center}']
    text = replace_region(text, 'BENCHMARK_TABLE', '\n'.join(rows))
    rows = [r'\begin{center}\small\setlength{\tabcolsep}{5pt}',
            r'\begin{tabular}{rrrrrr}\toprule',
            r'Arms & Literal witnesses & Representatives & Literal (ms) & New (ms) & Ratio\\\midrule']
    for a in bench['ablation']:
        c = a['literal_sets_over_representatives']
        literal = a['samples'][0]['literal_sets']['stats']['retained']
        rep = a['samples'][0]['representatives']['stats']['retained']
        rows.append(f"{a['arms']} & {literal:,} & {rep:,} & {c['left_median_ms']:.3f} & {c['right_median_ms']:.3f} & {c['median_paired_ratio']:.3f}" + r'\\')
    rows += [r'\bottomrule\end{tabular}\end{center}']
    text = replace_region(text, 'ABLATION_TABLE', '\n'.join(rows))
    article.write_text(text)

if __name__ == '__main__':
    main()
