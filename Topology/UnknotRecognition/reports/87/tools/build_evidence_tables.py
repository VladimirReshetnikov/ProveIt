#!/usr/bin/env python3
"""Regenerate article tables and compact CSV data from the archived JSON.

This uses only the Python standard library. It does not rerun benchmarks.
"""

import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'evidence'
TABLES = ROOT / 'article' / 'tables'


def read(name):
    return json.loads((EVIDENCE / name).read_text())


def csv_write(name, fields, rows):
    with (EVIDENCE / name).open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fields)
        writer.writeheader()
        writer.writerows(rows)


def latex_table(name, columns, header, rows, caption, label):
    TABLES.mkdir(parents=True, exist_ok=True)
    text = '\\begin{table}[htbp]\n\\centering\n\\small\n'
    text += '\\begin{tabular}{@{}' + columns + '@{}}\n\\toprule\n'
    text += header + '\\\\\n\\midrule\n'
    text += ''.join(' & '.join(row) + '\\\\\n' for row in rows)
    text += '\\bottomrule\n\\end{tabular}\n'
    text += '\\caption{' + caption + '}\n\\label{' + label + '}\n\\end{table}\n'
    (TABLES / name).write_text(text)


def main():
    support = read('maximal_support_final_benchmark.json')
    names = {
        'cap_3_5_2': r'\code{cap\_3\_5\_2}',
        'cap_3_5_3': r'\code{cap\_3\_5\_3}',
        'cap_1_2_3': r'\code{cap\_1\_2\_3}',
        'fibonacci_lst_09': 'LST9, mixed',
        'fibonacci_lst_09_meridian': 'LST9, meridian',
        'pachner_36_fixed_row_miss': 'Pachner36',
    }
    support_rows = []
    for case in support['cases']:
        for row in case['measurements']:
            support_rows.append(dict(
                case=case['name'], tetrahedra=case['tetrahedra'], mode=row['mode'],
                status=row['status'], incumbent_median_seconds=row['left_median_seconds'],
                comparison_median_seconds=row['right_median_seconds'],
                median_paired_ratio=row['median_paired_ratio'],
                ratio_of_medians=row['ratio_of_medians'],
                minimum_paired_ratio=min(row['paired_ratios']),
                maximum_paired_ratio=max(row['paired_ratios']),
            ))
    csv_write('support_timings.csv', list(support_rows[0]), support_rows)
    for mode, filename, scope in [
        ('fresh-source', 'support_fresh.tex', 'fresh source'),
        ('prepared-source', 'support_prepared.tex', 'shared prepared source'),
    ]:
        rows = [[names[r['case']], str(r['tetrahedra']),
                 f"{1000*r['incumbent_median_seconds']:.2f}",
                 f"{1000*r['comparison_median_seconds']:.2f}",
                 f"{r['median_paired_ratio']:.3f}"]
                for r in support_rows if r['mode'] == mode]
        latex_table(filename, 'lrrrr',
                    r'Case & $t$ & Incumbent (ms) & New (ms) & Paired new/old', rows,
                    'Complete supplied-sector calls with ' + scope +
                    '. Nine paired trials; lower paired new/old is favorable. '
                    'Time columns are individual medians. LST9 denotes the '
                    'nine-tetrahedron Fibonacci layered source.',
                    'tab:support-' + mode)

    geometric = read('parallelity-port-audit-final.json')
    geo_rows = []
    for row in geometric['timing']:
        ratios = [p['literal']/p['compressed'] for p in row['rounds']]
        geo_rows.append(dict(tetrahedra=row['tetrahedra'], multiplier=row['multiplier'],
            compressed_median_seconds=row['compressed_median_seconds'],
            literal_median_seconds=row['literal_median_seconds'],
            median_paired_literal_over_compressed=row['median_literal_over_compressed'],
            minimum_paired_ratio=min(ratios), maximum_paired_ratio=max(ratios),
            common_output_bytes=row['common_output_bytes']))
    csv_write('geometry_timings.csv', list(geo_rows[0]), geo_rows)
    latex_table('geometry_timing.tex', 'rrrrr',
        r'$t$ & Multiplier & Compressed (ms) & Literal (ms) & Paired literal/compressed',
        [[str(r['tetrahedra']), f"{r['multiplier']:,}",
          f"{1000*r['compressed_median_seconds']:.2f}",
          f"{1000*r['literal_median_seconds']:.2f}",
          f"{r['median_paired_literal_over_compressed']:.3f}"] for r in geo_rows],
        'Matched supplied-surface port recovery, including source construction, '
        'proof replay and common-output serialization. Seven paired trials. '
        'A paired ratio above one favors compression.', 'tab:geometry-timing')

    abstract = read('maximal_support_results.json')['abstract']
    abstract_rows = [dict(m=r['m'], coordinates=r['coordinates'],
        raw_dimension=r['raw_dimension'], effective_dimension=r['effective_dimension'],
        pair_closure_forced=r['pair_closure_forced'], exact_forced=r['exact_forced'],
        raw_coordinate_arrangement_bases=r['raw_coordinate_arrangement_bases'])
        for r in abstract]
    csv_write('abstract_family.csv', list(abstract_rows[0]), abstract_rows)
    rows = []
    for r in abstract_rows:
        if r['effective_dimension'] != 1:
            continue
        n = int(r['raw_coordinate_arrangement_bases'])
        if n < 10**7:
            count = f'{n:,}'
        else:
            coefficient, exponent = f'{n:.3e}'.split('e')
            count = r'$\approx ' + coefficient + r'\times10^{' + str(int(exponent)) + '}$'
        rows.append([str(r['m']), str(r['raw_dimension']), '1',
                     str(r['pair_closure_forced']), str(r['exact_forced']), count])
    latex_table('abstract_family.tex', 'rrrrrl',
        r'$m$ & Raw $d$ & Effective $s$ & Pair zeros & Exact zeros & Raw basis candidates',
        rows, 'The abstract cyclic family with effective dimension one. '
        'Large candidate counts are rounded here and exact in the CSV/JSON.',
        'tab:abstract-family')
    summary = dict(
        support_source_audit=read('maximal_support_results.json')['source_summary'],
        regression_tests_passed=59,
        geometric_finite_cases=geometric['finite_cases'],
        geometric_binary_cases=geometric['binary_cases'],
        geometric_literal_boundary_edges=geometric['literal_boundary_edges'],
        geometric_templates_checked=geometric['template_validation']['templates_checked'],
        geometric_distinct_ball_complexes=geometric['template_validation']['distinct_complexes'],
        geometric_port_charts_checked=geometric['template_validation']['port_charts_checked'],
        support_timings=support_rows, geometry_timings=geo_rows,
    )
    (EVIDENCE / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('Wrote four TeX tables, three CSV tables and evidence/summary.json.')


if __name__ == '__main__':
    main()
