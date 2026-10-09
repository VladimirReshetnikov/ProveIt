"""Build compact tables from preserved final raw-saturation measurements."""
from collections import Counter
import json
from pathlib import Path
from statistics import median

ROOT = Path(__file__).resolve().parents[1]
RESULTS = ROOT / 'results'


def load(name):
    return json.loads((RESULTS / name).read_text())


def number(value, scale=1):
    return '--' if value is None else f'{scale*value:,.3f}'


def tex_name(name):
    return name.replace('_', r'\_')


def table(caption, label, header, rows, columns):
    return '\n'.join([
        r'\begin{table}[htbp]', r'\centering\small',
        r'\begin{tabular}{' + columns + '}', r'\toprule',
        ' & '.join(header) + r' \\', r'\midrule',
        *[' & '.join(map(str, row)) + r' \\' for row in rows],
        r'\bottomrule', r'\end{tabular}',
        r'\caption{' + caption + '}', r'\label{' + label + '}',
        r'\end{table}', '',
    ])


def main():
    data = {mode: load(f'raw_saturation_{mode}.json')
            for mode in ('audit', 'kernels', 'stage', 'pipeline')}
    assert len({x['driver_sha256'] for x in data.values()}) == 1
    for x in data.values():
        assert x['candidate_label'] == 'final-preindex-guard'
        assert x['source_hashes'] == data['audit']['source_hashes']
    initial = load('raw_saturation_initial_audit.json')
    assert all(a['saturation']['status'] == b['saturation']['status'] and
               a['saturation'].get('certificate') == b['saturation'].get('certificate')
               for a, b in zip(data['audit']['rows'], initial['rows']))

    summary = {'final_source_hashes_identical_across_modes': True,
               'final_driver_sha256': data['audit']['driver_sha256'],
               'timing_scope': {
                   'kernels': 'internal search on preconstructed abstract SLP presentations; no PD provenance or mandatory source replay',
                   'stage': 'fresh PD validation, presentation reconstruction, group search, and mandatory independent source replay',
                   'pipeline': 'fresh full recognizer with ordinary earlier filters and resource caps'},
               'initial_final_audit_status_and_certificate_equality': True,
               'modes': {}, 'guard_work_comparison': []}
    for mode in ('stage', 'pipeline'):
        rows = data[mode]['rows']
        aa = [r['paired_ratios']['control'] for r in rows
              if r['paired_ratios']['control'] is not None]
        summary['modes'][mode] = {
            'inputs': len(rows), 'measured_calls': 15*len(rows),
            'warmup_calls': 3*len(rows), 'elapsed_seconds': data[mode]['elapsed_seconds'],
            'completed': {arm: sum(r['completion_counts'][arm] for r in rows)
                          for arm in ('baseline', 'control', 'saturation')},
            'aa_ratio_range': [min(aa), max(aa)],
            'outcomes': {arm: dict(Counter(s['arms'][arm]['result']['status']
                                         for r in rows for s in r['samples']))
                         for arm in ('baseline', 'control', 'saturation')},
            'reasons': {arm: dict(Counter(s['arms'][arm]['result'].get('reason') or
                                        s['arms'][arm]['result'].get('method') or
                                        s['arms'][arm]['result']['status']
                                        for r in rows for s in r['samples']))
                        for arm in ('baseline', 'control', 'saturation')},
            'rows': [{key: r[key] for key in ('name', 'crossings', 'median_seconds',
                                            'paired_ratios', 'completion_counts')}
                     for r in rows],
        }
    rows = data['kernels']['rows']
    summary['modes']['kernels'] = {
        'inputs': len(rows), 'measured_calls': 15*len(rows),
        'warmup_calls': 3*len(rows), 'elapsed_seconds': data['kernels']['elapsed_seconds'],
        'completed_calls': sum(sum(r['completion_counts'].values()) for r in rows),
        'search_work_allowance': data['kernels']['kernel_search_allowance'],
        'rows': [{key: r[key] for key in ('bits', 'median_seconds', 'paired_ratio',
                                        'control_ratio', 'completion_counts')}
                 for r in rows],
    }
    rows = data['audit']['rows']
    summary['modes']['audit'] = {
        'inputs': len(rows), 'elapsed_seconds': data['audit']['elapsed_seconds'],
        'outcomes': {arm: dict(Counter(r[arm]['status'] for r in rows))
                     for arm in ('baseline', 'control', 'explicit_false', 'saturation')},
        'compressed_source_replays': sum(2*len(r['replayed']) for r in rows),
        'literal_source_replays': sum(2*len(r['replayed']) for r in rows if len(r['pd']) <= 16),
        'source_binding_rejections': sum(r['source_binding_rejections'] for r in rows),
        'new_version_eight_certificates': sum(r['saturation'].get('certificate', {}).get('version') == 8 for r in rows),
    }
    for name in ('survivor-00', 'monster', 'gordian'):
        old = next(r for r in initial['rows'] if r['name'] == name)
        new = next(r for r in data['audit']['rows'] if r['name'] == name)
        summary['guard_work_comparison'].append({
            'name': name, 'baseline_work': new['baseline']['search_stats']['work'],
            'initial_saturation_work': old['saturation']['search_stats']['work'],
            'final_saturation_work': new['saturation']['search_stats']['work'],
            'initial_incidence': old['saturation']['search_stats'].get('raw_saturation_source_incidence', 0),
            'final_incidence': new['saturation']['search_stats'].get('raw_saturation_source_incidence', 0),
        })
    (RESULTS/'raw_saturation_summary.json').write_text(json.dumps(summary, indent=2)+'\n')

    tables = []
    kernel_rows = []
    for row in data['kernels']['rows']:
        arms = row['samples'][0]['arms']
        kernel_rows.append([
            r'$2^{' + str(row['bits']) + '}$', arms['saturation']['source_nodes'],
            number(row['median_seconds']['ordinary'], 1000),
            number(row['median_seconds']['saturation'], 1000),
            number(row['paired_ratio']), number(row['control_ratio']),
        ])
    tables.append(table(
        'Internal algebraic search on the fixed compressed redundant-presentation family. '
        'Source construction is outside these timings; these are not full knot-recognition calls. '
        'All three arms have the same two-million search-work allowance. '
        'Dashes denote work-limited ordinary/control arms; no ratio uses their censored times. '
        'The ratio is the median of five complete paired ratios, not the ratio of displayed medians.',
        'tab:raw-saturation-kernels',
        ['Power $N$', 'Source nodes', 'Ordinary ms', 'New ms', 'Paired ratio', 'A/A'],
        kernel_rows, 'lrrrrr'))

    chosen = [f'circle-{n}' for n in (15, 31, 63, 127, 255, 511)] + [
        'unknot_braid40', 'hard_unknot_8', 'monster', 'gordian']
    stage_rows = []
    for name in chosen:
        row = next(r for r in data['stage']['rows'] if r['name'] == name)
        stage_rows.append([
            tex_name(name), row['crossings'], number(row['median_seconds']['baseline'], 1000),
            number(row['median_seconds']['saturation'], 1000),
            number(row['paired_ratios']['saturation']), number(row['paired_ratios']['control']),
        ])
    tables.append(table(
        'Selected complete group-stage calls, including fresh PD validation, source reconstruction, '
        'search, and mandatory independent replay. All 28 inputs and all outcomes are retained in the JSON data. '
        'The circle family is an elementary mechanism control. On circle-511, the earlier arms hit '
        'the unchanged 100,000-node allowance; only the new arm completes. '
        'No wall-time limit is imposed in this stage experiment.',
        'tab:raw-saturation-stage',
        ['Source', '$n$', 'Old ms', 'New ms', 'Paired ratio', 'A/A'],
        stage_rows, 'lrrrrr'))

    pipeline_rows = []
    for row in data['pipeline']['rows']:
        pipeline_rows.append([
            tex_name(row['name']), number(row['median_seconds']['baseline'], 1000),
            number(row['median_seconds']['saturation'], 1000),
            number(row['paired_ratios']['saturation']), number(row['paired_ratios']['control']),
        ])
    tables.append(table(
        'All full-pipeline inputs, with the ordinary preceding filters, a one-second global allowance, '
        'and a 0.15-second group-stage allowance. Gordian is resource-limited in every arm. '
        'Earlier-filter controls do not exercise the new planner. Five measured rounds follow one excluded warmup.',
        'tab:raw-saturation-pipeline',
        ['Source', 'Old ms', 'New ms', 'Paired ratio', 'A/A'],
        pipeline_rows, 'lrrrr'))

    guard_rows = [[tex_name(row['name']), f"{row['baseline_work']:,}",
                   f"{row['initial_saturation_work']:,}", f"{row['final_saturation_work']:,}"]
                  for row in summary['guard_work_comparison']]
    tables.append(table(
        'Deterministic producer work before and after moving the exact first-firing guard '
        'ahead of incidence construction. All initial/final audit outcomes and certificates agree. '
        'These are cooperative work counts, not bit-operation counts or wall-time ratios.',
        'tab:raw-saturation-guard',
        ['Source', 'Baseline', 'Initial probe', 'Final probe'], guard_rows, 'lrrr'))
    (RESULTS/'raw_saturation_tables.tex').write_text('\n'.join(tables))
    print(json.dumps({mode: {k: v for k, v in info.items() if k not in ('rows', 'reasons')}
                      for mode, info in summary['modes'].items()}, indent=2))


if __name__ == '__main__':
    main()
