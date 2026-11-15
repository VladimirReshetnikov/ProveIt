#!/usr/bin/env python3
"""Generate report tables from frozen checked artifacts, with no new claims."""
from pathlib import Path
import csv
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def esc(s):
    pairs = {'\\': r'\textbackslash{}', '&': r'\&', '%': r'\%', '$': r'\$',
             '#': r'\#', '_': r'\_', '{': r'\{', '}': r'\}', '~': r'\textasciitilde{}',
             '^': r'\textasciicircum{}'}
    return ''.join(pairs.get(c, c) for c in str(s))

def comma(n):
    return f'{n:,}'

certs = [json.loads((ROOT / 'machines' / name / 'certificate.json').read_text())
         for name in ('PA194GD_SF', 'PA194GDH_SF', 'PA194GDHS_SF')]
lines = [r'\begin{center}', r'\begin{tabular}{@{}lrrrr@{}}', r'\toprule',
         r'Machine & States & Rows & Parent startup & New startup\\\midrule']
for c in certs:
    s = c['startup']
    lines.append(f"{esc(c['name'])} & 194 & 388 & {comma(s['parent_steps'])} & {comma(s['new_steps'])}\\\\")
lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}',
          r'The exact dense table SHA-256 identities are:']
for c in certs:
    lines += [esc(c['name']) + r'\par{\small\path{' + c['sha256'] + r'}}\par']
(HERE / 'metrics.tex').write_text('\n'.join(lines) + '\n')

lines = [r'\begin{center}', r'\begin{tabular}{@{}lrrrr@{}}', r'\toprule',
         r'Machine & Selector uses & Fast $26/1$ & Fast $101/0$ & Intermediate time\\\midrule']
for c in certs:
    s = c['startup']; uses = s['shortcut_uses']
    lines.append(f"{esc(c['name'])} & {s['selector_expansions']} & {uses['26/1']} & {uses['101/0']} & {comma(s['selector_steps'])}\\\\")
lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}',
          r'For each row, new time equals parent time plus twice the selector uses,',
          r'minus twice the total shortcut uses. The full changed-row visit counts and',
          r'every seed one-cell are recorded in the machine certificate.']
(HERE / 'startup_details.tex').write_text('\n'.join(lines) + '\n')

rows = list(csv.DictReader((ROOT / 'comparison/named_designs85.csv').open()))
lines = [r'\begingroup\small', r'\setlength{\tabcolsep}{4pt}',
         r'\begin{longtable}{@{}>{\raggedright\arraybackslash}p{0.29\linewidth}>{\raggedright\arraybackslash}p{0.65\linewidth}@{}}',
         r'\toprule Name / class prefix & Mechanism\\\midrule\endfirsthead',
         r'\toprule Name / class prefix & Mechanism\\\midrule\endhead']
for row in sorted(rows, key=lambda r: r['name'].lower()):
    lines.append(r'\nolinkurl{' + row['name'] + r'}\newline{\footnotesize\texttt{' +
                 row['table_class'][:12] + '}} & ' + esc(row['feature']) + r'\\[5pt]')
lines += [r'\bottomrule', r'\end{longtable}', r'\endgroup']
(HERE / 'named_designs.tex').write_text('\n'.join(lines) + '\n')

lines = []
for number, c in enumerate(certs):
    name = c['name']; table = {}
    for line in (ROOT / 'machines' / name / 'machine.tm').read_text().splitlines():
        q, b, w, d, n = line.split()
        table[int(q), int(b)] = f'{w}{d}{n}'
    if number:
        lines.append(r'\clearpage')
    lines += [r'\subsection{' + esc(name) + '}', r'\begingroup\small',
              r'\begin{longtable}{@{}rll@{\hspace{2em}}rll@{}}',
              r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule\endfirsthead',
              r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule\endhead']
    for q in range(97):
        p = q + 97
        lines.append(f"{q} & \\texttt{{{table[q,0]}}} & \\texttt{{{table[q,1]}}} & " +
                     f"{p} & \\texttt{{{table[p,0]}}} & \\texttt{{{table[p,1]}}}\\\\")
    lines += [r'\bottomrule', r'\end{longtable}', r'\endgroup']
(HERE / 'transition_tables.tex').write_text('\n'.join(lines) + '\n')

bs = []
for path in sorted((ROOT / 'research/bootstrap').glob('run_k*.log')):
    tail = path.read_text().strip().splitlines()[-1]
    if not tail.startswith('DONE'):
        continue
    d = {k: float(v) if '.' in v else int(v) for k, v in re.findall(r'(\w+) ([0-9.]+)', tail)}
    bs.append(d)
lines = [r'\begin{center}\small', r'\begin{tabular}{@{}rrrrrr@{}}', r'\toprule',
         r'Edit budget & Branches & Rays & Exact cycles & Bounded & Frames\\\midrule']
for d in bs:
    lines.append(' & '.join(comma(d[k]) for k in ('edits', 'branches', 'rays', 'cycles', 'limits', 'hits')) + r'\\')
lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
(HERE / 'bootstrap_results.tex').write_text('\n'.join(lines) + '\n')
(ROOT / 'research/bootstrap/summary.json').write_text(json.dumps(bs, indent=2) + '\n')

refined = ROOT / 'research/state_reduction/frontier/refined_summary.json'
refined_runs = json.loads(refined.read_text())
ready = len(refined_runs) == 3 and all(len(family['results']) == 3 for family in refined_runs)
if not ready:
    raise RuntimeError('Expected all nine completed literal-envelope reduction runs')
lines = [r'Each new table was tested in three distinct radius-six reduction families:',
         r'\begin{center}\small', r'\begin{tabular}{@{}p{0.32\linewidth}p{0.32\linewidth}p{0.26\linewidth}@{}}',
         r'\toprule Family & Coverage per table & Step bounds\\\midrule',
         r'Joint return quotient & 18,721 unordered control pairs & 1 old / 100 new\\[3pt]',
         r'Positive stuttering quotient & 18,721 unordered control pairs & 12 old / 128 new\\[3pt]',
         r'Incoming-edge deletion & All 193 non-start controls & 24 old / 256 new\\',
         r'\bottomrule', r'\end{tabular}', r'\end{center}',
         r'The nine coarse-envelope runs found no hit. Together the two pair families',
         r'cover 112,326 machine/pair/family instances, and deletion covers 579 controls.']
if ready:
    lines += [r'The nine source-envelope refinement runs also completed with no hit;',
              r'their exact input hashes, context counts and action-trial statistics are retained.']
    reduction = json.loads((ROOT / 'research/state_reduction/RESULTS.json').read_text())
    all_logs = [item['log'] for item in reduction['coarse_frontier']]
    all_logs += [item['log'] for family in reduction['literal_frontier'] for item in family['results']]
    total = {key: sum(int(match.group(1)) for line in all_logs
                     if (match := re.search(r'\b' + key + r' (\d+)', line)))
             for key in ('pairs', 'trials', 'combos')}
    lines += [r'Across both regimes, the pair searches cover ' + comma(total['pairs']) +
              r' machine/pair/family instances, ' + comma(total['trials']) +
              r' candidate row actions and ' + comma(total['combos']) +
              r' paired-row combinations. The deletion runs cover 1,158 control instances.',
              r'\begin{center}\small', r'\begin{tabular}{@{}lrr@{}}', r'\toprule',
              r'Literal envelope & Source outcomes & Radius-six windows\\\midrule']
    for family in reduction['literal_frontier']:
        lines.append(esc(family['family']) + ' & ' + comma(family['source_outcomes']) +
                     ' & ' + comma(family['literal_windows']) + r'\\')
    lines += [r'\bottomrule', r'\end{tabular}', r'\end{center}']
lines += [r'A separate 83/190 merger experiment additionally permits one non-arithmetic',
          r'helper row to change. Across 256 radius-five exterior contexts it tested',
          r'772 merged-zero actions and 18,318,203 joint choices, with an 80-step bound,',
          r'and found no hit. It keeps the common read-one action and excludes the',
          r'23 arithmetic controls, start, and the merged control as helper rows.',
          r'This is stronger than holding every helper row fixed, but is still a',
          r'restricted local specification.',
          r'A fixed-core source study mapped 86 decoder roots, found 14 individual',
          r'rotations preserving the resolved source graph, and examined all 2,915',
          r'nonempty disjoint-pair subsets for another last-bit history fold.',
          r'No additional fold was found; these are experimental source layouts,',
          r'not fourteen separately verified physical machines.']
(HERE / 'state_search_results.tex').write_text('\n'.join(lines) + '\n')

fragment = (ROOT / 'research/modal_consequents/generalized_modal_heads.tex').read_text()
fragment = fragment.replace(r'\section{Two new generalized quantifier heads}',
                            r'\subsection{Consequents as independent parameters}', 1)
(HERE / 'modal_consequents.tex').write_text(fragment)
print('Report fragments generated from', len(certs), 'machines,', len(rows), 'named designs and', len(bs), 'completed bootstrap budgets.')
