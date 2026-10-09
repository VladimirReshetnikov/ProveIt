"""Embed measured tables in the standalone LaTeX source; no invented values."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]

def table(header, columns, rows, caption, label):
    out=[r'\begin{table}[htbp]',r'\centering\small',r'\begin{tabular}{@{}'+columns+r'@{}}',r'\toprule',
         header+r'\\',r'\midrule']
    out += [' & '.join(row)+r'\\' for row in rows]
    out += [r'\bottomrule',r'\end{tabular}',r'\caption{'+caption+'}',r'\label{'+label+'}',r'\end{table}']
    return '\n'.join(out)

def main():
    bench=json.loads((ROOT/'results/benchmark.json').read_text())
    audit=json.loads((ROOT/'results/audit.json').read_text())
    rows=[]
    for r in bench['rows']:
        med=r['median_seconds']
        rows.append([str(r['k']),f"{r['expanded_crossings']:,}",str(r['input_rules']),
                     f"{med['compressed_and_replay']*1000:.3f}",f"{med['expand_and_stack']*1000:.3f}",
                     f"{r['baseline_over_compressed']:.2f}"])
    texts=[table(r'$k$ & Crossings $N_k$ & Input rules & New (ms) & Baseline (ms) & Ratio',
                 'rrrrrr',rows,'Paired native-input comparison on the positive sleeve family. New includes discovery and independent replay; baseline includes expansion and the source-derived stack control. Ratios below one favor the baseline.','tab:benchmark')]
    rows=[]
    for r in audit['capacity']:
        rows.append(['Knotted' if r['negative'] else 'Unknot',str(r['k']),str(r['input_rules']),
                     str(r['stats']['arena_nodes']),f"{r['discovery_seconds']*1000:.3f}",
                     f"{r['verification_seconds']*1000:.3f}"])
    texts.append(table('Core type & $k$ & Input rules & String rules & Produce (ms) & Replay (ms)',
                        'lrrrrr',rows,'Completed expansion-forbidden capacity checks. Times are single-run observations, not paired benchmark medians. The absence of a huge expanded baseline is not a speed measurement.','tab:capacity'))
    rows=[]
    for r in audit['forests']:
        rows.append([str(r['strands']),str(r['factors']),str(r['k']),str(r['input_rules']),
                     'Unknot' if r['status']=='UNKNOT' else 'Knotted',
                     f"{r['discovery_seconds']+r['verification_seconds']:.3f}"])
    texts.append(table('Strands & Leaves & $k$ & Input rules & Verdict & Total (s)',
                        'rrrrlr',rows,'Native singleton-forest capacity checks, including replay. Each leaf is a compressed three-braid sleeve; the negative case has one figure-eight core.','tab:forests'))
    article=ROOT/'paper/article.tex'
    text=article.read_text()
    begin='% BEGIN GENERATED TABLES';end='% END GENERATED TABLES'
    before,tail=text.split(begin,1);_,after=tail.split(end,1)
    article.write_text(before+begin+'\n'+'\n\n'.join(texts)+'\n'+end+after)
    print('Updated tables from completed results.')

if __name__=='__main__':main()
