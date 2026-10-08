"""Embed recorded benchmark tables into a self-contained article.tex."""
from pathlib import Path
import json,statistics
ROOT=Path(__file__).resolve().parents[1]

def table(caption,label,columns,header,rows):
    body='\n'.join(' & '.join(map(str,row))+r' \\' for row in rows)
    return '\n'.join([r'\begin{table}[htbp]',r'\centering\small',r'\begin{tabular}{'+columns+'}',r'\toprule',
                     header+r' \\',r'\midrule',body,r'\bottomrule',r'\end{tabular}',
                     r'\caption{'+caption+'}',r'\label{'+label+'}',r'\end{table}'])

def main():
    text=(ROOT/'docs'/'article.template.tex').read_text()
    micro=json.loads((ROOT/'results'/'micro.json').read_text())['records']
    rows=[]
    for kind,b,cache in [('dense',4,'cold'),('dense',6,'cold'),('dense',8,'cold'),('dense',10,'cold'),
                         ('dense',6,'warm'),('dense',8,'warm'),('dense',10,'warm'),
                         ('near_equal',10,'cold'),('near_equal',10,'warm'),('sparse',10,'cold'),('sparse',10,'warm')]:
        vals=[statistics.median(r['seconds'] for r in micro if r['kind']==kind and r['variables']==b and r['cache']==cache and r['engine']==e)*1000 for e in ['baseline','adaptive']]
        rows.append([kind.replace('_',' '),b,cache,f'{vals[0]:.3f}',f'{vals[1]:.3f}',f'{vals[0]/vals[1]:.2f}'])
    text=text.replace('@@MICRO_TABLE@@',table('Composition microbenchmarks. Times are milliseconds; speedup is baseline/adaptive. Topology is precompiled, whole-result caches are bypassed, and sparse regressions are included.',
                  'tab:micro','lrcrrr','Input & $b$ & Memo & Baseline & Adaptive & Speedup',rows))
    def dense_median(engine, cache):
        return statistics.median(r['seconds'] for r in micro if r['kind']=='dense' and r['variables']==10 and r['cache']==cache and r['engine']==engine)*1000
    bc,ac,bw,aw=(dense_median(e,c) for e,c in [('baseline','cold'),('adaptive','cold'),('baseline','warm'),('adaptive','warm')])
    summary=(f'The dense ten-variable samples reduce the median cold composition time from {bc:.1f} milliseconds to {ac:.1f} milliseconds, a ratio of {bc/ac:.1f}. '
             f'The warmed baseline still visits every supported pair: its median is {bw:.1f} milliseconds, compared with {aw:.1f} milliseconds for the adaptive kernel, a ratio of {bw/aw:.1f}.')
    text=text.replace('@@MICRO_SUMMARY@@',summary)
    scans=json.loads((ROOT/'results'/'scans.json').read_text())['records'];rows=[]
    names={'trefoil':'Trefoil','figure_eight':'Figure-eight','hard_unknot_8':'Eight-crossing unknot',
           'conway':'Conway','kinoshita_terasaka':'Kinoshita--Terasaka','torus_3_5':'$T(3,5)$',
           'unknot_braid40':'Forty-crossing braid unknot','alternating_3_braid_10':'Alternating three-braid (10)'}
    for name,label in names.items():
        rs=[r for r in scans if r['case']==name];vals=[statistics.median(r['seconds'] for r in rs if r['engine']==e)*1000 for e in ['baseline','adaptive']]
        rr=next(r for r in rs if r['engine']=='adaptive')
        rows.append([label,rr['rank'],f'{vals[0]:.3f}',f'{vals[1]:.3f}',f'{vals[0]/vals[1]:.3f}'])
    text=text.replace('@@SCAN_TABLE@@',table('Raw scanning comparisons in the current-engine source-derived harness. Median milliseconds include the common order-selection routine; no preliminary recognition filters are used. All rank dictionaries agree.',
                  'tab:scans','lrrrr','Diagram & Rank & Baseline & Adaptive & Ratio',rows))
    data=json.loads((ROOT/'results'/'interfaces.json').read_text())['records'];rows=[]
    for n in [8,16,24]:
        rr=[r for r in data if r['size']==n]
        vals=[statistics.median(r[k] for r in rr)*1000 for k in ['full_schur','build_interface','evaluate_interface']]
        rows.append([n,f'{vals[0]:.3f}',f'{vals[1]:.3f}',f'{vals[2]:.3f}',f'{vals[0]/(vals[1]+vals[2]):.2f}'])
    text=text.replace('@@INTERFACE_TABLE@@',table('Structured block experiment over $R_3$, with supplied inner rank $r=2$ and $p=q=2$. Median milliseconds. Ratio compares the full Schur calculation with the sum of interface-building and evaluation medians.',
                  'tab:interface','rrrrr','$M$ & Full Schur & Build interface & Evaluate & Ratio',rows))
    data=json.loads((ROOT/'results'/'succinct.json').read_text());rows=[]
    for r in data:
        rows.append([r['modes'],f'$2^{{{r["modes"]}}}$',f'{r["median_seconds"]*1000:.3f}',r'$xy$'])
    text=text.replace('@@SUCCINCT_TABLE@@',table('Description-sized verification of the explicit complementary-support family. Nine repetitions; median milliseconds. The represented matrix is never expanded.',
                  'tab:succinct','rrrr','$m$ & Hidden generators & Verify & Schur result',rows))
    if '@@' in text: raise ValueError('unexpanded template marker')
    text=text.replace('where $A_0$ is an invertible $M$-by-$M$ matrix,',
                      'where $A_0$ now denotes an invertible background $M$-by-$M$ matrix (not necessarily the augmentation),')
    (ROOT/'docs'/'article.tex').write_text(text)

if __name__=='__main__':main()
