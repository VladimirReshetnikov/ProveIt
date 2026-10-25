#!/usr/bin/env python3
"""Render complete monic row-to-coordinate pivot tables."""
from pathlib import Path
import json,argparse
ROOT=Path(__file__).resolve().parent

def contents():
    results=json.loads((ROOT/'RESULTS.json').read_text())
    parts=[r'''\section{Complete monic-elimination pivot tables}
\label{app:monic-pivots}

Every entry $j\mapsto v$ selects the source residual $R_j$ and source
coordinate $x_v$ of the printed $248$-variable equation.  Both indices are
zero based: $0\le j<182$ and $0\le v<248$.  Write the selected row uniquely
as $R_j=\varepsilon_vx_v+f_v$ with $\varepsilon_v=\pm1$, and replace
$x_v$ by $-\varepsilon_vf_v$.  The substitution dependency graph is acyclic;
apply the definitions recursively, evaluating dependencies before their
users (a reverse topological order for the graph defined in the theorem). Retain, in
increasing source-index order, every coordinate not selected as a target.
The new polynomial is the sum of the squares of all unselected residuals
after these substitutions.  Thus these finite tables and the complete
source residual list specify all eight polynomials without a search rule
or unspecified compiler choice.  The machine-readable certificates and
literal polynomial DAGs supply the same definitions independently.

''']
    tsv=['profile\tsource_row\teliminated_coordinate']
    for r in results:
        name=r['name'];c=json.loads((ROOT/'certificates'/f'{name}.json').read_text())
        pairs=sorted((s['row'],s['variable']) for s in c['steps'])
        for row,var in pairs:tsv.append(f'{name}\t{row}\t{var}')
        parts.append('\\subsection{'+str(r['variables'])+' integer variables, degree '+format(r['degree'],',')+'}\n')
        parts.append(f"There are ${len(pairs)}$ selected coordinates and ${r['residuals']}$ remaining residuals.\n")
        parts.append(r'''\begingroup
\small
\setlength{\tabcolsep}{4pt}
\begin{longtable}{*{6}{r@{\,$\mapsto$\,}r}}
\hline
\multicolumn{12}{c}{Source residual $j$ $\mapsto$ eliminated coordinate $v$}\\
\hline
\endfirsthead
\hline
\multicolumn{12}{c}{Source residual $j$ $\mapsto$ eliminated coordinate $v$ (continued)}\\
\hline
\endhead
''')
        for first in range(0,len(pairs),6):
            row=pairs[first:first+6]
            cells=[]
            for a,b in row:cells.extend((str(a),str(b)))
            for _ in range(6-len(row)):cells.append(r'\multicolumn{2}{c}{}')
            parts.append(' & '.join(cells)+r' \\'+'\n')
        parts.append(r'''\hline
\end{longtable}
\endgroup

''')
    return ''.join(parts),'\n'.join(tsv)+'\n'

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true');a=ap.parse_args()
    tex,tsv=contents()
    for name,data in [('pivot_appendix.tex',tex),('PIVOT_TABLES.tsv',tsv)]:
        p=ROOT/name
        if a.check:
            if p.read_text()!=data:raise ValueError('Printed pivot table mismatch: '+name)
        else:p.write_text(data)
    print(json.dumps({'status':'PASS','complete_pivot_tables':8}))

if __name__=='__main__':main()
