#!/usr/bin/env python3
"""Generate the printed transition table and complete comparison appendices."""
from pathlib import Path
import csv
import math

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def escape(text):
    replacements = {'\\':r'\textbackslash{}','&':r'\&','%':r'\%',
                    '$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}',
                    '~':r'\textasciitilde{}','^':r'\textasciicircum{}'}
    return ''.join(replacements.get(c,c) for c in text.replace('`',''))

def main():
    table = {}
    for line in (ROOT/'machines/PA194HS/machine.tm').read_text().splitlines():
        q,b,w,d,t = line.split()
        table[int(q),int(b)] = w+d+t
    assert set(table)=={(q,b) for q in range(194) for b in (0,1)}
    lines=[r'\begingroup\footnotesize\setlength{\tabcolsep}{4pt}',
           r'\renewcommand{\arraystretch}{1.02}',r'\begin{center}',
           r'\begin{tabular}{@{}rll@{\hspace{12pt}}rll@{\hspace{12pt}}rll@{\hspace{12pt}}rll@{}}',
           r'\toprule', r'$q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\\midrule']
    for i in range(49):
        cells=[]
        for group in range(4):
            q=i+49*group
            cells.extend([str(q),r'\texttt{'+table[q,0]+'}',r'\texttt{'+table[q,1]+'}'] if q<194 else ['','',''])
        lines.append(' & '.join(cells)+r'\\')
    lines.extend([r'\bottomrule\end{tabular}',r'\end{center}\endgroup'])
    (HERE/'transition_table.tex').write_text('\n'.join(lines)+'\n')

    packets=list(csv.DictReader((ROOT/'comparison/packet_ledger.csv').open()))
    assert len(packets)==46
    lines=[r'\begingroup\small',r'\begin{longtable}{@{}p{.37\linewidth}p{.59\linewidth}@{}}',
           r'\toprule Packet & Contribution and stated outcome\\\midrule\endhead']
    for i,row in enumerate(packets,1):
        name=str(i)+'. '+r'\nolinkurl{'+row['packet']+'}'
        if row['location']=='incoming':name+=r'\newline\emph{Incoming}'
        lines.append(name+' & '+escape(row['claimed_contribution'])+r'\\[4pt]')
    lines.extend([r'\bottomrule\end{longtable}\endgroup'])
    (HERE/'packet_ledger.tex').write_text('\n'.join(lines)+'\n')

    frontier=list(csv.DictReader((ROOT/'comparison/frontier194.csv').open()))
    assert len(frontier)==28
    status={'principal/companion':'Principal/companion','research/supplementary':'Research/supplement',
            'rejected':'Rejected'}
    lines=[r'\begingroup\small',r'\begin{longtable}{@{}p{.49\linewidth}p{.29\linewidth}rr@{}}',
           r'\toprule Class & Supplied role & Forms & Copies\\\midrule\endhead']
    for row in frontier:
        lines.append(escape(row['name'])+' & '+status[row['status']]+' & '+row['byte_forms']+' & '+row['occurrences']+r'\\[3pt]')
    lines.extend([r'\bottomrule\end{longtable}\endgroup',
                  r'\emph{Forms} counts distinct complete file byte forms; \emph{Copies} counts recognized occurrences.'])
    (HERE/'frontier194.tex').write_text('\n'.join(lines)+'\n')
    print('Generated the exact 194-state table, 46-packet ledger and 28-class frontier.')

if __name__=='__main__':main()
