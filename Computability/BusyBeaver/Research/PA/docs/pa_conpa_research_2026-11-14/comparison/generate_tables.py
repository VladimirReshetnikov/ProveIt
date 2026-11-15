#!/usr/bin/env python3
"""Generate complete comparison appendices from the frozen exact ledgers."""
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
def tex(s):
    m={'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_\allowbreak ','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}'}
    return ''.join(m.get(c,c) for c in s)

def main():
    classes=json.loads((HERE/'comparison194_complete.json').read_text())
    packets=json.loads((HERE/'packet_ledger86.json').read_text())
    codes={'reported principal construction':'P','supplementary construction':'S','research auxiliary':'A','research seed':'U','rejected':'R','diagnostic control':'D'}
    out=[r'\section{All recognized 194-state table classes}',r'\label{app:comparison-classes}',
         r'This is a table inventory, not a list of independently proved consistency theorems. P denotes a reported principal construction; S a supplementary construction; A a research auxiliary; U a research seed; R a rejected construction; and D a disconnected diagnostic. Short identifiers below are prefixes of the exact table-class SHA-256 values. Complete identifiers, paths, file digests, and historical evidence scopes appear in \texttt{comparison194\_complete.csv}.',
         r'\begingroup\small\setlength{\tabcolsep}{3pt}\renewcommand{\arraystretch}{1.07}',
         r'\begin{longtable}{p{0.12\linewidth}p{0.25\linewidth}p{0.07\linewidth}p{0.45\linewidth}}',
         r'\caption{All 111 recognized historical classes at the pinned revision.}\label{tab:comparison-all-classes}\\',
         r'\toprule Class & Name & Type & Mechanism or evidence boundary \\ \midrule\endfirsthead',
         r'\multicolumn{4}{l}{\emph{Table \thetable{} continued}}\\',
         r'\toprule Class & Name & Type & Mechanism or evidence boundary \\ \midrule\endhead',
         r'\bottomrule\endfoot']
    for r in classes:
        out.append(r'\texttt{'+r['table_class'][:8]+'} & '+tex(r['historical_name'])+' & '+codes[r['historical_evidence']]+' & '+tex(r['mechanism'])+r' \\ \addlinespace[2pt]')
    out.extend([r'\end{longtable}',r'\endgroup'])
    (HERE/'frontier_table.tex').write_text('\n'.join(out)+'\n')
    out=[r'\section{Every delivery in the comparison}',r'\label{app:comparison-packets}',
         r'The 86 rows below consist of 82 filed deliveries and four current incoming ZIP payloads. Repeated names can identify distinct deliveries. In particular, the current incoming AX11H archive changes the proof claim while retaining the two existing principal transition tables. Descriptions attribute the respective packet claims; they are not blanket endorsements. The exact repository/member mapping is in \texttt{packet\_ledger86.csv}.',
         r'\begingroup\small\setlength{\tabcolsep}{3pt}\renewcommand{\arraystretch}{1.07}',
         r'\begin{longtable}{p{0.05\linewidth}p{0.37\linewidth}p{0.47\linewidth}}',
         r'\caption{All 86 delivery payloads at the pinned revision.}\label{tab:comparison-all-packets}\\',
         r'\toprule No. & Packet & Reported contribution \\ \midrule\endfirsthead',
         r'\multicolumn{3}{l}{\emph{Table \thetable{} continued}}\\',
         r'\toprule No. & Packet & Reported contribution \\ \midrule\endhead',
         r'\bottomrule\endfoot']
    for i,r in enumerate(packets,1):
        desc=r['reported_content']+(' [Current incoming ZIP.]' if r['delivery_scope']=='current incoming' else '')
        out.append(str(i)+' & '+r'\texttt{'+tex(r['packet'])+'} & '+tex(desc)+r' \\ \addlinespace[2pt]')
    out.extend([r'\end{longtable}',r'\endgroup'])
    (HERE/'packet_table.tex').write_text('\n'.join(out)+'\n')
    print('Generated',len(classes),'class rows and',len(packets),'packet rows.')
if __name__=='__main__':main()
