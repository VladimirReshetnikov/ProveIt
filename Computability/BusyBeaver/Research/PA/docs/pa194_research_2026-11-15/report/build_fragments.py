#!/usr/bin/env python3
"""Regenerate data-bound report appendices; Python standard library only."""
from pathlib import Path
import csv, hashlib, json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

def tex(s):
    mapping = {'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$',
               '#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}'}
    return ''.join(mapping.get(c,c) for c in str(s)).replace('/',r'/\allowbreak{}')

def write(name, s):
    (HERE/name).write_text(s, encoding='utf-8')

def main():
    specs=json.loads((ROOT/'inputs/specifications.json').read_text())
    out=[r'\paragraph{Byte identities.} SHA-256 is computed over each complete delivered dense table, including its final newline.']
    for s in specs:
        p=ROOT/'machines'/s['name']/'machine.tm'
        out += [r'\noindent\file{'+s['name']+r'}\par',
                r'{\small\file{'+hashlib.sha256(p.read_bytes()).hexdigest()+r'}}\par']
    write('identities.tex','\n'.join(out)+'\n')

    out=[]
    for sn,s in enumerate(specs):
        if sn:out.append(r'\clearpage')
        out += [r'\subsection{\texorpdfstring{\file{'+s['name']+r'}}{'+tex(s['name'])+r'}}',
                r'\begingroup\fontsize{8.4}{9.6}\selectfont\ttfamily',
                r'\setlength{\tabcolsep}{4pt}\renewcommand{\arraystretch}{1.0}',
                r'\begin{center}\begin{tabular}{rrr@{\hspace{13pt}}rrr@{\hspace{13pt}}rrr@{\hspace{13pt}}rrr}',
                r'\toprule q&read 0&read 1&q&read 0&read 1&q&read 0&read 1&q&read 0&read 1\\\midrule']
        T={}
        for line in (ROOT/'machines'/s['name']/'machine.tm').read_text().splitlines():
            q,b,w,d,n=line.split(); T[int(q),int(b)]=w+d+('H' if n=='194' else n)
        for k in range(49):
            cells=[]
            for block in range(4):
                q=49*block+k
                cells += [str(q),T[q,0],T[q,1]] if q<194 else ['','','']
            out.append('&'.join(cells)+r'\\')
        out += [r'\bottomrule\end{tabular}\end{center}\endgroup']
    write('transition_tables.tex','\n'.join(out)+'\n')

    families=json.loads((ROOT/'comparison/families32.json').read_text())
    out=[r'\begingroup\small\setlength{\tabcolsep}{3pt}',
         r'\begin{longtable}{>{\raggedright\arraybackslash}p{0.21\linewidth}>{\raggedright\arraybackslash}p{0.31\linewidth}>{\raggedright\arraybackslash}p{0.41\linewidth}}',
         r'\caption{All 32 inherited mechanism families. The last column summarizes the recurring change and its mathematical obligation; full physical descriptions are in the CSV ledger.}\\',
         r'\toprule Family&Named designs&Change and proof obligation\\\midrule\endfirsthead',
         r'\toprule Family&Named designs&Change and proof obligation\\\midrule\endhead',r'\bottomrule\endfoot']
    for x in families:
        designs=tex(x['designs'])
        out.append(tex(x['family'])+'&'+designs+'&'+tex(x['recurring_behavior']+' '+x['proof_obligation'])+r'\\[5pt]')
    out += [r'\end{longtable}\endgroup']
    write('families.tex','\n'.join(out)+'\n')

    named=json.loads((ROOT/'comparison/named_designs91.json').read_text())
    out=[r'The following 91 rows name distinct inherited graph classes, with aliases grouped. These are attributed proposals with different strengths of evidence; the ledger does not certify 91 separate absolute iPRA theorems. Full identities, source locators and proof-status fields are in \file{comparison/named_designs91.csv}.',
         r'\begingroup\small\setlength{\tabcolsep}{3pt}',
         r'\begin{longtable}{>{\raggedright\arraybackslash}p{0.23\linewidth}>{\raggedright\arraybackslash}p{0.24\linewidth}>{\raggedright\arraybackslash}p{0.46\linewidth}}',
         r'\toprule Name or alias group&Family&Distinguishing mechanism\\\midrule\endfirsthead',
         r'\toprule Name or alias group&Family&Distinguishing mechanism\\\midrule\endhead',r'\bottomrule\endfoot']
    for x in named:
        mechanism=x['mechanism']
        for a,b in {'native26':'native 26','and101':'and 101',
                    'all3673':'all 3,673','Native139':'Native 139',
                    ';305primitive addresses,61constructor loops,all3671AX11Hsource':'; 305 primitive addresses, 61 constructor loops, all 3,671 AX11H source',
                    'positions[':'positions [','];changes':']; changes',
                    'initialization48320':'initialization 48,320',
                    'native190':'native 190','read1':'read 1'}.items():
            mechanism=mechanism.replace(a,b)
        out.append(tex(x['name'])+'&'+tex(x['family'])+'&'+tex(mechanism)+r'\\[5pt]')
    out += [r'\end{longtable}\endgroup']
    write('named_designs.tex','\n'.join(out)+'\n')

    results=json.loads((ROOT/'research/physical_searches/SUMMARY.json').read_text())['results']
    out=[r'All the following recorded physical searches ended with empty accepted-hit sets. Counts describe concrete finite search spaces, not lower bounds.',
         r'\begingroup\small\setlength{\tabcolsep}{3pt}',
         r'\begin{longtable}{>{\raggedright\arraybackslash}p{0.26\linewidth}>{\raggedright\arraybackslash}p{0.39\linewidth}r}',
         r'\toprule Input&Search template&Candidate count\\\midrule\endfirsthead',
         r'\toprule Input&Search template&Candidate count\\\midrule\endhead',r'\bottomrule\endfoot']
    desc={'one_row_receipt':'Shared-row pair; arbitrary other row',
          'whole_instruction_receipt':'Pair; rows chosen from originals',
          'incoming_thread_receipt':'Delete reader; rethread incoming edges',
          'joint_pairs_radius6_160':'Arbitrary two-row local quotient'}
    for r in results:
        name='Primary PA194' if r['input']=='pa194_reduce' else r['input']
        n=r.get('candidates',r.get('candidate_actions',r.get('row_trials',0)))
        out.append(tex(name)+'&'+tex(desc.get(r['suite'],r['suite']))+'&'+f'{n:,}'+r'\\[3pt]')
    out += [r'\end{longtable}\endgroup',
            r'For the arbitrary two-row local quotients, the count is row-action trials, not complete machines. Each 194-state input has 18,721 unordered control pairs; each 195-state input has 18,915. Radius-six blank-window abstraction and a 160-step detour cap define the local search. Joint choices and precise exclusions are retained in \file{research/physical_searches/SUMMARY.json}. The complete-instruction screens use symbolic register frames and their specified arithmetic-box exclusions; they are a different acceptance criterion.']
    write('search_summary.tex','\n'.join(out)+'\n')

if __name__=='__main__':main()
