#!/usr/bin/env python3
from pathlib import Path
import json
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def tex(s):
    replacements={'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}','→':r'$\to$','≤':r'$\le$','≥':r'$\ge$','−':'-','–':'--','—':'---','Γ':r'$\Gamma$'}
    return ''.join(replacements.get(c,c)for c in s)
def name(s):return tex(s).replace(r'\_',r'\_\allowbreak ').replace('-',r'-\allowbreak ')
front=json.loads((ROOT/'comparison/frontier194.json').read_text())['classes']
rows=[r'\small',r'\setlength{\tabcolsep}{3pt}',r'\begin{longtable}{@{}p{3.3cm}p{1.3cm}p{1.9cm}p{9.1cm}@{}}',r'\toprule Name & Status & Class & Distinguishing change\\\midrule\endfirsthead',r'\toprule Name & Status & Class & Distinguishing change\\\midrule\endhead',r'\bottomrule\endfoot']
for x in sorted(front,key=lambda x:({'reported':0,'auxiliary':1,'rejected':2}[x['status']],x['name'])):
 rows.append(name(x['name'])+' & '+{'reported':'R','auxiliary':'A','rejected':'X'}[x['status']]+' & '+r'\texttt{'+x['graph_hash'][:10]+'} & '+tex(x['change'])+r'\\[4pt]')
rows.extend([r'\end{longtable}',r'\normalsize']);(HERE/'frontier_table.tex').write_text('\n'.join(rows)+'\n')
packets=json.loads((ROOT/'comparison/packet_ledger_61.json').read_text())['packets']
rows=[r'\small',r'\setlength{\tabcolsep}{3pt}',r'\begin{longtable}{@{}p{4.5cm}p{11.1cm}@{}}',r'\toprule Packet & Contribution and duplication\\\midrule\endfirsthead',r'\toprule Packet & Contribution and duplication\\\midrule\endhead',r'\bottomrule\endfoot']
for i,x in enumerate(packets,1):
 desc=x['contribution']+(' '+x['duplicate_note'] if x['duplicate_note'] else '')
 rows.append(str(i)+'. '+name(x['packet'])+' ('+('incoming' if x['location']=='incoming' else 'filed')+') & '+tex(desc)+r'\\[5pt]')
rows.extend([r'\end{longtable}',r'\normalsize']);(HERE/'packet_table.tex').write_text('\n'.join(rows)+'\n')
print('Generated 49 frontier rows and 61 packet rows')
