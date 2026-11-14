from pathlib import Path
import json,collections
HERE=Path(__file__).resolve().parent;ROOT=HERE.parent

def esc(s):
 return ''.join({'\\':r'\textbackslash{}','&':r'\&','%':r'\%','$':r'\$','#':r'\#','_':r'\_','{':r'\{','}':r'\}','~':r'\textasciitilde{}','^':r'\textasciicircum{}'}.get(c,c) for c in str(s))

rows=json.loads((ROOT/'comparison/principal_designs40.json').read_text())
out=[r'\small',r'\begin{longtable}{@{}p{4.15cm}ccccccc@{}}',r'\toprule',r'Design & $r$ & Q & $\Gamma$ & AX & MP & Halt & Sym.\\',r'\midrule\endfirsthead',r'\toprule Design & $r$ & Q & $\Gamma$ & AX & MP & Halt & Sym.\\\midrule\endhead',r'\bottomrule\endfoot']
for e in rows:
 mp='P' if 'dummy' in e['MP_success']else('C'if'cached'in e['MP_success']else'N')
 out.append(esc(e['name'])+' & '+' & '.join(map(str,[e['constructor_coefficient'],'yes'if e['quantifier_distribution']!='original'else'--','D'if e['diagonal_seed']=='Gamma(D)'else'A',e['AX_stack_prefix_length'],mp,'sum'if'sum'in e['Shift_halt_guard']else'cache','yes'if e['Shift_comparator']=='symmetric'else'--']))+r'\\')
out+= [r'\midrule\textbf{New AX11QH} & 4 & yes & A & 11 & N & cache & --\\',r'\end{longtable}',r'\normalsize']
(HERE/'principal_table.tex').write_text('\n'.join(out)+'\n')
front=[e for e in json.loads((ROOT/'comparison/results/frontier_annotated.json').read_text())if e['states']==194 and e['spanning']]
assert len(front)==82
cats=collections.Counter(e['evidence_category']for e in front);print('categories',cats)
out=[r'\small\begin{longtable}{@{}p{2.3cm}p{7.8cm}p{2.25cm}@{}}',r'\toprule Graph prefix & Reported name or role & Evidence\\\midrule\endfirsthead',r'\toprule Graph prefix & Reported name or role & Evidence\\\midrule\endhead',r'\bottomrule\endfoot']
for e in sorted(front,key=lambda x:(x['evidence_category'],x.get('name',''),x['strict_graph'])):
 n=e.get('name')or'equivalent stored representative'; cat={'reported principal construction':'P','supplementary construction':'S','source-validated research rotation':'V','research auxiliary':'A','rejected':'R'}[e['evidence_category']]
 out.append(r'\texttt{'+e['strict_graph'][:12]+'} & '+esc(n)+' & '+esc(cat)+r'\\')
out += [r'\end{longtable}\normalsize']
(HERE/'frontier_table.tex').write_text('\n'.join(out)+'\n')
r={}
for l in (ROOT/'candidate/machine/machine.tm').read_text().splitlines():
 q,b,w,d,n=l.split();r[int(q),int(b)]=(w,d,n)
def action(q,b):
 w,d,n=r[q,b];return '$'+w+r'\mathrm{'+d+'}'+('H'if n=='194'else n)+'$'
out=[r'\small\begin{longtable}{@{}rcc@{\hspace{1.6cm}}rcc@{}}',r'\toprule $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\\midrule\endfirsthead',r'\toprule $q$ & Read 0 & Read 1 & $q$ & Read 0 & Read 1\\\midrule\endhead',r'\bottomrule\endfoot']
for i in range(97):out.append(f'{i} & {action(i,0)} & {action(i,1)} & {i+97} & {action(i+97,0)} & {action(i+97,1)}'+r'\\')
out +=[r'\end{longtable}\normalsize']
(HERE/'transition_table.tex').write_text('\n'.join(out)+'\n')
