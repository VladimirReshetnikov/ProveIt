from pathlib import Path
import csv,json,hashlib
R=Path(__file__).resolve().parents[1];O=R/'report'
def esc(s):
 return str(s).replace('\\',r'\textbackslash{}').replace('&',r'\&').replace('%',r'\%').replace('_',r'\_').replace('#',r'\#')
rs=[]
for name in ['PA194ORHF','PA194ORHBF']:
 p=R/'machines'/name;r=json.loads((p/'receipt.json').read_text());rs.append(r)
 rows={}
 for l in (p/'machine.tm').read_text().splitlines():
  q,b,w,d,n=l.split();rows[int(q),int(b)]=f'{w}{d}{n}'
 t=[r'\begin{longtable}{rll@{\hspace{10mm}}rll}',r'\toprule',r'State & Read 0 & Read 1 & State & Read 0 & Read 1\\',r'\midrule\endfirsthead',r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule\endhead',r'\bottomrule\endfoot']
 for q in range(97):t.append(' & '.join([str(q),rows[q,0],rows[q,1],str(q+97),rows[q+97,0],rows[q+97,1]])+r'\\')
 t.append(r'\end{longtable}');(O/(name+'_table.tex')).write_text('\n'.join(t)+'\n')
summary=[r'\begin{tabular}{lrr}',r'\toprule & PA194ORHF & PA194ORHBF\\\midrule',r'Working controls & 194 & 194\\',r'Transition rows & 388 & 388\\',r'Complete blank startup & '+str(rs[0]['startup']['steps'])+' & '+str(rs[1]['startup']['steps'])+r'\\',r'Changed rows from ORH & 2 & 6\\',r'Source instruction sites & 3,671 & 3,671\\',r'Source outcomes & 4,778 & 4,778\\',r'\bottomrule\end{tabular}']
(O/'summary_table.tex').write_text('\n'.join(summary)+'\n')
hashlines=[]
for r in rs:hashlines += [r'\paragraph{'+r['name']+r'.} Dense table SHA-256:',r'\begin{quote}\footnotesize\path{'+r['dense_sha256']+r'}\end{quote}']
(O/'hashes.tex').write_text('\n'.join(hashlines)+'\n')
with (R/'comparison/named_designs104.csv').open() as f: roster=list(csv.DictReader(f))
t=[r'\begingroup\footnotesize',r'\begin{longtable}{p{43mm}p{73mm}p{25mm}}',r'\toprule Design & Mechanism family & Class prefix\\\midrule\endfirsthead',r'\toprule Design & Mechanism family & Class prefix\\\midrule\endhead',r'\bottomrule\endfoot']
for r in roster:t.append(esc(r['name'])+' & '+esc(r['family'])+' & '+r'\texttt{'+r['table_class'][:12]+'}'+r'\\')
t += [r'\end{longtable}\endgroup'];(O/'roster.tex').write_text('\n'.join(t)+'\n')
# Include observed runtime receipts only after both checks finish.
rr=[]
for name in ['PA194ORHF','PA194ORHBF']:
 p=R/'machines'/name/'independent/receipt.json'
 if p.exists():rr.append(json.loads(p.read_text()))
if len(rr)==2:
 t=[r'\begin{tabular}{lrr}',r'\toprule Independent literal check & ORHF & ORHBF\\\midrule']
 for key,label in [('source_outcomes','Source outcomes'),('symbolic_steps','Symbolic events'),('maximum_symbolic_steps','Largest event count per outcome'),('minimum_positive_duration_constant','Minimum duration constant'),('list_lemmas_from_literal_table','Literal unary-list lemmas')]:
  t.append(label+' & '+f'{rr[0][key]:,}'+' & '+f'{rr[1][key]:,}'+r'\\')
 t+=[r'\bottomrule\end{tabular}'];(O/'literal_table.tex').write_text('\n'.join(t)+'\n')
else:(O/'literal_table.tex').write_text('Literal replay receipts pending.\n')
print('Generated tables, 104-design roster, hashes; literal receipts',len(rr))
