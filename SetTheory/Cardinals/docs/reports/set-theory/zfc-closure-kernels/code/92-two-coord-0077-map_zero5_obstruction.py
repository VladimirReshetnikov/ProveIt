from pathlib import Path
exec((Path(__file__).resolve().parent / 'audit_search_outputs.py').read_text().split('all_results=[]')[0])
g={q:(a,b) for q,a,b in json.loads((OUT/'zero5-feasibility-best.json').read_text())['rules']};ba={int(i):names[int(q)] for q,i in source['sequence_ast_roots'].items()}
@functools.cache
def a(i):
 if i in ba:return w(ba[i])
 r=source['ast_dag'][i]
 return ('L',tuple(r[1])) if r[0]=='L' else ('N',a(r[1]),a(r[2]),('ast',i))
@functools.cache
def w(q):
 if len(q)==1:return a(source['atoms'][symbols[q]]['ast'])
 l,r=g.get(q,old.get(q));return('N',w(l),w(r),('word',q))
def walk(t,p='',trace=()):
 if t[0]=='L':
  if len(p)-len(p.rstrip('0'))>=6:
   print('BAD',p,t[1]);print(trace[-7:])
  return
 walk(t[1],p+'0',trace+(t[3],));walk(t[2],p+'1',trace+(t[3],))
walk(a(source['original_ast']))
