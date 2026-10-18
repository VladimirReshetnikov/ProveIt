import os,sys,importlib.util,collections
from pathlib import Path
from functools import cache
repo=Path('ProveIt').resolve()
base=repo/'lib/jeff-busy-beaver-zfc254/ZF/m254'
os.environ['PROVEIT_ZFC254_ROOT']=str(base)
p=repo/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/09-decoder-decoder-search-dag_tools.py'
s=importlib.util.spec_from_file_location('dag_tools',p);d=importlib.util.module_from_spec(s);s.loader.exec_module(d)
@cache
def norm(e):
 if e[0]!='N':return e
 a,b=norm(e[1]),norm(e[2])
 if d.closed(e[1]) and d.closed(e[2]):
  word=(*(a[1:] if a[0]=='S' else (a,)),*(b[1:] if b[0]=='S' else (b,)))
  out=[];inc=[]
  for v in word+(('end',),):
   if v[0]=='I':inc.append(v);continue
   if inc:out+=sorted(inc);inc=[]
   if v!=('end',):out.append(v)
  return ('S',*out)
 return ('N',a,b)
native,names=d.read_dag254();nt=d.unfold(native);pn=d.read_p254();pt=d.unfold(pn)
print('whole norms equal:',norm(nt)==norm(pt))
wnt=d.unfold(native,218);wn=norm(wnt)
print('wn atoms:',len(wn)-1)
patterns=[]
for q in (171,216,217,162,212,116,120,117,160,119,177,218):
 u=norm(d.unfold(native,q));patterns.append((q,u));print(q,names[q], 'norm',u[0],len(u)-1 if u[0]=='S' else 'atom')
for label,t in [('native',nt),('optimized',pt)]:
 u=norm(t);seqs=[]
 def collect(e):
  if e[0]=='S':seqs.append(e[1:]);[collect(x) for x in e[1:]]
  elif e[0]=='N':collect(e[1]);collect(e[2])
 collect(u)
 c=collections.Counter()
 for word in seqs:
  for q,pat in patterns:
   ps=pat[1:] if pat[0]=='S' else (pat,)
   for i in range(len(word)-len(ps)+1):
    if word[i:i+len(ps)]==ps:c[q]+=1
 print(label,'sequences',len(seqs),'maxlen',max(map(len,seqs)),'pattern counts',dict(c))
