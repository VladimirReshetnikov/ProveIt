import sys,json
from pathlib import Path
BASE=(Path(__file__).resolve().parent/'data/k219')
PARENT=(Path(__file__).resolve().parent/'support/k221')
sys.path.insert(0,str(PARENT/'portable'))
import source_language as s,build221 as b
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes()); TREE=s.tree(json.loads((BASE/'machine/sites219.json').read_text()))
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
hits=[tup(x)for x in json.loads((BASE/'research/encoding/eq_clean_hits.json').read_text())]
for i,t in enumerate(hits):
 print(i,s.metrics(t),'rightCD',[(p,op,k)for p,op,k in s.sites(t)if p.endswith('1')and op=='CD'],repr(t))
G,P=b.decoder_map(T,TREE)
unique={}
def vis(n,path=''):
 if s.leaf(n):return
 unique.setdefault(n,[]).append(path);vis(n[0],path+'0');vis(n[1],path+'1')
vis(hits[10])
for n,ps in unique.items():
 states=[q for q,ns in G.items()if n in ns]
 print('node',ps,'states',states,'multiplicities',[(q,len(P[q]),len(G[q]))for q in states])
def repl(n,old,new):return new if n==old else n if s.leaf(n)else(repl(n[0],old,new),repl(n[1],old,new))
def swap(n):return(n[0],11-n[1])if s.leaf(n)and n[0]in('CI','CD')and n[1]in(5,6)else n if s.leaf(n)else(swap(n[0]),swap(n[1]))
for i,h in enumerate(hits):
 for reflected in[False,True]:
  n=swap(h)if reflected else h;tr=repl(TREE,hits[10],n);print('whole',i,reflected,s.metrics(tr))
