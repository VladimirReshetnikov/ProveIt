#!/usr/bin/env python3
"""Check layout, complete source graph, universal primitive contracts, and startup."""
if not __debug__:
    raise RuntimeError("Verification requires Python without -O or -OO.")

from pathlib import Path
import json,hashlib
import symbolic_runtime as s
from reconstruct import reconstruct
HERE=Path(__file__).resolve().parent

def source_graph(tree):
 sites=s.flatten(tree);index={p:i for i,(p,op)in enumerate(sites)}
 def locate(p):
  if p in index:return index[p]
  for i,(q,op)in enumerate(sites):
   if q[:len(p)]==p or(p[:len(q)]==q and not any(p[len(q):])):return i
  raise ValueError(p)
 def after(p):
  for j in range(len(p)-1,-1,-1):
   if p[j]==0:return locate(p[:j]+(1,))
  raise ValueError(p)
 graph=[]
 for p,(op,k)in sites:
  if op=='inc':g=(op,k,after(p))
  elif op=='dec':g=(op,k,after(s.cut(p,0,1)),after(p))
  elif op=='breakTo':g=('jump',after(s.cut(p,0,k)))
  elif op=='continueTo':g=('jump',locate(s.cut(p,1,k)))
  elif op=='halt':g=('halt',)
  else:raise ValueError(op)
  graph.append(g)
 return sites,graph

def main():
 receipt=json.loads((HERE/'receipt.json').read_text())
 for name,digest in receipt['hashes'].items():assert hashlib.sha256((HERE/name).read_bytes()).hexdigest()==digest,name
 reconstruction=reconstruct()
 labels=json.loads((HERE/'dense_labels.json').read_text())['dense_to_native']
 assert len(labels)==199 and len(set(labels))==199 and labels[0]==74 and labels[-1]==254
 dense={}
 for line in(HERE/'machine.tm').read_text().splitlines():
  q,b,w,d,n=line.split();key=int(q),int(b);assert key not in dense
  dense[key]=(int(w),d,int(n))
 assert set(dense)=={(q,b)for q in range(198)for b in(0,1)}
 for(q,b),(w,d,n)in dense.items():
  assert w in(0,1)and d in('L','R')and 0<=n<=198
  assert s.rows[labels[q],b]==(w,d,labels[n])
 box=json.loads((HERE/'box_agreement.json').read_text())['agreement_rows']
 for q,b,w,d,n in box:assert s.rows[q,b]==(w,d,n)
 source,graph=source_graph(s.TREE)
 ref,refgraph=source_graph(s.tuples(json.loads((HERE/'reference199.tree.json').read_text())))
 assert [op for p,op in source]==[op for p,op in ref]and graph==refgraph
 assert len(source)==3700
 ok,runtime=s.validate(s.rows);assert ok,runtime
 tape=set();q=74;head=0;trace=hashlib.sha256()
 for _ in range(58154):
  b=int(head in tape);w,d,n=s.rows[q,b]
  trace.update(f'{q},{head},{b},{w},{d},{n}\n'.encode())
  (tape.add if w else tape.discard)(head);head+=1 if d=='R'else-1;q=n
 path=source[25][0];phy=[0,0,0,0,0,0,2,0,0]+[1]*26
 expected={-3}|{-2+i for i,b in enumerate(path)if b}|{46};p=47
 for value in phy:p+=1;expected.update(range(p,p+value+1));p+=value+1
 assert(q,head,tape)==(84,-2,expected)
 result={'result':'PASS','reconstruction':reconstruction,'working_states':198,'transitions':396,'reference199_primitive_word_equal':True,
  'reference199_ordinal_cfg_equal':True,'source_sites':3700,'symbolic_contracts':runtime,'protected_engine_rows':len(box),
  'dense_native_conjugacy':True,'blank_startup':{'steps':58154,'state_native':q,'head':head,'one_positions':sorted(tape),'source_ordinal':25,'gap':48,'trace_sha256':trace.hexdigest()}}
 (HERE/'verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
