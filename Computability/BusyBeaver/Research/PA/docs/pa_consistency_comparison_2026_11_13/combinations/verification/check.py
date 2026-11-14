#!/usr/bin/env python3
"""Recheck frozen tables and uniform symbolic primitive contracts (stdlib only).

This is executable verification evidence, not an independently trusted proof
kernel. The report states the inherited engine lemmas and mathematical bridge.
"""
from pathlib import Path
import argparse,hashlib,json,time
import symbolic as s
BASE=Path(__file__).resolve().parents[1]
BASE_TREE=s.TREE;BASE_SITES=s.SITES;BASE_CASES=s.CASES
BOX={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
PROTECTED={(q,b) for q in BOX for b in (0,1) if b or q not in {3,16,40,113,198}}|{(198,0)}
assert len(PROTECTED)==42

def tuplify(x):return tuple(map(tuplify,x)) if isinstance(x,list) else x

def parse(p):
 out={}
 for line in p.read_text().splitlines():
  if not line.strip() or line.startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  assert b in(0,1) and w in(0,1) and d in('L','R') and(q,b)not in out
  out[q,b]=(w,d,n)
 states={q for q,b in out}
 assert set(out)=={(q,b)for q in states for b in(0,1)}
 assert 74 in states and 254 not in states
 assert all(n in states|{254}for w,d,n in out.values())
 return out

def set_tree(tree):
 s.TREE=tree;s.SITES=s.flatten(tree);s.lookup.__defaults__=(tree,)
 assert max(len(p)for p,_ in s.SITES)<=48
 s.CASES=list(s.cases())

def startup(M,limit=300000):
 vs=[0,0,0,0,0,0,2,0,0]+[1]*26
 r=[1]+[0]*47+[1]+[b for v in vs for b in [0]+[1]*(v+1)]
 wanted={-1}|{i for i,b in enumerate(r)if b};ones=set();q=74;head=0
 for n in range(limit+1):
  if q==84 and{j-head for j in ones}==wanted:return n
  if q==254:raise AssertionError('startup halted')
  b=int(head in ones);w,d,q=M[q,b]
  if w:ones.add(head)
  else:ones.discard(head)
  head+=1 if d=='R'else-1
 raise AssertionError('clean startup frame not found within stated bound')

def run(name,M,tree):
 assert all(M.get(k)==s.rows[k]for k in PROTECTED),'modified an assumed engine row'
 set_tree(tree);ok,detail=s.validate(M)
 assert ok,(name,detail)
 steps=startup(M)
 return {'name':name,'working_states':len(M)//2,'rows':len(M),
         'engine_agreement_rows':42,'startup_steps':steps,'symbolic':detail,'passed':True}

def dense_check(folder,native):
 labels=json.loads((folder/'dense_labels.json').read_text())
 if isinstance(labels,dict):
  # Stored map is dense label -> native label, with descriptive fields if any.
  if 'dense_to_native'in labels:labels=labels['dense_to_native']
  else:labels=[labels[str(i)]for i in range(len(labels))]
 dense=[]
 for line in(folder/'machine.tm').read_text().splitlines():
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  target=254 if n==199 else labels[n]
  assert native[labels[q],b]==(w,d,target)
  dense.append((q,b))
 assert set(dense)=={(q,b)for q in range(199)for b in(0,1)}

def main():
 p=argparse.ArgumentParser();p.add_argument('--experiments',action='store_true');args=p.parse_args()
 results=[run('published_PA196',s.rows,BASE_TREE)]
 f=BASE/'diagonal199';M=parse(f/'machine.native.tm')
 result=run('diagonal_vacuity_199',M,tuplify(json.loads((f/'source.tree.json').read_text())))
 dense_check(f,M);result['dense_table_sha256']=hashlib.sha256((f/'machine.tm').read_bytes()).hexdigest();results.append(result)
 if args.experiments:
  for f in sorted((BASE/'experiments').iterdir()):
   if (f/'machine.native.tm').exists()and(f/'source.tree.json').exists():
    results.append(run(f.name,parse(f/'machine.native.tm'),tuplify(json.loads((f/'source.tree.json').read_text()))))
 print(json.dumps({'results':results,'scope':'Finite symbolic contracts and startup; mathematical PA calibration is in the report, not executed here.'},indent=2))
if __name__=='__main__':main()
