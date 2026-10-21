#!/usr/bin/env python3
"""Replay either complete 6^8 fixed-shape logical-row permutation census."""
import argparse,collections,itertools,json,os,random,sys,time
from pathlib import Path
ap=argparse.ArgumentParser()
ap.add_argument('--workspace',type=Path,default=Path(__file__).resolve().parent)
ap.add_argument('--reverse-rho1',action='store_true')
ap.add_argument('--output',type=Path)
args=ap.parse_args();W=args.workspace.resolve()
OUT=(args.output or W/('row_permutations_reversed'if args.reverse_rho1 else'row_permutations_original')).resolve()
OUT.mkdir(parents=True,exist_ok=True)
os.environ['K221_BASE']=str(W/'K221_Construction_2026-10-20')
os.environ['ENCODING_OUTPUT']=str(OUT)
sys.path.insert(0,str(W/'K220_Construction_2026-10-20/research/encoding/scripts/rows'))
import search as z
base=W/'K220_Construction_2026-10-20/machine'
z.T=z.b.read_table((base/'k220.native.tm').read_bytes())
oldrows=json.loads((base/'sites220.json').read_text());old=z.s.tree(oldrows)
rows=json.loads(json.dumps(oldrows))
if args.reverse_rho1:
 for i in range(2445,2497):
  if rows[i][1]in('CI','CD')and rows[i][2]in(4,5):rows[i][2]=9-rows[i][2]
z.ROWS=rows;z.TREE=z.s.tree(rows);z.GRAPH=z.s.graph_arithmetic(rows)[0]
import exhaustive as e
rng=random.Random(20261020)
for _ in range(100):
 v=tuple(rng.randrange(6)for _ in range(8));assert e.count(v)==e.j.count(v)
start=time.monotonic();hist=collections.Counter();small=[];best=999
for v in itertools.product(range(6),repeat=8):
 n=e.count(v);hist[n]+=1;best=min(best,n)
 if n<=210:small.append((n,v))
results=[]
for n,v in sorted(small):
 rr,tt=z.changed(e.j.as_perms(v));rec={'dag_nodes':n,'indices':v,'permutations':e.j.as_perms(v)}
 try:
  U,meta=z.compile_tree(z.T,old,tt);rec['compiler']=meta
 except Exception as exc:rec['error']=repr(exc)
 results.append(rec)
out={'status':'EXHAUSTIVE_FIXED_SHAPE_ROW_PERMUTATIONS','reverse_rho1':args.reverse_rho1,
     'count':6**8,'minimum':best,'histogram':dict(hist),'results':results,
     'seconds':time.monotonic()-start,'scope':'Decoder counts only; no runtime certification'}
(OUT/'summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='results'},indent=2))
