#!/usr/bin/env python3
"""Exact 6^8 census for a fixed negative-equality source shape."""
import argparse,collections,itertools,json,random,sys,time
from pathlib import Path
import inverse_mp as q
import recompile219 as compiler
s,b,z=q.s,q.b,q.z
ap=argparse.ArgumentParser();ap.add_argument('--dual',action='store_true');args=ap.parse_args()
BASE=q.W/'K219_Construction_2026-10-20'
OLD=s.tree(json.loads((BASE/'machine/sites219.json').read_text()))
T=b.read_table((BASE/'machine/k219.native.tm').read_bytes())
source=q.W/('disequality_dual219/raw_B/sites.json'if args.dual else'disequality_codec219/raw/sites.json')
OUT=q.W/('disequality_dual_row_permutations219'if args.dual else'disequality_row_permutations219');OUT.mkdir(exist_ok=True)
z.ROWS=json.loads(source.read_text());z.TREE=s.tree(z.ROWS);z.GRAPH=s.graph_arithmetic(z.ROWS)[0]
z.INTERVALS={'rho8':(135,486),'G':(486,1036),'rho6':(1036,1319),'rho5':(1319,1662),'rho4':(1662,1961),'rho3':(1961,2304),'rho2':(2304,2654),'rho1':(2654,2932)}
import exhaustive as e
rng=random.Random(20261020)
for _ in range(100):
 v=tuple(rng.randrange(6)for _ in range(8));assert e.count(v)==e.j.count(v)
start=time.time();best=999;hist=collections.Counter();small=[]
for v in itertools.product(range(6),repeat=8):
 n=e.count(v);hist[n]+=1
 if n<best:best=n;small=[];print('BEST',best,v,flush=True)
 if n==best:small.append(v)
records=[]
for i,v in enumerate(small):
 rr,tr=z.changed(e.j.as_perms(v));assert s.metrics(tr)['dag_nodes']==best
 rec={'indices':v,'permutations':e.j.as_perms(v),'metrics':s.metrics(tr)}
 dd=OUT/f'best{i}';dd.mkdir(exist_ok=True);(dd/'sites.json').write_bytes(s.compact(rr))
 try:
  U,meta=compiler.compile_tree(T,OLD,tr,extend_direct=True);rec['compiler']=meta;(dd/'candidate.tm').write_bytes(b.table_bytes(U))
 except Exception as exc:rec['error']=repr(exc)
 (dd/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');records.append(rec);print(json.dumps(rec),flush=True)
report={'tested':6**8,'dual_B':args.dual,'minimum_DAG':best,'histogram':dict(hist),'records':records,'seconds':time.time()-start,'scope':'Fixed shape; exact DAG census. Decoder compilation is not runtime proof.'}
(OUT/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
