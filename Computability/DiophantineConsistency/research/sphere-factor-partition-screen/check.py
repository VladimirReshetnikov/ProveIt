#!/usr/bin/env python3
"""Exhaustive five-factor partition arithmetic screen; no Lean or graph construction."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib, json
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent
TASK=HERE.parents[1]
CERT=TASK/'research/fourteen-nonzero-spheres/CERTIFICATE.json'
GRAPH=TASK/'research/fourteen-nonzero-spheres/polynomial71.json'
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
cb=CERT.read_bytes();gb=GRAPH.read_bytes()
need(digest(cb)=='99a901c08cd45b549a638ddd051ce80a0bf7a833231b52bc2b29d5390feb37ec','certificate hash')
need(digest(gb)=='937752350556a94539584db8f646ff9e02d25a7113e6d4af70ac22c1b1e01ad2','graph hash')
g=json.loads(gb); rows=g['source'];need(len(rows)==71 and rows[61][0]=='U' and rows[62][0]=='PQ','prefix boundary')
leaders=json.loads(cb)['profiles']['71']['degree']['all_gate_leaders']
names=('N0','N1','U','Nt','Z'); degrees={name:leaders[name]['degree'] for name in names}
need(degrees=={'N0':22,'N1':18,'U':30,'Nt':2,'Z':34},'factor degree mismatch')

def partitions(items):
    if not items:
        yield ();return
    x=items[0]
    for rest in partitions(items[1:]):
        yield ((x,),)+rest
        for j in range(len(rest)):
            yield rest[:j]+((x,)+rest[j],)+rest[j+1:]

allparts=list(partitions(names));need(len(allparts)==52 and len(set(allparts))==52,'not Bell(5)')
res=[]
for part in allparts:
    k=len(part); groupW=[q for q in part if 'Nt' in q];need(len(groupW)==1,'transport group')
    # 62 prefix gates, k blocks each having |block|-1 multiplications
    # and a square, one subtraction in the transport block, k-1 additions,
    # and a final subtraction by k-1 when k>1.
    operations=62+sum(len(q)-1 for q in part)+k+1+(k-1)+(1 if k>1 else 0)
    degree=2*max(sum(degrees[x] for x in q) for q in part)
    res.append({'blocks':[list(q) for q in part],'operations':operations,'degree':degree})
summary={}
for k in range(1,6):
    vals=[r for r in res if len(r['blocks'])==k]; best=min(r['degree'] for r in vals)
    summary[str(k)]={'count':len(vals),'operations':sorted({r['operations'] for r in vals}),
                     'best_degree':best,'optimal_partitions':[r['blocks'] for r in vals if r['degree']==best]}
need([summary[str(i)]['best_degree'] for i in range(1,6)]==[212,108,80,68,68],'unexpected optimum')
need([summary[str(i)]['count'] for i in range(1,6)]==[1,15,25,10,1],'partition counts')
# Check the already-used grouping and its operation count/degree as a positive control.
need(any(r['operations']==71 and r['degree']==80 and {frozenset(q) for q in r['blocks']}==
    {frozenset(('N0','N1')),frozenset(('U','Nt')),frozenset(('Z',))} for r in res),'71 positive control')
print(json.dumps({'status':'PASS','checker_sha256':digest(Path(__file__).read_bytes()),'certificate_sha256':digest(cb),
 'parent_graph_sha256':digest(gb),'factor_degrees':degrees,'partitions':len(res),'summary':summary,
 'scope':'Exact partition/count arithmetic conditional on pinned factor-degree certificate; no candidate zero equivalence or global lower bound.'},sort_keys=True,indent=2))
