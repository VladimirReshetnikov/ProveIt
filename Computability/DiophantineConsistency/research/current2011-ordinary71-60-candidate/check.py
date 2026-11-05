#!/usr/bin/env python3
"""Check candidate graph, specialized port bytes, degree bound and modular ray."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import gzip,hashlib,json
from collections import Counter
from pathlib import Path
HERE=Path(__file__).resolve().parent; TASK=HERE.parents[1]
def need(ok,msg):
    if not ok:raise RuntimeError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
gb=(HERE/'polynomial.json').read_bytes();need(sha(gb)=='3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27','graph hash');g=json.loads(gb)
pb=(TASK/'research/current2011-ordinary67-94-candidate/polynomial.json').read_bytes();need(sha(pb)=='d76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb','parent hash');p=json.loads(pb)
cb=(TASK/'research/fourteen-nonzero-spheres/CERTIFICATE.json').read_bytes();need(sha(cb)=='99a901c08cd45b549a638ddd051ce80a0bf7a833231b52bc2b29d5390feb37ec','certificate hash');c=json.loads(cb)
need(g['source'][:61]==p['source'][:61] and {k:v for k,v in g['coefficient_binding'].items() if k!='path'}=={k:v for k,v in p['coefficient_binding'].items() if k!='path'},'shared prefix/ports')
need(len(g['source'])==71,'gate count'); counts=Counter(row[1] for row in g['source']);need(dict(counts)=={'*':38,'+':19,'-':14},'operation profile')
values=set(g['witnesses']+g['fixed_numerals']);producers={}
for n,op,a,b in g['source']:
    need(n not in values and op in ('+','-','*'),'bad node')
    for x in (a,b):need(isinstance(x,int) or x in values,'bad dependency')
    values.add(n);producers[n]=(a,b)
seen=set();leaves=set();stack=[g['output']]
while stack:
    x=stack.pop()
    if x in producers and x not in seen:seen.add(x);stack.extend(producers[x])
    elif isinstance(x,str) and x not in producers:leaves.add(x)
need(len(seen)==71 and leaves==set(g['witnesses']+g['fixed_numerals']),'liveness')
# Prefix degrees come from the pinned full leader certificate, including N1's exact cancellation.
degrees={x:1 for x in g['witnesses']};degrees.update({x:0 for x in g['fixed_numerals']})
leaders=c['profiles']['71']['degree']['all_gate_leaders']
for n,op,a,b in g['source'][:51]:degrees[n]=leaders[n]['degree']
def degree(x):return 0 if isinstance(x,int) else degrees[x]
for n,op,a,b in g['source'][51:]:degrees[n]=(degree(a)+degree(b) if op=='*' else max(degree(a),degree(b)))
need({n:degrees[n] for n in ('N0','N1','Na','Nt','strong_residual','polynomial')}=={'N0':22,'N1':18,'Na':30,'Nt':2,'strong_residual':22,'polynomial':60},'degree upper bound')
prime=1000000007;fixed={};port_dir=(HERE/g['coefficient_binding']['path']).resolve();need(port_dir==(TASK/'research/fourteen-nonzero-spheres/coefficients').resolve(),'coefficient path')
for name,meta in g['coefficient_binding']['ports'].items():
    z=(port_dir/meta['file']).read_bytes();need(sha(z)==meta['gzip_sha256'],'compressed port '+name)
    b=gzip.decompress(z);need(len(b)==meta['raw_bytes'] and sha(b)==meta['raw_sha256'],'raw port '+name)
    fixed[name]=int.from_bytes(b,'big')%prime
# Full graph along the ray all witnesses=t, evaluated as polynomials over F_p.
def trim(a):
    while len(a)>1 and a[-1]==0:a.pop()
    return a
def add(a,b,sgn=1):return trim([(a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def addm(a,b,sgn=1):return trim([x%prime for x in add(a,b,sgn)])
def mul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):r[i+j]=(r[i+j]+x*y)%prime
    return trim(r)
vals={x:[0,1] for x in g['witnesses']};vals.update({x:[y] for x,y in fixed.items()})
def val(x):return [x%prime] if isinstance(x,int) else vals[x]
for n,op,a,b in g['source']:
    av,bv=val(a),val(b);vals[n]=mul(av,bv) if op=='*' else addm(av,bv,1 if op=='+' else -1)
out=vals[g['output']];need(len(out)-1==60 and out[-1]!=0,'ray lower bound')
print(json.dumps({'status':'PASS','checker_sha256':sha(Path(__file__).read_bytes()),'graph_sha256':sha(gb),
 'certificate_sha256':sha(cb),'live_rows':len(seen),'operations':dict(counts),'degree_upper':60,
 'factor_degree_bounds':{n:degrees[n] for n in ('N0','N1','Na','Nt','strong_residual')},
 'ray_modulus':prime,'ray_degree':len(out)-1,'ray_leading_coefficient':out[-1],
 'scope':'Exact graph/count and degree: prefix bound from pinned certificate, independent full-graph modular ray. No zero-equivalence or iPRA claim.'},indent=2,sort_keys=True))
