#!/usr/bin/env python3
import gzip,hashlib,json,sys
from collections import Counter
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
root=Path(__file__).resolve().parents[2];oldp=root/'research/nine-sharing-sign15-inner-candidate/seed.json';newp=root/'research/nine-sharing-sign14-tau-candidate/seed.json';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();assert sha(oldp)=='bdd841f25618a01e659d6f2f802f0420501b00c5270df9fa56b9589733ecbd59' and sha(newp)=='7048a10d409ab5ff8031a444cd32117ba772b3834425c17a066188338e189ea9';old=json.loads(oldp.read_text());new=json.loads(newp.read_text());assert old['witness_count']==15 and new['witness_count']==14 and new['total_coordinates']==15 and new['distinguished_input_coordinate']==0
row,=[r for r in old['residuals'] if r['gate']=='tau'];assert row['expr'][:2]==['sub',['var',15]];rhs=row['expr'][2];assert rhs==new['lift_expression']
def replace(t):
 op=t[0]
 if op=='var':return rhs if t[1]==15 else t
 if op in ('num','port'):return t
 assert op in ('add','sub','mul') and len(t)==3
 return [op,replace(t[1]),replace(t[2])]
oldrows=[r for r in old['residuals'] if r['gate']!='tau'];assert len(oldrows)==len(new['residuals'])==5
for a,b in zip(oldrows,new['residuals']):assert a.keys()==b.keys() and all((replace(a[k]) if k=='expr' else a[k])==b[k] for k in a)
def degree(t):
 op=t[0]
 if op=='var':assert 0<=t[1]<15;return 1
 if op in ('num','port'):return 0
 x,y=degree(t[1]),degree(t[2]);return x+y if op=='mul' else max(x,y)
degrees={r['gate']:degree(r['expr']) for r in new['residuals']};assert degrees=={'Dc2':22,'N0':22,'Nt':2,'Na':62,'scaled_Ns':46}
# Expand just the leading homogeneous part at each node, retaining enough lower terms
# whenever top-degree cancellation occurs; variables 1..15 map to a single t.
def pol(t):
 op=t[0]
 if op=='num':return {(0,0,0,0):t[1]} if t[1] else {}
 if op=='var':assert t[1]!=0;return {(1,0,0,0):1}
 if op=='port':return { {'beta':(0,1,0,0),'MC':(0,0,1,0),'MF':(0,0,0,1)}[t[1]]:1 }
 a=pol(t[1]);b=pol(t[2]);out=Counter()
 if op in ('add','sub'):
  out.update(a)
  for k,v in b.items():out[k]+=v if op=='add' else -v
 else:
  assert op=='mul'
  for k,v in a.items():
   for l,w in b.items():out[tuple(x+y for x,y in zip(k,l))]+=v*w
 return {k:v for k,v in out.items() if v}
na,=[r['expr'] for r in new['residuals'] if r['gate']=='Na'];q=pol(na);assert max(k[0] for k in q)==62 and {k:v for k,v in q.items() if k[0]==62}=={(62,34,0,0):64}
assert new['fixed_ports']==old['fixed_ports'] and new['coefficient_binding']==old['coefficient_binding'];binding=new['coefficient_binding'];assert (oldp.parent/binding['path']).resolve()==(newp.parent/binding['path']).resolve()
for name,rec in binding['ports'].items():
 packed=(newp.parent/binding['path']/rec['file']).read_bytes();raw=gzip.decompress(packed);assert hashlib.sha256(packed).hexdigest()==rec['gzip_sha256'] and hashlib.sha256(raw).hexdigest()==rec['raw_sha256'] and len(raw)==rec['raw_bytes']
 if name=='beta':assert int.from_bytes(raw,'big')>0
def ev(t,v,p):
 op=t[0]
 if op=='num':return t[1]
 if op=='var':return v[t[1]]
 if op=='port':return p[t[1]]
 x,y=ev(t[1],v,p),ev(t[2],v,p);return {'add':lambda:x+y,'sub':lambda:x-y,'mul':lambda:x*y}[op]()
v=[0]*15;v[3]=1000;ports={'beta':10,'K0':0,'MC':0,'MF':0};gap=ev(rhs,v,ports);assert gap<0 and ev(row['expr'],v+[gap],ports)==0
print(json.dumps({'status':'PASS_EXTERNAL_CONDITIONAL','candidate_sha256':sha(newp),'syntactic_degrees':degrees,'axis_Na_leading_coefficient':'64*beta^34','degree_if_beta_nonzero':124,'negative_lift_example':gap,'scope':'external substitution and symbolic computation only; no natural lift, Lean equivalence, iPRA, or PDF binding'},indent=2,sort_keys=True))
