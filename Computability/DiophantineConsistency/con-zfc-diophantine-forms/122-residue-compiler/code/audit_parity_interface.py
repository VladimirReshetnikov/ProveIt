#!/usr/bin/env python3
"""Independent literal parity and frame check; imports no producer modules."""
import json, hashlib, argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('directory',type=Path,nargs='?',default=ROOT/'equations/natural333')
parser.add_argument('--output',type=Path)
args=parser.parse_args()
PATH=args.directory/'raw/raw_audit_input.json'
d=json.loads(PATH.read_text())
rows=d['rows']; gates={int(v):int(r) for v,r in d['gates'].items()}
variables=d['variables']
def fail(label):raise ValueError(label)
def require(q,label):
 if not q: fail(label)

def rhs(v):
 row=rows[gates[v]];terms={tuple(m):int(c) for c,m in row['terms']}
 require(terms.get((v,))==1,('monic',v))
 del terms[v,]
 require(not any(v in m for m in terms),('cycle',v))
 return {m:-c for m,c in terms.items()}
parity_cache={}
def parity(v):
 if v not in gates:return {frozenset([v])}
 if v in parity_cache:return parity_cache[v]
 out=set()
 for mon,coef in rhs(v).items():
  if not coef%2:continue
  term={frozenset()}
  for u in mon:
   nxt=set()
   for a in term:
    for b in parity(u):
     c=a|b
     if c in nxt:nxt.remove(c)
     else:nxt.add(c)
   term=nxt
  out.symmetric_difference_update(term)
 parity_cache[v]=out;return out
min_cache={}
def lower(v):
 if v not in gates:return 0
 if v in min_cache:return min_cache[v]
 r=rhs(v)
 if any(c<0 for c in r.values()):return 0
 out=0
 for mon,c in r.items():
  z=c
  for u in mon:z=min(64,z*lower(u))
  out=min(64,out+z)
 min_cache[v]=out;return out
seed_report=[]
for s in d['seeds']:
 kind,v=s['exponent'];require(kind=='v','variable seed')
 require(not parity(v),('odd parity possible',v))
 lo=lower(v);require(lo>=2,('zero seed possible',v,lo))
 seed_report.append({'index':v,'name':variables[v]['name'],'unconditional_lower_bound':lo})
# Identify W expression from the terminal row, then expand only affine
# intermediary sum gates, preserving all semantically required atoms.
W=d['scale'][0][1]
atoms=set()
for p in d['powers']:
 for name in ('base','exponent','output'):
  typ,val=p[name]
  if typ=='v':atoms.add(val)
  elif typ=='c': fail(('unexpected constant power atom',p))
for req in d['radix']['modular_requests']:
 typ,val=req['n'];require(typ=='v','modular index atom');atoms.add(val)
frame=[r for r in rows if r['label']=='shared.frame_definition'];require(len(frame)==1,'frame count')
def add(a,b):
 out=dict(a)
 for m,c in b.items():
  out[m]=out.get(m,0)+c
  if not out[m]:del out[m]
 return out
def linear_var(v):
 if v in atoms or v==W or v not in gates:return {(v,):1}
 out={}
 for mon,c in rhs(v).items():
  require(len(mon)<=1,('nonlinear frame gate',v))
  q={():1} if not mon else linear_var(mon[0])
  out=add(out,{m:c*k for m,k in q.items()})
 return out
actual={}
for c,mon in frame[0]['terms']:
 require(len(mon)<=1,'nonlinear frame row')
 p={():1} if not mon else linear_var(mon[0])
 actual=add(actual,{m:c*k for m,k in p.items()})
expected={(W,):1,():-2}|{(v,):-1 for v in atoms}
require(actual==expected or actual=={m:-c for m,c in expected.items()},'literal complete frame mismatch')
require(all(s['exponent'][1] in atoms for s in d['seeds']),'seed omitted from frame')
# V=v0+1 must be literal, before using the positive product row.
V=d['auxiliary'][1][1]
v_rhs=rhs(V)
require(v_rhs.get(())==1 and len(v_rhs)==2 and all(c==1 for c in v_rhs.values()),'strict common V definition')
productrows=[r for r in rows if r['label']=='shared_index.V_positive_product']
require(len(productrows)==1,'positive common-product row')
report={'raw_sha256':hashlib.sha256(PATH.read_bytes()).hexdigest(),'result':'passed',
 'checked_without_producer_imports':True,'seed_parity_and_lower_bounds':seed_report,
 'frame_atoms':len(atoms),'all_seed_indices_in_frame':True,'strict_common_ordinate':V,
 'scope':'Exact literal parity, positivity floors, and complete frame inclusion. The ordinary unbounded proof is reviewed separately in MATHEMATICAL_REVIEW.md.'}
text=json.dumps(report,indent=2)+'\n'
if args.output:args.output.write_text(text)
print(text)
