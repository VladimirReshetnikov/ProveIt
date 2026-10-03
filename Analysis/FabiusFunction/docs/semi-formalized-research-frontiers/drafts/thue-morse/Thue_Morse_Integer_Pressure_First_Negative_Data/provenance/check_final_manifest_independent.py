#!/usr/bin/env python3
"""Additional full-rational manifest check; requires regenerated raw traces."""
if not __debug__:
 raise RuntimeError("Run without -O: this supplementary checker uses assertions")
import json,hashlib,sys
from pathlib import Path
sys.set_int_max_str_digits(0)
r=Path(__file__).resolve().parents[1];man=json.loads((r/'first_negative_manifest.json').read_text());cs=man['cases']
assert man['complete'] and [z['m'] for z in cs]==list(range(2,129))
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
count=0;pref=0
for z in cs:
 m=z['m'];N=z['first_negative_degree']
 for field in ('production','trace','audit','radii'):
  assert digest(r/z[field+'_file'])==z[field+'_sha256'],(m,field,'hash')
 ps=[]
 for field in ('production','audit'):
  d=json.loads((r/z[field+'_file']).read_text());assert d['m']==m
  rows=d['pressure_bounds'];assert [a['degree'] for a in rows]==list(range(2*m,8*m,2))
  vals=[]
  for a in rows:
   lo,hi,den=(int(a[k]) for k in ('lower_numerator','upper_numerator','denominator'))
   assert den>0 and lo<=hi
   if 2*m<a['degree']<N:assert lo>0,(m,a['degree'],'prefix')
   if a['degree']==N:assert hi<0,(m,'negative')
   vals.append((lo,hi,den))
  ps.append(vals)
 for (l,h,q),(L,H,Q) in zip(*ps):assert l*Q<=H*q and L*q<=h*Q,(m,'interval disagreement')
 count+=len(ps[0]);pref+=(N-2*m)//2-1
 assert z['positive_prefix_count']==(N-2*m)//2-1
 assert z['pressure_intervals']==3*m and z['positive_order_response_states']==8*m-2
 if m%16==0:print('verified through',m,flush=True)
assert count==24765==man['pressure_intervals']
assert sum(z['positive_order_response_states'] for z in cs)==65786==man['positive_order_response_states']
out={'orders':127,'range':[2,128],'pressure_intervals':count,'response_orders':65786,'strict_positive_prefix_intervals':pref,'all_hashes_and_dual_sign_checks_pass':True}
(r/'validation/independent_final_manifest_result.json').write_text(json.dumps(out,indent=2)+'\n');print(out,flush=True)
