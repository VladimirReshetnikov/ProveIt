#!/usr/bin/env python3
"""Round18 literal signed sphere-batching compiler. No inherited code imported."""
import copy,json,hashlib
from pathlib import Path
from collections import defaultdict
ROOT=Path(__file__).resolve().parent
PRIOR=ROOT/'source_inputs'
def canon(o):return (json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode()
def put(p,o):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(canon(o))
def sha(o):return hashlib.sha256(canon(o)).hexdigest()
def norm(ts):
 d=defaultdict(int)
 for c,m in ts:d[tuple(sorted(m))]+=c
 return {m:c for m,c in d.items() if c}
def terms(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return {m:c for m,c in d.items() if c}
def sc(p,c):return {m:a*c for m,a in p.items() if a*c}
def mul(p,q):
 d=defaultdict(int)
 for m,c in p.items():
  for n,a in q.items():d[tuple(sorted(m+n))]+=c*a
 return {m:c for m,c in d.items() if c}
def var(i):return {(i,):1}
def build(point,merged=False,odd_square=False):
 src=json.loads((PRIOR/point/'equation.json').read_text());tr=json.loads((PRIOR/point/'translation_certificate.json').read_text());sh=dict(tr['shifts']);ns={v['name']:i for i,v in enumerate(src['variables'])};out=copy.deepcopy(src)
 groups=[('pow4.output',[3,12],['choose0.remainder','range8.remainder']),('pow6.output',[4,5,6,7,13],['range0.remainder','range1.remainder','range2.remainder','range3.remainder','range9.remainder']),('pow11.output',[8,9],['range4.remainder','range5.remainder']),('pow14.output',[10,11],['range6.remainder','range7.remainder'])]
 def affine(n):return add(var(ns[n]),{():sh.get(ns[n],0)})
 def form(i):return add(mul(var(ns[f'guard{i}.a']),var(ns[f'guard{i}.a'])),mul(var(ns[f'guard{i}.b']),var(ns[f'guard{i}.b'])),mul(var(ns[f'guard{i}.c']),var(ns[f'guard{i}.c'])),var(ns[f'guard{i}.c']))
 old=[]
 for dn,gs,rs in groups:
  for g,r in zip(gs,rs):
   row=next(r0 for r0 in src['residuals'] if r0['label']==f'domain_guard.{g}')
   R=affine(r);expect=add(mul(affine(dn),R),sc(R,-1),sc(mul(R,R),-1),sc(form(g),-1))
   if norm(row['terms'])!=expect:raise ValueError(('guard shape',g))
   old.append(row)
 out['residuals']=[r for r in out['residuals'] if r not in old]
 if odd_square:
  out['residuals']=[r for r in out['residuals'] if r['label']!='domain_guard.2']
  z=len(out['variables']);out['variables'].append({'name':'radix.odd_square_root','kind':'signed_witness'})
  out['residuals'].append({'label':'radix.odd_square','terms':terms(add(affine('pow2.output'),sc(mul(add(sc(var(z),2),{():1}),add(sc(var(z),2),{():1})),-1)))})
 certgroups=[]
 if merged:
  dn1,gs1,rs1=groups[0];dn2,gs2,rs2=groups[1];scaled=[]
  for r in rs1:
   i=len(out['variables']);out['variables'].append({'name':'sphere.scaled.'+r,'kind':'gate'});scaled.append(var(i));out['residuals'].append({'label':'sphere.scale.'+r,'terms':terms(add(var(i),sc(mul(affine('pow2.output'),affine(r)),-1)))})
  groups=[(dn2,gs1+gs2,rs1+rs2)]+groups[2:]
 for j,(dn,gs,rs) in enumerate(groups):
  rp=([*scaled,*[affine(r) for r in rs[2:]]]) if merged and j==0 else [affine(r) for r in rs]
  p=add(mul(affine(dn),affine(dn)),*[sc(mul(r,r),-2) for r in rp],sc(form(gs[0]),-1))
  row={'label':'sphere.interval_group.'+str(j),'terms':terms(p)};out['residuals'].append(row)
  certgroups.append({'denominator':dn,'denominator_affine':terms(affine(dn)),'old_guard_ids':gs,'remainders':rs,'scaled_remainder_polynomials':list(map(terms,rp)),'retained_guard_id':gs[0],'row':copy.deepcopy(row)})
 used=sorted({v for r in out['residuals'] for c,m in r['terms'] for v in m});mp={v:i for i,v in enumerate(used)};out['variables']=[out['variables'][v] for v in used]
 for r in out['residuals']:r['terms']=[[c,[mp[v] for v in m]] for c,m in r['terms']]
 out['variant']=src.get('variant','')+':round18_sphere_intervals'+(':merged' if merged else '')
 out.pop('metrics',None);out.pop('elimination',None)
 poly={}
 for r in out['residuals']:p=norm(r['terms']);poly=add(poly,mul(p,p))
 exp={'schema':'sparse_integer_polynomial_v1','domain':'unrestricted integers','variables':len(used),'terms':terms(poly)}
 metrics={'variables':len(used),'rows':len(out['residuals']),'degree':max(map(len,poly)),'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(c) for r in out['residuals'] for c,m in r['terms'])}
 cert={'schema':'round18_signed_sphere_v1','source_endpoint':point,'source_equation_sha256':sha(src),'source_translation_sha256':sha(tr),'output_sha256':sha(out),'merged':merged,'sphere_coefficient':2,'sphere_margin':0,'odd_square_radix':odd_square,'groups':certgroups,'removed_rows':old,'retained_original_indices':used,'removed_original_indices':sorted(set(range(len(src['variables'])))-set(used)),'coordinate_convention':'Certificate polynomials use extended source indices (source variables, then optional odd root, then optional two scale gates); output is compacted using retained_original_indices.','proof':'PROOF.md'}
 dest=ROOT/(point.replace('strict_','sphere_')+('_merged' if merged else '')+('_odd' if odd_square else ''))
 for n,o in [('source_equation.json',src),('source_translation.json',tr),('equation.json',out),('expanded_polynomial.json',exp),('certificate.json',cert),('METRICS.json',metrics)]:put(dest/n,o)
 print(dest.name,json.dumps(metrics))
if __name__=='__main__':
 for point in ['strict_dimension_centered','strict_grouped_centered','strict_sparse_centered']:
  build(point);build(point,True);build(point,False,True);build(point,True,True)
