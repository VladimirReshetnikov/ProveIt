#!/usr/bin/env python3
"""Independent literal checker: no imports from compiler or prior checkers."""
import json,hashlib,copy,sys,math
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parent
def require(c,m):
 if not c:raise ValueError(m)
def serial(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(x):return hashlib.sha256(serial(x)).hexdigest()
def read(p):return json.loads(p.read_text())
def collect(ts):
 out=Counter()
 for c,m in ts:out[tuple(sorted(m))]+=c
 return {m:c for m,c in out.items() if c}
def linear(name,c=1):return {(name,):c}
def plus(*ps):
 out=Counter()
 for p in ps:
  for m,c in p.items():out[m]+=c
 return {m:c for m,c in out.items() if c}
def times(p,q):
 out=Counter()
 for a,c in p.items():
  for b,d in q.items():out[tuple(sorted(a+b))]+=c*d
 return {m:c for m,c in out.items() if c}
def scale(p,c):return {m:c*v for m,v in p.items() if c*v}
def namesystem(e):
 names=[v['name'] for v in e['variables']];require(len(names)==len(set(names)),'duplicate names')
 return [(r['label'],collect([[c,[names[v] for v in m]] for c,m in r['terms']])) for r in e['residuals']]
def check(d,override=None):
 src=read(d/'source_equation.json');tr=read(d/'source_translation.json');cert=read(d/'certificate.json');e=override if override is not None else read(d/'equation.json');expanded=read(d/'expanded_polynomial.json');metrics=read(d/'METRICS.json')
 pins=read(ROOT/'SOURCE_PINS.json');point=cert['source_endpoint'];require(digest(src)==pins[point]['equation'],'source content pin');require(digest(tr)==pins[point]['translation'],'translation content pin');require(digest(src)==cert['source_equation_sha256'],'source certificate hash');require(digest(tr)==cert['source_translation_sha256'],'translation certificate hash')
 source=namesystem(src);out=[];sh={src['variables'][v]['name']:s for v,s in tr['shifts']}
 def atom(n):return plus(linear(n),{():sh.get(n,0)})
 def tri(g):return plus(times(linear(f'guard{g}.a'),linear(f'guard{g}.a')),times(linear(f'guard{g}.b'),linear(f'guard{g}.b')),times(linear(f'guard{g}.c'),linear(f'guard{g}.c')),linear(f'guard{g}.c'))
 groups=[('pow4.output',[3,12],['choose0.remainder','range8.remainder']),('pow6.output',[4,5,6,7,13],['range0.remainder','range1.remainder','range2.remainder','range3.remainder','range9.remainder']),('pow11.output',[8,9],['range4.remainder','range5.remainder']),('pow14.output',[10,11],['range6.remainder','range7.remainder'])]
 remove=set()
 for den,gs,rs in groups:
  for g,r in zip(gs,rs):
   label=f'domain_guard.{g}';remove.add(label);actual=[p for l,p in source if l==label];R=atom(r);want=plus(times(atom(den),R),scale(R,-1),scale(times(R,R),-1),scale(tri(g),-1));require(actual==[want],'old interval guard semantics')
 if cert['odd_square_radix']:remove.add('domain_guard.2')
 out=[(l,p) for l,p in source if l not in remove]
 if cert['odd_square_radix']:
  z=plus(linear('radix.odd_square_root',2),{():1});out.append(('radix.odd_square',plus(atom('pow2.output'),scale(times(z,z),-1))))
 if cert['merged']:
  scaled=[]
  for r in groups[0][2]:
   R=linear('sphere.scaled.'+r);scaled.append(R);out.append(('sphere.scale.'+r,plus(R,scale(times(atom('pow2.output'),atom(r)),-1))))
  groups=[('pow6.output',groups[0][1]+groups[1][1],groups[0][2]+groups[1][2])]+groups[2:]
 require(cert['sphere_coefficient']==2,'sphere weight');require(cert['sphere_margin']==0,'sphere margin')
 for j,(den,gs,rs) in enumerate(groups):
  rp=scaled+[atom(r) for r in rs[2:]] if cert['merged'] and j==0 else [atom(r) for r in rs]
  out.append(('sphere.interval_group.'+str(j),plus(times(atom(den),atom(den)),*[scale(times(R,R),-2) for R in rp],scale(tri(gs[0]),-1))))
 require(namesystem(e)==out,'literal transformed system')
 extnames=[v['name'] for v in src['variables']]+(['radix.odd_square_root'] if cert['odd_square_radix'] else [])+(['sphere.scaled.choose0.remainder','sphere.scaled.range8.remainder'] if cert['merged'] else [])
 def decode(ts):return collect([[c,[extnames[v] for v in m]] for c,m in ts])
 require(len(cert['groups'])==len(groups),'certificate group count')
 for j,((den,gs,rs),cg) in enumerate(zip(groups,cert['groups'])):
  require(cg['denominator']==den and cg['old_guard_ids']==gs and cg['remainders']==rs and cg['retained_guard_id']==gs[0],'certificate group metadata')
  require(decode(cg['denominator_affine'])==atom(den),'certificate denominator')
  rp=scaled+[atom(r) for r in rs[2:]] if cert['merged'] and j==0 else [atom(r) for r in rs]
  require([decode(x) for x in cg['scaled_remainder_polynomials']]==rp,'certificate remainder polynomials')
  require((cg['row']['label'],decode(cg['row']['terms']))==out[-len(groups)+j],'certificate new row')
 wanted_indices=sorted(extnames.index(n) for l,p in out for m in p for n in m)
 wanted_indices=sorted(set(wanted_indices));require(cert['retained_original_indices']==wanted_indices,'certificate compacting map')
 require([v['name'] for v in e['variables']]==[extnames[i] for i in wanted_indices],'compacted variable order')
 require(cert['removed_original_indices']==sorted(set(range(len(src['variables'])))-set(wanted_indices)),'certificate removed indices')
 require(e['domain']=='unrestricted integers','domain');require(digest(e)==cert['output_sha256'],'output hash')
 used={v for l,p in out for m in p for v in m};require(used=={v['name'] for v in e['variables']},'unused coordinates')
 poly={}
 for r in e['residuals']:
  p=collect(r['terms']);require(max(map(len,p),default=0)<=2,'quadratic row');poly=plus(poly,times(p,p))
 require(poly==collect(expanded['terms']),'collected quartic');require(len(e['variables'])==expanded['variables'],'expanded dimension')
 got={'variables':len(used),'rows':len(out),'degree':max(map(len,poly)),'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(c) for r in e['residuals'] for c,m in r['terms'])};require(got==metrics,'metric mismatch');return got

def controls():
 # This checks finite examples, not the unbounded proof in PROOF.md.
 for M in range(1,21):
  for t in range(1,41):require(all(math.comb(M+t,j)<=(M+1)**t for j in range(t+1)),'Pascal bound control')
 valid=0
 for D in range(1,81):
  for T in range((D+7)//8):
   if not 8*T<D:continue
   for r in range(-D,D+1):
    if 2*r*r<D*D and (r-T)%D==0:require(r==T,'signed tail uniqueness control');valid+=1
 return {'pascal_cases':800,'signed_uniqueness_cases':valid}
def main():
 rows={};rejected=[]
 for d in sorted(ROOT.glob('sphere_*')):
  if not d.is_dir():continue
  rows[d.name]=check(d)
  e=read(d/'equation.json')
  for label in ['sphere.interval_group.0','shared.frame_definition']+(['radix.odd_square'] if read(d/'certificate.json')['odd_square_radix'] else []):
   bad=copy.deepcopy(e);r=next(r for r in bad['residuals'] if r['label']==label);r['terms'][0][0]+=1
   try:check(d,bad)
   except ValueError:rejected.append(d.name+':'+label)
   else:raise ValueError('malformed polynomial accepted')
 result={'status':'PASS','python_optimized':not __debug__,'endpoints':rows,'negative_controls_rejected':len(rejected),'arithmetic_controls':controls(),'boundary':'Literal transformations and finite controls; mathematical proof is PROOF.md. No consistency assertion.'}
 (ROOT/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK_NORMAL.json')).write_bytes(serial(result));print(json.dumps(result,indent=2))
if __name__=='__main__':main()
