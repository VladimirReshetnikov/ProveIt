#!/usr/bin/env python3
"""Independent whole-row and filtered-prefix check; no producer import."""
import json,sys,argparse
from hashlib import sha256
from collections import Counter,defaultdict
from pathlib import Path
HERE=Path(__file__).resolve().parent
S=HERE/'source'
REMOVED={548,575,584,592,600,609,618,627,636}
SIGNED={546,573,583,591,599,607,617,625,635}
CALLS=[7,10,12,13,14,15,17,18,20]
def need(b,s):
 if not b:raise ValueError(s)
def load(p):return json.loads(p.read_bytes())
def P(ts):
 p=defaultdict(int)
 for c,m in ts:p[tuple(sorted(m))]+=c
 return {m:c for m,c in p.items() if c}
def C(c):return {():c} if c else {}
def V(i):return {(i,):1}
def add(a,b,k=1):
 r=dict(a)
 for m,c in b.items():r[m]=r.get(m,0)+k*c
 return {m:c for m,c in r.items() if c}
def mul(a,b):
 r=defaultdict(int)
 for ma,ca in a.items():
  for mb,cb in b.items():r[tuple(sorted(ma+mb))]+=ca*cb
 return {m:c for m,c in r.items() if c}
def product(fs):
 r=C(1)
 for f in fs:r=mul(r,f)
 return r
def vs(p):return {v for m in p for v in m}
def odd(p):return {v for m in p for v,k in Counter(m).items() if k%2}
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,default=HERE/'SOURCE_VERIFY.json');cli=ap.parse_args()
 for rel,info in load(HERE/'SOURCE_PINS.json')['files'].items():need(sha256((HERE/rel).read_bytes()).hexdigest()==info['sha256'],'frozen input: '+rel)
 old=load(S/'parent75.json');od=load(S/'domain75.json');src=load(HERE/'parent.json');domain=load(HERE/'domain.json');cert=load(S/'sign_certificate.json');raw=load(S/'raw_builder.json')
 need(src['variables'][:1259]==old['variables'][:1259]==raw['variables'],'whole original body metadata')
 need((len(src['variables']),len(src['residuals']))==(1457,1243),'66guard raw census')
 for i in range(1176):need(src['residuals'][i]==old['residuals'][i],'unchanged body row'+str(i))
 rows=[P(r['terms']) for r in src['residuals']]
 expected=[g['predicate'] for g in od['guards'] if not(g['predicate']['kind']=='retained_scalar' and g['predicate']['raw_variables'][0] in REMOVED)]
 need(len(expected)==66 and [g['predicate'] for g in domain['guards']]==expected,'66 retained predicates')
 for j,g in enumerate(domain['guards']):
  a,b,c=range(1259+3*j,1262+3*j)
  need(g['auxiliary']==[a,b,c],'guard positions')
  need(rows[1177+j]==P(g['predicate']['terms']+[[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]),'complete guard polynomial')
 args=sorted({v[1] for p in raw['powers'] for v in [p['base'],p['exponent'],p['output']]})
 need(args==cert['frame_arguments'] and len(args)==43,'all43 actual power atoms')
 need(not SIGNED & {c[key][1] for c in raw['powers'] for key in ['base','exponent']},'omitted outputs are terminal, never power inputs')
 frame=add(V(643),C(-2))
 for i in args:frame=add(frame,mul(V(i),V(i)) if i in SIGNED else V(i),-1)
 need(rows[1176]==frame,'signed square frame')
 nideals=0
 def ideal(obj,expect=None):
  nonlocal nideals
  got={}
  for t in obj['row_combination']:
   need(t['row']!=1176,'must not assume old frame');got=add(got,mul(P(t['multiplier']),rows[t['row']]))
  if expect is None:expect=P(obj.get('polynomial',obj.get('expanded_polynomial')))
  need(got==expect,'complete original-row ideal');nideals+=1
 bounds={i:0 for i in cert['prefix_proof']['initial_semantic_guard_indices'] if i not in REMOVED and i!=93}
 bounds[87]=2
 # Recover the omitted output93 with complete exact rows78..85.
 values={}
 def sub(p):
  z={}
  for mon,c in p.items():z=add(z,product([C(c)]+[values.get(v,V(v)) for v in mon]))
  return z
 for j in [78,79,80,81,83,84]:
  v=max(vs(rows[j]));need(rows[j].get((v,))==1,'early topological gate')
  values[v]=sub({m:-c for m,c in rows[j].items() if m!=(v,)})
 f,r,s,N,Cvar=map(V,[87,94,95,93,91])
 R=add(add(add(Cvar,r,-1),s,-1),C(-1))
 E=add(add(mul(f,Cvar),N,-1),s,-1)
 need(sub(rows[85])==R,'C=r+s+1 exact cut')
 need(sub(rows[82])==add(R,E,-1),'fC=N+s exact cut')
 target=add(N,add(add(mul(f,r),mul(add(f,C(-1)),s)),f),-1)
 need(add(mul(f,R),E,-1)==target,'N=f*r+(f-1)*s+f exact identity')
 bounds[93]=2
 def shifted(p):
  need(vs(p)<=set(bounds),'unproved sign dependency')
  z={}
  for mon,c in p.items():z=add(z,product([C(c)]+[add(V(v),C(bounds[v])) for v in mon]))
  return z
 def strict(p):
  q=shifted(p);need(all(c>=0 for c in q.values()) and q.get((),0)>0,'strict positive shift')
 def bound(o):
  v,F,R,L=o['variable'],P(o['factor']),P(o['rhs']),o['lower']
  need(v not in vs(F)|vs(R),'no circular target sign')
  ideal(o,add(mul(V(v),F),R,-1));strict(F);strict(add(R,mul(C(L-1),F),-1));bounds[v]=max(bounds.get(v,L),L)
 accepted=[];skipped=[]
 def sign(s):
  v,c,rhs=s['variable'],s['coefficient'],P(s['rhs']);want=add(mul(C(c),V(v)),rhs,-1)
  need(v<643 and c>0 and rows[s['row']] in (want,mul(C(-1),want)),'literal prefix sign row')
  if s['kind']=='positive_monomials':
   need(all(a>0 for a in rhs.values()) and odd(rhs)==set(s['dependencies']),'positive coefficients and exact dependencies')
   if not odd(rhs)<=set(bounds):skipped.append(s);return
  else:need(s['kind']=='affine_square' and mul(P(s['square_root']),P(s['square_root']))==rhs,'whole square')
  bounds[v]=max(bounds.get(v,0),0);accepted.append(s)
 for o in cert['prefix_proof']['preliminary_t_n_bounds']:bound(o)
 for st in cert['prefix_proof']['five_stages']:
  for s in st['preceding_sign_steps']:sign(s)
  bound(st)
 for s in cert['prefix_proof']['final_sign_steps']:sign(s)
 missing=sorted(set(range(643))-set(bounds))
 need(len(missing)==38 and SIGNED|REMOVED<=set(missing),'exact38 unguarded quotient-cone values')
 need(set(args)-SIGNED<=set(bounds),'all other atoms nonnegative')
 pp=cert['positive_prefix'];ideal(pp['canonical_modulus_cut']);strict(add(P(pp['canonical_modulus_cut']['polynomial']),V(129)))
 positive={4,5,129};possteps=[]
 for s in pp['steps']:
  v=s['variable'];row=rows[s['row']]
  need(row.get((v,))==1 and all(v not in m or m==(v,) for m in row),'positive pivot')
  rhs={m:-c for m,c in row.items() if m!=(v,)};need(all(c>0 for c in rhs.values()),'positive RHS')
  if not odd(rhs)<=set(bounds):continue
  mon=tuple(s['positive_monomial'])
  if not(rhs.get(mon,0)>0 and set(mon)<=positive):continue
  positive.add(v);possteps.append(s)
 need({s['exponent'][1] for s in raw['seeds']}<=positive,'all15 seed indices positive')
 need(530 in positive and rows[509]==P([[-1,[]],[-1,[530]],[1,[531]]]),'signed output common base531 at least2')
 bounds[694]=0
 for o in cert['initial_A_D_bounds']:bound(o)
 for key in ['bootstrap_norm','unit_norm_cut','comparison_base_constructor','comparison_base_congruence','positive_V_product']:ideal(cert[key])
 for mod in cert['moduli']:ideal(mod['cut'])
 for seed in cert['seeds']:
  for cut in seed['cuts'].values():ideal(cut)
 for call in cert['power_calls']:ideal(call['cut'])
 retained={g['predicate']['raw_variables'][0] for g in domain['guards'] if g['predicate']['kind']=='retained_scalar'}
 selected=[]
 for j in CALLS:
  c=cert['power_calls'][j];need(c['output'] in SIGNED and c['base']==531,'signed call binding')
  seed=next(s for s in cert['seeds'] if s['aliases']['k']==c['exponent'])
  need(seed['aliases']['YminusK'] in retained and c['exponent'] in positive,'retained positive ordinate/index')
  selected.append({k:c[k] for k in ['base','exponent','output','X','Y','modulus','quotient']})
 # Independently collapse only literal local defining gates, preserving all other coordinates.
 inter=load(S/'arithmetic_interfaces.json');gate_rows=set(inter['all_gate_rows'])
 def local_cuts(lo,hi):
  substitutions={}
  def subst(poly):
   acc={}
   for mon,c in poly.items():acc=add(acc,product([C(c)]+[substitutions.get(v,V(v)) for v in mon]))
   return acc
  cuts={}
  for j in range(lo,hi+1):
   if j in gate_rows:
    v=max(vs(rows[j]));need(rows[j].get((v,))==1,'range local monic gate')
    substitutions[v]=subst({mon:-c for mon,c in rows[j].items() if mon!=(v,)})
   else:cuts[src['residuals'][j]['label']]=subst(rows[j])
  return cuts
 cuts=local_cuts(543,593);range_bindings=[]
 for name,q,m,L,r,s in [('a',575,573,574,576,577),('b',584,583,574,585,586),('c',592,591,574,593,594),('d',600,599,574,601,602),('S',609,607,608,610,611),('Sp',618,617,608,619,620),('u',627,625,626,628,629),('vq',636,635,626,637,638)]:
  want=add(add(V(m),product([V(129),V(L),V(q)]),-1),V(r),-1)
  rem=add(add(add(V(L),V(r),-1),V(s),-1),C(-1))
  need(cuts['crt.range.'+name+'.quotient_multiple']==want and cuts['crt.range.'+name+'.remainder_bound']==rem,'whole range division and bound')
  need(r in retained and s in retained and 129 in positive,'range quotient recovery signs')
  range_bindings.append({'name':name,'quotient':q,'output':m,'M':129,'L':L,'remainder':r,'slack':s})
 if 548 in REMOVED:
  cuts=local_cuts(521,531)
  need(cuts['choose1.digit']==add(add(V(546),mul(V(547),add(V(111),mul(V(530),V(548)))),-1),V(549),-1),'ninth digit division')
  need(cuts['choose1.remainder_bound']==P([[1,[547]],[-1,[549]],[-1,[550]],[-1,[]]]),'ninth remainder bound')
  need(cuts['choose1.digit_bound']==P([[1,[530]],[-1,[111]],[-1,[551]],[-1,[]]]),'ninth digit bound')
  need({549,550,551}<=retained and 111 in bounds and 530 in positive,'ninth quotient recovery positive divisor')
 receipt={'status':'PASS','optimized_python':bool(sys.flags.optimize),'guards':66,'changed_source_rows':[1176],'source_body_variables':1259,'source_body_rows':1177,'prefix_missing_before_signed_power':missing,'retained_prefix_nonnegative':643-len(missing),'accepted_sign_steps':len(accepted),'skipped_sign_steps':len(skipped),'positive_constructor_steps':len(possteps),'checked_row_ideals':nideals,'selected_calls':selected,'range_records':raw['ranges'],'range_bindings':range_bindings,'scope':'Finite source identities and acyclic prefix certificate; unbounded proof separate.'}
 cli.output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 (HERE/'FILTERED_PREFIX.json').write_text(json.dumps({'accepted_steps':accepted,'skipped_steps':skipped,'bounds':bounds,'positive_steps':possteps,'positive_variables':sorted(positive)},sort_keys=True,separators=(',',':'))+'\n')
 print(json.dumps({k:v for k,v in receipt.items() if k not in ['range_records','range_bindings','selected_calls']},indent=2))
if __name__=='__main__':main()
