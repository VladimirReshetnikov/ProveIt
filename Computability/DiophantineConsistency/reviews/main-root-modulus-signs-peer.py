#!/usr/bin/env python3
"""Independent original-row/domain ledger audit for the21 proposed sign consequences.

Imports neither the author's generator nor checker nor any optimizer/emitter.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys
import zipfile
ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
HERE=ROOT/'research/main-root-and-modulus-signs'
def need(p,s):
 if not p:raise ValueError(s)
def load(p):return json.loads(p.read_bytes())
def sha(p):return sha256(p.read_bytes()).hexdigest()
def P(terms):
 p={}
 for c,m in terms:
  key=tuple(sorted(m));p[key]=p.get(key,0)+c
 return{m:c for m,c in p.items()if c}
def C(c):return{():c}if c else{}
def V(i):return{(i,):1}
def plus(a,b,sign=1):
 p=dict(a)
 for m,c in b.items():p[m]=p.get(m,0)+sign*c
 return{m:c for m,c in p.items()if c}
def times(a,b):
 p={}
 for m,c in a.items():
  for n,d in b.items():
   key=tuple(sorted(m+n));p[key]=p.get(key,0)+c*d
 return{m:c for m,c in p.items()if c}
def vars_(p):return{i for m in p for i in m}
def product(xs):
 p=C(1)
 for x in xs:p=times(p,x)
 return p

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);cli=ap.parse_args()
 manifest=load(HERE/'MANIFEST.json')
 for rel,h in manifest['files'].items():need(sha(HERE/rel)==h,'sealed research file '+rel)
 need({p.name for p in HERE.iterdir()if p.is_file()}==set(manifest['files'])|{'MANIFEST.json'},'closed research packet file inventory')
 pins=load(HERE/'SOURCE_PINS.json')
 for rel,h in pins['files'].items():need(sha(ROOT/rel)==h,'immutable source '+rel)
 archive=REPO/pins['signed_index_archive']['repository_path'];need(sha(archive)==pins['signed_index_archive']['sha256'],'whole signed-index archive')
 with zipfile.ZipFile(archive)as z:
  rawtheorem=z.read(pins['signed_index_member']['path'])
 need(sha256(rawtheorem).hexdigest()==pins['signed_index_member']['sha256']and rawtheorem==(HERE/'SIGNED_INDEX_THEOREM_SOURCE.md').read_bytes(),'exact signed theorem bytes')
 raw=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json');cert=load(HERE/'CERTIFICATE.json');rows=[P(r['terms'])for r in raw['rows']]
 need(len(raw['variables'])==1259,'whole raw coordinate inventory')
 combination_count=0
 def combination(obj,expected=None,prefix=False):
  nonlocal combination_count
  got={}
  for term in obj['row_combination']:
   p=P(term['multiplier']);row=rows[term['row']]
   if prefix:need(vars_(p)|vars_(row)<=set(range(643)),'no private variable in a prefix row identity')
   got=plus(got,times(p,row))
  if expected is None:expected=P(obj.get('polynomial',obj.get('expanded_polynomial')))
  need(got==expected,'every coefficient of complete original-row combination');combination_count+=1
  return got
 bounds={i:0 for i in cert['prefix_proof']['initial_semantic_guard_indices']}
 need(len(bounds)==61 and all(i<643 for i in bounds),'exact initial semantic guards')
 def shifted(p):
  need(vars_(p)<=set(bounds),'no unproved sign dependency in lower-bound inference')
  result={}
  for m,c in p.items():result=plus(result,product([C(c)]+[plus(V(i),C(bounds[i]))for i in m]))
  return result
 def strict_positive(p):
  q=shifted(p);need(all(c>=0 for c in q.values())and q.get((),0)>0,'universal strict positive polynomial after proven lower-bound shift')
 def bound(obj,prefix=False):
  var,F,R,L=obj['variable'],P(obj['factor']),P(obj['rhs']),obj['lower']
  need(var not in vars_(F)|vars_(R),'target sign not used in its own proof')
  combination(obj,plus(times(V(var),F),R,-1),prefix)
  strict_positive(F);strict_positive(plus(R,times(C(L-1),F),-1));bounds[var]=max(bounds.get(var,L),L)
 def sign_step(s):
  v,c,rhs=s['variable'],s['coefficient'],P(s['rhs']);need(v<643 and c>0,'prefix sign pivot')
  need(vars_(rows[s['row']])|vars_(rhs)<=set(range(643)),'prefix sign independent of all private coordinates')
  want=plus(times(C(c),V(v)),rhs,-1);need(rows[s['row']]==want or rows[s['row']]==times(C(-1),want),'complete literal sign row up to sign')
  if s['kind']=='positive_monomials':
   need(all(a>0 for a in rhs.values()),'positive RHS coefficients')
   deps={i for m in rhs for i,k in Counter(m).items()if k%2}
   need(deps==set(s['dependencies'])and deps<=set(bounds),'all odd-power signs proved earlier')
  else:
   need(s['kind']=='affine_square'and times(P(s['square_root']),P(s['square_root']))==rhs,'exact complete affine-square RHS')
  bounds[v]=max(bounds.get(v,0),0)
 for obj in cert['prefix_proof']['preliminary_t_n_bounds']:bound(obj,True)
 sign_count=0
 for stage in cert['prefix_proof']['five_stages']:
  for s in stage['preceding_sign_steps']:sign_step(s);sign_count+=1
  bound(stage,True)
 for s in cert['prefix_proof']['final_sign_steps']:sign_step(s);sign_count+=1
 need(set(range(643))<=set(bounds),'every643 prefix value is nonnegative')
 need(cert['prefix_proof']['required_nonnegative_coordinates']==list(range(643)),'complete prefix target list')
 # Positive constructors are independent from all private signs and power meanings.
 pp=cert['positive_prefix'];canon=P(pp['canonical_modulus_cut']['polynomial']);combination(pp['canonical_modulus_cut'],prefix=True)
 expected=plus(plus(C(1),product([V(87),plus(C(1),V(59))])),V(129),-1);need(canon==expected,'canonical positive M constructor')
 strict_positive(plus(canon,V(129)))
 positive={4,5,129};need(pp['initial_positive_coordinates']==[4,5,129]and bounds[4]>=1 and bounds[5]>=2,'initial positive bases')
 for s in pp['steps']:
  v=s['variable'];row=rows[s['row']];need(v<643 and row.get((v,))==1 and all(v not in m or m==(v,)for m in row),'literal positive constructor pivot')
  rhs={m:-c for m,c in row.items()if m!=(v,)}
  need(all(c>0 for c in rhs.values())and vars_(rhs)<=set(range(643)),'nonnegative constructor polynomial')
  m=tuple(s['positive_monomial']);need(rhs.get(m,0)>0 and set(m)<=positive,'earlier strictly positive monomial')
  positive.add(v)
 need(positive==set(pp['known_after']),'exact positive constructor closure')
 actual_exponents=[s['exponent'][1]for s in raw['seeds']]
 need(len(actual_exponents)==15 and len(set(actual_exponents))==15 and actual_exponents==pp['required_seed_exponents']and set(actual_exponents)<=positive,'all15 actual exponents strictly positive')
 # Keep the only initially needed private modulus sign.
 need(694 in cert['remaining_raw_guard_indices'],'base0.T guard retained');bounds[694]=0
 for obj in cert['initial_A_D_bounds']:bound(obj)
 args=sorted({a[1]for call in raw['powers']for a in [call['base'],call['exponent'],call['output']]})
 need(args==cert['frame_arguments']and all(i<643 for i in args),'all actual power arguments in independent prefix')
 frame=plus(V(643),C(-2))
 for i in args:frame=plus(frame,V(i),-1)
 combination(cert['frame_cut'],frame)
 W,A,Z=V(643),V(644),V(646)
 bootstrap=plus(plus(times(A,A),C(-1)),times(product([W,W,W,plus(W,C(2))]),times(Z,Z)),-1)
 combination(cert['bootstrap_norm'],bootstrap)
 for c in [cert['unit_norm_cut'],cert['comparison_base_constructor'],cert['comparison_base_congruence'],cert['positive_V_product']]:combination(c)
 Ys=[s['pair'][1][1]for s in raw['seeds']]
 normU=plus(plus(times(V(655),V(655)),C(-1)),times(plus(times(A,A),C(-1)),times(V(656),V(656))),-1)
 need(P(cert['unit_norm_cut']['polynomial'])==normU,'exact common unit norm')
 constructor=plus(plus(V(667),C(-1)),product([C(4),V(656),plus(V(657),C(1))]),-1)
 need(P(cert['comparison_base_constructor']['polynomial'])==constructor,'exact comparison B constructor')
 need(P(cert['comparison_base_congruence']['polynomial'])==plus(plus(V(667),A,-1),times(V(655),V(658)),-1),'exact B=A modulo U row')
 need(P(cert['positive_V_product']['polynomial'])==plus(V(656),product([plus(C(1),V(1214))]+[times(V(y),V(y))for y in Ys]),-1),'whole product V, without coprimality premise')
 for mod in cert['moduli']:
  n,T=mod['base'],mod['modulus'];expected=plus(plus(plus(product([C(2),A,V(n)]),times(V(n),V(n)),-1),C(-1)),V(T),-1)
  combination(mod['cut'],expected)
  need(mod['early_positive_base']==(n!=87),'only factorial0 base postponed')
  if n!=87:need(n in positive,'every earlier constructor base strictly positive')
 need(len(cert['moduli'])==7 and [m['modulus']for m in cert['moduli']if m['retained_guard']]==[694],'exact seven base moduli')
 interfaces=load(ROOT/'candidates/projected-radius-mixed/arithmetic_interfaces.json')
 need(len(cert['seeds'])==len(raw['seeds'])==len(interfaces['seeds'])==15,'complete source seed count')
 for s,actual,inter in zip(cert['seeds'],raw['seeds'],interfaces['seeds']):
  al=s['aliases'];X,Y,k,S,R=map(al.get,['X','Y','k','S','R'])
  need(actual['exponent']==['v',k]and actual['pair']==[['v',X],['v',Y]]and inter['X']==['v',X]and inter['Y']==['v',Y],'complete actual seed binding')
  need(k in positive and al['YminusK']in cert['remaining_raw_guard_indices'],'positive exponent and retained Y-k sign')
  expected={
   'norm1':plus(plus(times(V(X),V(X)),C(-1)),times(plus(times(A,A),C(-1)),times(V(Y),V(Y))),-1),
   'norm3':plus(plus(times(V(S),V(S)),C(-1)),times(plus(times(V(667),V(667)),C(-1)),times(V(R),V(R))),-1),
   'S_mod_U':plus(plus(V(S),V(X),-1),times(V(655),V(al['Squotient'])),-1),
   'R_mod_4Y':plus(plus(V(R),V(k),-1),product([C(4),V(Y),V(al['Rquotient'])]),-1),
   'index_at_most_Y':plus(plus(V(Y),V(k),-1),V(al['YminusK']),-1)}
  need(set(s['cuts'])==set(expected),'all five signed-index premises')
  for name,polynomial in expected.items():combination(s['cuts'][name],polynomial)
 need(len(cert['power_calls'])==len(raw['powers'])==len(interfaces['powers'])==21,'every literal source power call')
 for call,actual in zip(cert['power_calls'],raw['powers']):
  need([actual[f]for f in ['base','exponent','output']]==[['v',call[f]]for f in ['base','exponent','output']],'entire actual call binding')
  n,k,m,X,Y,T,h=[call[f]for f in ['base','exponent','output','X','Y','modulus','quotient']]
  want=plus(plus(plus(V(X),times(plus(A,V(n),-1),V(Y)),-1),V(m),-1),times(V(T),V(h)),-1)
  combination(call['cut'],want)
 for s in cert['seeds']:
  call=cert['power_calls'][s['selected_power_call']]
  need(call['exponent']==s['aliases']['k']and call['X']==s['aliases']['X']and call['Y']==s['aliases']['Y']and call['base']in [5,92,531,530],'all15 independent positive-base supporting calls')
 early=cert['power_calls'][cert['early_exact_value_call']]
 need((early['base'],early['exponent'],early['output'],early['modulus'])==(92,86,93,730),'exact early pow1 interface')
 removed={s['aliases']['X']for s in cert['seeds']}|{m['modulus']for m in cert['moduli']if not m['retained_guard']}
 need(len(removed)==21 and set(cert['remaining_raw_guard_indices'])==set(cert['original_guard_indices'])-removed,'exact21 omitted guards')
 need(len(cert['remaining_raw_guard_indices'])==79 and {657,1214}<=set(cert['remaining_raw_guard_indices']),'retained common positive factors')
 for d in cert['removed_guard_identities']:need(d['raw_variable']in removed and raw['variables'][d['raw_variable']]==d['metadata'],'exact removed coordinate identity')
 # Small arithmetic checks of universal inequalities, never interpreted as unbounded proof.
 inequalities=0
 for w in range(2,14):
  a=w**w+1
  for n in range(1,w):
   T=2*a*n-n*n-1;need(T-a==(a-2)+(n-1)*(2*a-n-1)and T>=a,'positive modulus bound')
   for k in range(1,w):
    for m in range(w):need(1<=m*n**k+1<=w**w<a<=T,'negative-X product impossible range');inequalities+=1
 result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),
  source_pins={str(p.relative_to(ROOT)):sha(p)for p in [HERE/'README.md',HERE/'CERTIFICATE.json',HERE/'SOURCE_PINS.json',HERE/'SIGNED_INDEX_THEOREM_SOURCE.md']},
  independent_prefix=dict(nonnegative_coordinates=643,initial_semantic_guards=61,sequential_original_sign_rows=sign_count,strict_positive_constructor_steps=len(pp['steps']),strictly_positive_seed_exponents=15),
  sealed_packet=dict(manifest_sha256=sha(HERE/'MANIFEST.json'),authenticated_files=len(manifest['files'])+1),
  original_row_combinations_checked=combination_count,all_seed_premises=15,all_actual_calls=21,independent_chosen_calls=15,early_pow1=(92,86,93,730),
  removed_guard_signs=21,remaining_guards=79,finite_integer_inequality_controls=inequalities,
  scope='Independent complete original-row combinations, prefix signs,15 exact signed-index/positive-exponent interfaces and21 call bindings; unbounded ordinary argument reviewed separately. No generated quartic or Lean/native calibration claim.')
 cli.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
