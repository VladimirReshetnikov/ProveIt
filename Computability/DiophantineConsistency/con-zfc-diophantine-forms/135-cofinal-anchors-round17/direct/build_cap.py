#!/usr/bin/env python3
"""Signed pooled-cap compiler. All inputs are literal, pinned round15 data."""
from pathlib import Path
import argparse, copy, hashlib, json, re
import terminal_elimination as E
import factor_horn as F
import build_signed as S
import translate_coordinates as T
add,neg,V=F.add,F.neg,F.V
mul=E.multiply

def put(d,n,x):
 d.mkdir(parents=True,exist_ok=True);(d/n).write_bytes(E.canonical_bytes(x))
def sha(x):return hashlib.sha256(E.canonical_bytes(x)).hexdigest()
def sc(p,k):return {m:k*c for m,c in p.items()}
def build(rawdir,out,cap=16,ys_only=False,odd_frame=False,odd_comparison=False,strong_cap=False,cofinal=False,self_radix=False,sparse=False,semantic_anchor=False,signed_center=False,odd_auxiliary=False,squared_anchor=False,orientation_first=False,pool_width=0,separate_sign_pool=False,strict_budget=False):
 raw=json.loads((rawdir/'raw_audit_input.json').read_text());original=json.loads((rawdir/'equation.json').read_text())
 pre=copy.deepcopy(original);raw=copy.deepcopy(raw);architecture_changes=[]
 n0={v['name']:i for i,v in enumerate(pre['variables'])}
 if self_radix:
  N=n0['pow1.output'];B0=n0['choose0.output']
  reps=[i for i,v in enumerate(pre['variables']) if v['name'].startswith('crt.encoded.') or v['name']=='crt.encoded_index_minus_one']
  Hpoly=add({():1+len(reps)},*[V(i) for i in reps])
  newbase=len(pre['variables']);pre['variables'].append({'name':'self_radix.BH','kind':'gate'})
  pre['residuals'].append({'label':'self_radix.base_definition','terms':E.as_terms(add(V(newbase),neg(mul(V(B0),Hpoly))))})
  rawbase=len(raw['variables']);raw['variables'].append({'name':'self_radix.BH','kind':'gate'})
  raw['powers'][2]['base']=['v',rawbase]
  for ri,row0 in enumerate(pre['residuals']):
   p0=E.normalize(row0['terms']);repl=None
   if row0['label']=='base2.T_definition':
    # Original N^2 gate occurs only here and in the removed aggregate bound.
    oldsq=n0['mul.385'];repl=add(p0,V(oldsq),neg(mul(V(newbase),V(newbase))))
   elif row0['label']=='multiplication' and any(N in m and (n0['shared.A'] in m or n0['index1.Y'] in m) for m in p0):
    repl=E.substitute(p0,N,V(newbase))
   if repl is not None:
    newrow=dict(row0,terms=E.as_terms(repl));architecture_changes.append({'kind':'self_radix_row','row':ri,'old':row0,'new':newrow});pre['residuals'][ri]=newrow
  old=next(r for r in pre['residuals'] if r['label']=='crt.aggregate_representative_bound');architecture_changes.append({'kind':'remove_aggregate','old':old})
  pre['residuals']=[r for r in pre['residuals'] if r['label']!='crt.aggregate_representative_bound']
 if strict_budget:
  oldk=raw['powers'][1]['exponent'];oldx=raw['powers'][14]['exponent'];rawx=['v',next(i for i,v in enumerate(raw['variables']) if v['name']=='x')]
  for j in (1,2,14):raw['powers'][j]['exponent']=rawx
  for field in ('seeds','indices'):
   raw[field]=[sd for sd in raw[field] if sd['exponent']!=oldk]
   for sd in raw[field]:
    if sd['exponent']==oldx:sd['exponent']=rawx
  raw['amplification']['K']=rawx;raw['amplification']['budget']='x';raw['amplification']['derived_label_radix_budget']='ell*(t+1)<2F<x=K'
  raw['radix']['K']=rawx
  for rg in raw['ranges']:
   if rg[3] in ('crt.range.u','crt.range.vq'):rg[1]=rawx
  oldpair=[n0['index1.X'],n0['index1.Y']];newpair=[n0['index12.X'],n0['index12.Y']]
  def aywire(prefix,pair):
   nr=next(r for r in pre['residuals'] if r['label']==prefix+'.norm1')
   return next(m[0] for coef,m in nr['terms'] if coef==-1 and len(m)==2 and m[0]==m[1])
  olday=aywire('index1',oldpair);neway=aywire('index12',newpair)
  aliases=dict(zip(oldpair+[olday],newpair+[neway]));kept=[]
  for ri,rr in enumerate(pre['residuals']):
   p=E.normalize(rr['terms'])
   if rr['label']=='index1.norm1' or E.candidate(p,olday,False)==mul(V(n0['shared.A']),V(oldpair[1])):
    architecture_changes.append({'kind':'strict_delete','row':ri,'old':rr});continue
   pp=p
   for old,new in aliases.items():pp=E.substitute(pp,old,V(new))
   nr=dict(rr,terms=E.as_terms(pp))
   if nr!=rr:architecture_changes.append({'kind':'strict_alias','row':ri,'old':rr,'new':nr})
   kept.append(nr)
  pre['residuals']=kept
 source,budget=S.square_budget(pre,raw);source['domain']='unrestricted integers';source['variant']+=':signed_pooled_cap';source.pop('metrics',None)
 names={v['name']:i for i,v in enumerate(source['variables'])};calls=budget['power_calls'];W=names['shared.W'];A=names['shared.A']
 if cofinal:
  hv=len(source['variables']);source['variables'].append({'name':'cofinal.horizon_root','kind':'signed_witness'})
  source['residuals'].append({'label':'cofinal.horizon','terms':E.as_terms(add(V(names['t0']),neg(mul(V(hv),V(hv)))))})
  v0=V(names['pow0.output'])
  source['residuals'].append({'label':'cofinal.beta_base','terms':E.as_terms(add(V(names['y']),neg(mul(v0,v0)),v0))})
 rows=source['residuals']
 # The square budget alone has W>=2+t^2>=258 and dominates every signed atom.
 seeddata=[]
 for seed in raw['seeds']:
  ids=[j for j,p in enumerate(raw['powers']) if p['exponent']==seed['exponent']]
  x,y=[names[raw['variables'][a[1]]['name']] for a in seed['pair']]
  seeddata.append({'pair':[x,y],'exponent':calls[ids[0]]['exponent'],'calls':ids})
 deleted=[];kept=[]
 for ri,row in enumerate(rows):
  label=row['label']
  if (re.fullmatch(r'index\d+\.(index_at_most_Y|norm3|S_mod_U|R_mod_4Y)',label) or label.startswith('shared_index.')):
   deleted.append({'row':ri,'content':row})
  else:kept.append(row)
 source['residuals']=kept
 modifications=[]
 if odd_frame:
  z=names['shared.Zminus1']
  for ri,row in enumerate(source['residuals']):
   p=E.normalize(row['terms'])
   if any(z in m for m in p):
    nr=dict(row,terms=E.as_terms(E.substitute(p,z,sc(V(z),2))))
    modifications.append({'row':ri,'old':row,'new':nr});source['residuals'][ri]=nr
 def var(n,kind='signed_witness'):
  i=len(source['variables']);source['variables'].append({'name':'cap.'+n,'kind':kind});return i
 def row(n,p):
  if E.degree(p)>2:raise ValueError(('degree',n))
  source['residuals'].append({'label':'cap.'+n,'terms':E.as_terms(p)})
 def gate(n,p):
  i=var(n,'gate');row(n,add(V(i),neg(p)));return i
 # Reuse the semantic derived-label Pell seed when requested.
 anchor_seed=seeddata[-1] if semantic_anchor else None
 anchor_index=E.normalize(anchor_seed['exponent']) if semantic_anchor else V(W)
 if semantic_anchor:
  U,Y=anchor_seed['pair']
 else:
  U,Y=[var(n) for n in ('U','Y')]
 H,J,C,R,B,d,e,f,g,h=[var(n) for n in ('H','J','S','R','B','d','e','f','g','h')]
 normpairs=[('common',H,J)] if semantic_anchor else [('main',U,Y),('common',H,J)]
 for n,x,y in normpairs:
  ay=gate(n+'_Ay',mul(V(A),V(y)))
  row(n+'_norm',add(mul(V(x),V(x)),mul(V(y),V(y)),neg(mul(V(ay),V(ay))),{():-1}))
 br=gate('BR',mul(V(B),V(R)))
 row('comparison_norm',add(mul(V(C),V(C)),mul(V(R),V(R)),neg(mul(V(br),V(br))),{():-1}))
 y2=gate('Y2',mul(V(Y),V(Y)))
 row('common_multiple',add(V(J),neg(mul(V(y2),add(sc(V(e),2 if odd_auxiliary else 1),{():1})))))
 factor=add(sc(V(d),2),{():1}) if odd_comparison else add(V(d),{():1})
 row('comparison_constructor',add(V(B),{():-1},sc(mul(V(J),factor),-4)))
 row('comparison_modulus',add(V(B),neg(V(A)),neg(mul(V(H),V(f)))))
 row('abscissa_residue',add(V(C),neg(V(U)),neg(mul(V(H),V(g)))))
 row('index_residue',add(V(R),neg(anchor_index),sc(mul(V(Y),V(h)),-4)))
 pooled_groups=[]
 width=pool_width or len(seeddata)
 for lo in range(0,len(seeddata),width):
  ids=list(range(lo,min(lo+width,len(seeddata))))
  kinds=['y','x'] if separate_sign_pool and not ys_only else ['y' if ys_only else 'both']
  for kind in kinds:
   pooled={}
   for si in ids:
    sd=seeddata[si];x,y=sd['pair']
    if kind in ('y','both'):
     delta=add(V(y),neg(E.normalize(sd['exponent'])));pooled=add(pooled,mul(delta,delta))
    if kind in ('x','both'):pooled=add(pooled,mul(add(V(x),{():-1}),add(V(x),{():-1})))
   pooled_groups.append({'indices':ids,'kind':kind,'polynomial':E.as_terms(pooled)})
 q=None
 if sparse:
  for i,sd in enumerate(seeddata):
   qi=var('residue_'+str(i));row('index_residue_'+str(i),add(V(sd['pair'][1]),neg(E.normalize(sd['exponent'])),neg(mul(add(V(A),{():-1}),V(qi)))))
   if not ys_only:
    qi=var('sign_residue_'+str(i));row('sign_residue_'+str(i),add(V(sd['pair'][0]),{():-1},neg(mul(add(V(A),{():-1}),V(qi)))))
 else:
  for gi,group in enumerate(pooled_groups):
   suffix='' if len(pooled_groups)==1 else '_'+str(gi)
   qi=var('pooled_quotient'+suffix);group['quotient']=qi
   row('pooled_index_residue'+suffix,add(E.normalize(group['polynomial']),neg(mul(add(V(A),{():-1}),V(qi)))))
  q=pooled_groups[0]['quotient'] if len(pooled_groups)==1 else None
 # Front sign basis, excluding predicates recovered only after the Pell semantics.
 pats=[r'index\d+\..*',r'shared_index\..*',r'pow\d+\.(quotient|output)',r'base\d+\.T',r'index_addition\.D',r'range\d+\..*',r'choose\d+\.(high|remainder|rslack)',r'crt\.(nonnegative_quotient|index_quotient)',r'endpoint\.(u0|ut)',r'y',r'fact0\.output',r'cap\..*']
 if orientation_first:
  if ys_only or not squared_anchor:raise ValueError('orientation-first requires both-sign pooling and squared anchor')
  pats.extend([r'x',r'crt\.encoded\..*',r'crt\.encoded_index_minus_one'])
 if signed_center:pats.append(r'shared\.A')
 if odd_frame:pats.append(r'shared\.Zminus1')
 if cofinal:pats.extend([r't0',r'endpoint\.r0',r'cofinal\..*'])
 if self_radix:pats.append(r'crt\.aggregate_representative_slack')
 exempt={i for i,v in enumerate(source['variables']) if any(re.fullmatch(p,v['name']) for p in pats)}
 proof=S.inference(source,exempt,[W]);guards=[{'kind':'front_nonnegative','expression':E.as_terms(V(i)),'coordinate':i} for i in proof['guard_indices']]
 # Every ordinary digit denominator is positive after power recovery; product suffices.
 pairs=[]
 for ri,r in enumerate(source['residuals']):
  if not (r['label'].endswith('.remainder_bound') and r['label']!='fact0.remainder_bound'):continue
  p=E.normalize(r['terms']);pair=[m[0] for m,c in p.items() if len(m)==1 and c==-1 and (source['variables'][m[0]]['name'].endswith('.remainder') or source['variables'][m[0]]['name'].endswith('.slack') or source['variables'][m[0]]['name'].endswith('.rslack'))]
  if len(pair)!=2:raise ValueError(('pair',r))
  guards.append({'kind':'postsemantic_interval','expression':E.as_terms(mul(V(pair[0]),V(pair[1]))),'pair':pair,'bound_row':ri});pairs.append({'row':ri,'pair':pair})
 if not odd_auxiliary:guards += [{'kind':'anchor_common_multiplier','expression':E.as_terms(V(e))}]
 if not strong_cap:guards.append({'kind':'anchor_index_bound','expression':E.as_terms(add(V(Y),neg(V(W))))})
 if not odd_comparison:guards.append({'kind':'anchor_comparison_multiplier','expression':E.as_terms(V(d))})
 capexpr=add(mul(V(Y),V(Y)) if squared_anchor else (V(Y) if strong_cap else V(y2)),neg(mul(anchor_index,anchor_index)) if squared_anchor else (neg(anchor_index) if strong_cap else {}),{():-1},* [neg(mul(V(sd['pair'][1]),V(sd['pair'][1]))) for sd in seeddata if not (semantic_anchor and sd is anchor_seed)])
 guards.append({'kind':'shared_square_cap','expression':E.as_terms(capexpr)})
 guarded=copy.deepcopy(source)
 for j,guard in enumerate(guards):
  aux=list(range(len(guarded['variables']),len(guarded['variables'])+3));a,b,c=aux
  guarded['variables'] += [{'name':f'guard{j}.{s}','kind':'integer_guard'} for s in ('a','b','c')]
  p=add(E.normalize(guard['expression']),{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})
  guard.update({'auxiliary':aux,'row':len(guarded['residuals'])})
  guarded['residuals'].append({'label':f'domain_guard.{j}','terms':E.as_terms(p)})
 factored,fc=F.transform(guarded)
 projected,pc,metrics=E.optimize(factored,max_support=cap);receipt=E.verify(factored,projected,pc)
 shifts={i:-1 for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'].endswith('minus1')}
 for i,v in enumerate(projected['variables']):
  if v['name']=='t0':shifts[i]=-16
 final=T.translate(projected,shifts);poly=E.expand(final)
 metrics={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':max(len(m) for c,m in poly['terms']),'monomials':len(poly['terms']),'height':max(abs(c) for c,m in poly['terms']),'row_height':max(abs(c) for r in final['residuals'] for c,m in r['terms']),'guards':len(guards),'main_pairs':len(seeddata),'ys_only':ys_only,'odd_frame':odd_frame,'odd_comparison':odd_comparison,'strong_cap':strong_cap,'cofinal':cofinal,'self_radix':self_radix,'sparse':sparse,'semantic_anchor':semantic_anchor,'signed_center':signed_center,'odd_auxiliary':odd_auxiliary,'squared_anchor':squared_anchor,'anchor_index':E.as_terms(anchor_index),'orientation_first':orientation_first,'pool_width':pool_width,'separate_sign_pool':separate_sign_pool,'pooled_groups':pooled_groups,'strict_budget':strict_budget}
 cert={'schema':'signed_pooled_cap_v1','original_sha256':sha(original),'raw_sha256':sha(raw),'architecture_changes':architecture_changes,'square_budget':budget,'seed_data':seeddata,'deleted_constraints':deleted,'modifications':modifications,'source_sha256':sha(source),'sign_inference':proof,'guards':guards,'pairs':pairs,'cap_variables':dict(zip(('U','Y','H','J','S','R','B','d','e','f','g','h'),(U,Y,H,J,C,R,B,d,e,f,g,h))),'cap_square_variable':y2,'pooled_quotient':q,'ys_only':ys_only,'odd_frame':odd_frame,'odd_comparison':odd_comparison,'strong_cap':strong_cap,'cofinal':cofinal,'self_radix':self_radix,'sparse':sparse,'semantic_anchor':semantic_anchor,'signed_center':signed_center,'odd_auxiliary':odd_auxiliary,'squared_anchor':squared_anchor,'anchor_index':E.as_terms(anchor_index),'orientation_first':orientation_first,'pool_width':pool_width,'separate_sign_pool':separate_sign_pool,'pooled_groups':pooled_groups,'strict_budget':strict_budget}
 trans={'schema':'integral_translation_v1','input_sha256':sha(projected),'output_sha256':sha(final),'shifts':[[i,s] for i,s in shifts.items()],'convention':'old=new+shift'}
 for n,o in [('input_raw.json',raw),('input_equation.json',original),('source.json',source),('guarded.json',guarded),('transform_certificate.json',cert),('factored_source.json',factored),('factorization_certificate.json',fc),('projected.json',projected),('projection_certificate.json',pc),('PROJECTION_CHECK.json',receipt),('translation_certificate.json',trans),('equation.json',final),('expanded_polynomial.json',poly),('METRICS.json',metrics)]:put(out,n,o)
 print(json.dumps({k:v for k,v in metrics.items() if k not in ('pooled_groups','anchor_index')},indent=2));return metrics
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('raw',type=Path);p.add_argument('out',type=Path);p.add_argument('--cap',type=int,default=16);p.add_argument('--ys-only',action='store_true');p.add_argument('--odd-frame',action='store_true');p.add_argument('--odd-comparison',action='store_true');p.add_argument('--strong-cap',action='store_true');p.add_argument('--cofinal',action='store_true');p.add_argument('--self-radix',action='store_true');p.add_argument('--sparse',action='store_true');p.add_argument('--semantic-anchor',action='store_true');p.add_argument('--signed-center',action='store_true');p.add_argument('--odd-auxiliary',action='store_true');p.add_argument('--squared-anchor',action='store_true');p.add_argument('--orientation-first',action='store_true');p.add_argument('--pool-width',type=int,default=0);p.add_argument('--separate-sign-pool',action='store_true');p.add_argument('--strict-budget',action='store_true');a=p.parse_args();build(a.raw,a.out,a.cap,a.ys_only,a.odd_frame,a.odd_comparison,a.strong_cap,a.cofinal,a.self_radix,a.sparse,a.semantic_anchor,a.signed_center,a.odd_auxiliary,a.squared_anchor,a.orientation_first,a.pool_width,a.separate_sign_pool,a.strict_budget)
