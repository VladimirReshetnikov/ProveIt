#!/usr/bin/env python3
"""Selective even-index compiler with residue-one orientation; literal-data input only."""
from pathlib import Path
import argparse,copy,hashlib,json,re
from collections import defaultdict
import terminal_elimination as E
import build_signed as S
import factor_horn as F
import translate_coordinates as T

def put(d,n,x):
 d.mkdir(parents=True,exist_ok=True);(d/n).write_bytes(E.canonical_bytes(x))
def hashobj(x):return hashlib.sha256(E.canonical_bytes(x)).hexdigest()
def scale(p,c):return {m:c*v for m,v in p.items()}
def add(*ps):return F.add(*ps)
def V(i):return F.V(i)
def neg(p):return F.neg(p)
def compile(rawdir,out,cap=16,pair_fusion=True,reparam=False):
 raw=json.loads((rawdir/'raw_audit_input.json').read_text());original=json.loads((rawdir/'equation.json').read_text())
 source,budget=S.square_budget(original,raw);source['domain']='unrestricted integers';source['variant']+=':residue_even_v1';source.pop('metrics',None)
 interval_reference=copy.deepcopy(source)
 names={v['name']:i for i,v in enumerate(source['variables'])}
 calls=budget['power_calls'];q=E.normalize(raw_to_affine(raw['radix'],raw,source)) if False else None
 # The unique successor-base and radix used by all binomial/range powers.
 pluscalls=[i for i,p in enumerate(calls) if E.normalize(p['base']).get(())==1 and len(p['base'])==2 and i>=3]
 bases={tuple(tuple([c,*m]) for c,m in calls[i]['base']) for i in pluscalls}
 if len(bases)!=1:raise ValueError(('successor radix base',bases))
 baseplus=E.normalize(calls[pluscalls[0]]['base']);q=add(baseplus,{():-1})
 if E.degree(q)!=1 or len(q)!=1:raise ValueError('radix is not a coordinate')
 t=tuple(raw['powers'][0]['exponent']);K=tuple(raw['powers'][1]['exponent'])
 excluded={t,K};seeds=[];changes=[]
 for s in raw['seeds']:
  exp=tuple(s['exponent']);pair=[names[raw['variables'][a[1]]['name']] for a in s['pair']]
  if exp in excluded:continue
  ids=[i for i,p in enumerate(raw['powers']) if tuple(p['exponent'])==exp]
  if not ids:raise ValueError('seed with no supporting power')
  k=E.normalize(calls[ids[0]]['exponent']);prefix=source['variables'][pair[0]]['name'].split('.')[0]
  hits=[i for i,r in enumerate(source['residuals']) if r['label']==prefix+'.R_mod_4Y']
  if len(hits)!=1:raise ValueError('missing index residue')
  rid=hits[0];old=copy.deepcopy(source['residuals'][rid]);new=dict(old,terms=E.as_terms(add(E.normalize(old['terms']),neg(k))))
  source['residuals'][rid]=new;changes.append({'kind':'double_seed_index','row':rid,'old':old,'new':new})
  seeds.append({'exponent':s['exponent'],'pair':pair,'prefix':prefix,'calls':ids,'affine_exponent':E.as_terms(k)})
 selected={i for s in seeds for i in s['calls']};orient=[]
 for i in sorted(selected):
  call=calls[i];m=E.normalize(call['output']);base=E.normalize(call['base'])
  if len(m)!=1 or E.degree(m)!=1:raise ValueError('output not coordinate')
  rid=next(j for j,r in enumerate(source['residuals']) if r['label']==f'pow{i}.power_congruence')
  old=copy.deepcopy(source['residuals'][rid]);p=E.normalize(old['terms'])
  if not all(p.get(mon)==-c for mon,c in m.items()):raise ValueError('wrong output port')
  new=dict(old,terms=E.as_terms(add(p,m,neg(E.multiply(m,m)))))
  source['residuals'][rid]=new;changes.append({'kind':'square_output','call':i,'row':rid,'old':old,'new':new})
  if base==baseplus:
   if reparam:
    hits=[]
    for rr,row in enumerate(source['residuals']):
     rp=E.normalize(row['terms'])
     if not all(rp.get(mon)==c for mon,c in m.items()):continue
     rems=[mon[0] for mon,c in rp.items() if len(mon)==1 and c==-1 and source['variables'][mon[0]]['name'].endswith('.remainder')]
     if len(rems)==1:hits.append((rr,rems[0]))
    if len(hits)!=1:raise ValueError(('terminal remainder binding',i,hits))
    digitrow,u=hits[0];sub=add({():1},E.multiply(q,V(u)));subchanges=[]
    for rr,row in enumerate(source['residuals']):
     rp=E.normalize(row['terms'])
     if not any(u in mon for mon in rp):continue
     np=E.substitute(rp,u,sub)
     if E.degree(np)>2:raise ValueError(('remainder degree',i,rr))
     oldrow=copy.deepcopy(row);newrow=dict(row,terms=E.as_terms(np));source['residuals'][rr]=newrow
     subchanges.append({'row':rr,'old':oldrow,'new':newrow})
    orient.append({'call':i,'kind':'residue_reparameterization','quotient':u,'digit_row':digitrow,'radix':E.as_terms(q),'output':call['output'],'old_remainder':E.as_terms(sub),'changes':subchanges})
   else:
    u=len(source['variables']);source['variables'].append({'name':f'residue_one.pow{i}.quotient','kind':'signed_witness'})
    r={'label':f'residue_one.pow{i}','terms':E.as_terms(add(m,{():-1},neg(E.multiply(q,V(u)))))}
    source['residuals'].append(r);orient.append({'call':i,'kind':'residue_one','quotient':u,'row':len(source['residuals'])-1,'radix':E.as_terms(q),'output':call['output']})
  elif base==q:
   orient.append({'call':i,'kind':'nonnegative_remainder_bound','output':call['output']})
  else:raise ValueError(('unexpected selected base',i,base))
 W=budget['frame_variable'];rid=budget['frame_row'];old=copy.deepcopy(source['residuals'][rid]);p=E.normalize(old['terms']);new=dict(old,terms=E.as_terms(add(scale(p,2),neg(V(W)))))
 source['residuals'][rid]=new;changes.append({'kind':'double_square_frame','row':rid,'old':old,'new':new})
 # Natural signs are required only at the original semantic interface.
 pats=[r'index[0-9]+\.(?:S|R|Squotient|Rquotient|X|Y)$',r'pow[0-9]+\.(?:quotient|output)$',r'shared_index\.(?:Bquotient|U|Vquotient_minus1)$',r'base[0-9]+\.T$',r'index_addition\.D$',r'range[0-9]+\.quotient$',r'choose[0-9]+\.high$',r'crt\.nonnegative_quotient$',r'endpoint\.(?:u0|ut)$',r'y$',r'M0$',r'crt\.index_quotient$',r'residue_one\..*']
 exempt={i for i,v in enumerate(source['variables']) if any(re.fullmatch(p,v['name']) for p in pats)}
 exempt|={names[s['prefix']+'.YminusK'] for s in seeds}
 commonV=names['shared_index.V'];proof=S.inference(source,exempt,[W,commonV]);guards=set(proof['guard_indices'])
 # Pair replacement uses only literal interval identities and guarded anchors.
 groups=defaultdict(list)
 for rid,r in enumerate(interval_reference['residuals']):
  p=E.normalize(r['terms']);pairs=[m[0] for m,c in p.items() if len(m)==1 and c==-1 and m[0] in guards]
  if len(pairs)!=2 or p.get(())!=-1:continue
  a,b=sorted(pairs);upper=add(p,V(a),V(b),{():1})
  if E.degree(upper)>1 or any(c<0 for c in upper.values()):continue
  groups[tuple(sorted(upper.items()))].append((rid,a,b))
 paired=[]
 if pair_fusion:
  for upper,rows in sorted(groups.items()):
   if len(rows)<2:continue
   anchor=rows[0]
   for rid,a,b in rows[1:]:
    if a not in guards or b not in guards:raise ValueError('repeated pair')
    guards-={a,b};paired.append({'row':rid,'pair':[a,b],'anchor_row':anchor[0],'anchor':[anchor[1],anchor[2]],'upper':E.as_terms(dict(upper))})
 guard_specs=[{'kind':'nonnegative','expression':E.as_terms(V(i)),'coordinate':i} for i in sorted(guards)]
 guard_specs+=[{'kind':'positive_common_V','expression':E.as_terms(add(V(commonV),{():-1}))}]
 guard_specs+=[{'kind':'paired_interval','expression':E.as_terms(E.multiply(V(p['pair'][0]),V(p['pair'][1]))),'pair':p['pair']} for p in paired]
 guarded=copy.deepcopy(source)
 for j,g in enumerate(guard_specs):
  a,b,c=range(len(guarded['variables']),len(guarded['variables'])+3)
  guarded['variables'] += [{'name':f'guard{j}.{s}','kind':'integer_guard'} for s in ['a','b','c']]
  row={'label':f'domain_guard.{j}','terms':E.as_terms(add(E.normalize(g['expression']),{(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1}))}
  guarded['residuals'].append(row);g.update({'auxiliary':[a,b,c],'row':len(guarded['residuals'])-1})
 pruned=copy.deepcopy(guarded);drop=[]
 for seed in seeds:
  v=names[seed['prefix']+'.YminusK'];hits=[ri for ri,row in enumerate(pruned['residuals']) if any(v in mon for co,mon in row['terms'])]
  if len(hits)!=1:raise ValueError(('slack escaped',v,hits))
  ri=hits[0];rest=E.candidate(E.normalize(pruned['residuals'][ri]['terms']),v,False)
  if rest is None:raise ValueError('slack not monic')
  drop.append({'row':ri,'variable':v,'restoration':E.as_terms(rest)})
 deleted={x['row'] for x in drop};pruned['residuals']=[r for ri,r in enumerate(pruned['residuals']) if ri not in deleted]
 pruning={'input_sha256':hashobj(guarded),'output_sha256':hashobj(pruned),'dropped_private_slacks':drop}
 fcsource,fc=F.transform(pruned);projected,pc,metrics=E.optimize(fcsource,max_support=cap);receipt=E.verify(fcsource,projected,pc)
 shifts={i:-1 for i,v in enumerate(projected['variables']) if v['name'].startswith('crt.encoded') or v['name'] in ('t0','M0') or v['name'].endswith('minus1')}
 tconstant=E.normalize(calls[0]['exponent']).get((),0)
 for i,v in enumerate(projected['variables']):
  if v['name']=='t0':shifts[i]=-tconstant
 final=T.translate(projected,shifts);poly=E.expand(final)
 metrics={'variables':len(final['variables']),'rows':len(final['residuals']),'degree':max(len(m) for c,m in poly['terms']),'monomials':len(poly['terms']),'height':max(abs(c) for c,m in poly['terms']),'row_height':max(abs(c) for r in final['residuals'] for c,m in r['terms']),'guards':len(guard_specs),'doubled_seeds':len(seeds),'residue_one_guards':sum(o['kind']=='residue_one' for o in orient),'reparameterized_remainders':sum(o['kind']=='residue_reparameterization' for o in orient),'pair_fusions':len(paired)}
 cert={'schema':'selective_even_residue_one_v1','raw_sha256':hashobj(raw),'original_sha256':hashobj(original),'source_sha256':hashobj(source),'square_budget':budget,'seeds':seeds,'selected_calls':sorted(selected),'orientation':orient,'changes':changes,'sign_inference':proof,'paired_guards':paired,'guards':guard_specs,'undoubled_seed_exponents':[list(t),list(K)],'frame_factor':2,'reparameterization':reparam,'interval_reference_sha256':hashobj(interval_reference)}
 seed_positive=S.positive_seed_certificate(raw)
 seed_positive['conclusion']='Every original seed exponent is positive before power recovery. Doubling preserves positivity; the common auxiliary ordinate is separately guarded positive.'
 translation={'schema':'integral_translation_v1','input_sha256':hashobj(projected),'output_sha256':hashobj(final),'shifts':[[i,s] for i,s in shifts.items()],'convention':'old=new+shift'}
 for n,x in [('source.json',source),('positive_seed_certificate.json',seed_positive),('guarded.json',guarded),('pruned_source.json',pruned),('pruning_certificate.json',pruning),('transform_certificate.json',cert),('factored_source.json',fcsource),('factorization_certificate.json',fc),('projected.json',projected),('projection_certificate.json',pc),('translation_certificate.json',translation),('equation.json',final),('expanded_polynomial.json',poly),('METRICS.json',metrics),('PROJECTION_CHECK.json',receipt)]:put(out,n,x)
 print(json.dumps(metrics,indent=2));return metrics
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('raw',type=Path);p.add_argument('out',type=Path);p.add_argument('--cap',type=int,default=16);p.add_argument('--no-pair-fusion',action='store_true');p.add_argument('--reparam',action='store_true');a=p.parse_args();compile(a.raw,a.out,a.cap,not a.no_pair_fusion,a.reparam)
