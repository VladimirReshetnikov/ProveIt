#!/usr/bin/env python3
"""Safe natural composition of selector projection and endpoint penalties."""
import argparse,hashlib,itertools,json,random,types
from collections import Counter
from pathlib import Path
PINS={'three_mass_endpoint_penalties.py':'7010ab32c2ac44a84ea61f4393b826cdc1401c654f20364dbad7f694e3eb605c',
      'three_mass_selector_projection.py':'8129ec4da0aded05c98993b7575eb3ccfe42ee908c5d15c18a748a8b53d874b8'}
def need(v,s):
 if not v:raise ValueError(s)
def load(root):
 modules=[]
 for name,pin in PINS.items():
  data=(Path(root)/name).read_bytes();need(hashlib.sha256(data).hexdigest()==pin,'Pinned composition dependency')
  m=types.ModuleType('_composition_'+name[:-3]);m.__file__=str(Path(root)/name);exec(compile(data,m.__file__,'exec'),m.__dict__);modules.append(m)
 return modules

def emit(S,R,E,cert,mode='direct',implicit=None,endpoints='both'):
 need(type(endpoints)is str and endpoints in ('none','initial','terminal','both'),'Endpoint mode')
 need(type(mode)is str and mode in ('direct','factored','horner'),'Gate mode')
 S.emit(cert);f,groups,replace=R.layout(S,cert,implicit);B=len(f['branches'])
 old,new=E.endpoint_forms(S,cert)
 chosen={k:v for k,v in new.items() if endpoints=='both' or endpoints=='initial' and k=='step-0:control' or endpoints=='terminal' and k=='terminal:halt'}
 weights=[1]*f['horizon'];negative_counts=[0]*f['horizon']
 for label,form in chosen.items():
  t=0 if label=='step-0:control' else f['horizon']-1
  if B and form.get(groups[t][1]['e'],0):negative_counts[t]+=1
 for t,r in enumerate(negative_counts):weights[t]=2 if r==2 else 1
 d=S.DAG();N0=d.op('+','x',1);cache={}
 def aff(form):
  form={k:v for k,v in sorted(form.items()) if v};key=tuple(form.items())
  if key in cache:return cache[key]
  constant=form.get('',0)-form.get('x',0);by={}
  for n,c in form.items():
   if n:by.setdefault(c,[]).append(N0 if n=='x' else n)
  terms=[constant] if constant else []
  for c,ts in sorted(by.items(),key=lambda kv:(kv[0]<0,abs(kv[0]))):
   v=d.sum(ts);terms.append(v if c==1 else ('-',v) if c==-1 else d.op('*',c,v))
  out=0
  for t in terms:out=d.op('-',out,t[1]) if type(t)is tuple else d.op('+',out,t)
  cache[key]=out;return out
 squares=[];ports={'N0':N0,'squares':[],'projected_gates':[],'endpoint_penalty':0}
 for row in cert['squares']:
  if row['label']in chosen:continue
  form=R.projected_form(S,cert,row['affine'],replace)
  if B and row['label'].endswith(':one-hot'):
   need(not form,'Projected one-hot row');continue
  p=aff(form);ports['squares'].append([row['label'],p]);squares.append(d.op('*',p,p))
 gates=[]
 for t,(others,last,terms) in enumerate(groups):
  if last is None:ports['projected_gates'].append(0);gates.append(0);continue
  sm=aff(terms);vl='v'+last['u'][1:];w=weights[t]
  if mode=='horner' and B==2:
   r=others[0];e=r['e'];v='v'+r['u'][1:];complement=aff({'':1,e:-1})
   we=e if w==1 else d.op('+',e,e)
   g=d.op('+',d.op('*',complement,d.op('-',d.op('*',complement,v),we)),d.op('*',e,vl))
  else:
   inner=[]
   for r in others:
    complement=aff({'':1,r['e']:-1});v='v'+r['u'][1:]
    inner.append(d.op('*',d.op('*',complement,complement),v))
   sm1=aff(S.addform(terms,{'':-1}))
   if w==2:sm1=d.op('+',sm1,sm1)
   if mode=='factored':inner.append(d.op('*',sm,d.op('+',sm1,vl)))
   else:inner.extend([d.op('*',sm,sm1),d.op('*',sm,vl)])
   g=d.sum(inner)
  gates.append(g);ports['projected_gates'].append(g)
 projected_penalty=S.addform(*(R.projected_form(S,cert,form,replace) for form in chosen.values()))
 penalty=aff(projected_penalty);ports['endpoint_penalty']=penalty
 output=d.sum(squares+gates+[penalty])
 oldvars=[('v'+n[1:]) if n.startswith('u_') else n for n in cert['variables']]
 variables=[n for n in oldvars if n not in replace];p=d.finish(output,variables,ports)
 p.update(mode=mode,endpoints=endpoints,implicit_selectors=list(replace),restoration_forms=replace,
          horizon=f['horizon'],branches=B,natural_witnesses=2*B*f['horizon']-len(replace),
          removed_endpoint_squares={k:old[k] for k in chosen},endpoint_penalties=chosen,
          barrier_weights=weights,implicit_forbidden_penalty_counts=negative_counts)
 return p

def expected(S,R,cert,p):
 out=R.expected(S,cert,p)
 for label,old in p['removed_endpoint_squares'].items():
  c=S.formpoly(R.projected_form(S,cert,old,p['restoration_forms']))
  k=S.formpoly(R.projected_form(S,cert,p['endpoint_penalties'][label],p['restoration_forms']))
  out=S.padd(S.padd(out,S.pmul(c,c),-1),k)
 for t,rows in enumerate(cert.get('forward_certificate',cert)['steps']):
  if p['barrier_weights'][t]==2:
   s=S.formpoly({r['e']:1 for r in rows if r['e']not in p['restoration_forms']})
   out=S.padd(out,S.pmul(s,S.padd(s,{():1},-1)))
 return out

def verify(root,repo):
 E,R=load(root);S=E.parent(repo);sources,archives=S.source_bytes(repo);counts=Counter();records=[];rng=random.Random(80331)
 with S.subjects(sources) as(C,CT):
  cases=[(name,h,clean,S.make_case(C,CT,name,h,clean)) for name,h,clean in E.test_cases()]
  m=C.Machine(('s','h','z'),'h',(C.Instruction('s','h','zero',1),C.Instruction('z','z','nop',0)))
  trap=C.export_certificate(m,'s',1,{'mode':'free_raw','name':'x'},{'mode':'free','name':'y'},{'mode':'free','name':'T'})
  cases.append(('double-endpoint-trap',1,False,trap))
  for name,h,clean,c in cases:
   B=len(c.get('forward_certificate',c)['branches']);packets={};baselines={}
   for implicit in range(B) if B else (-1,):
    for mode in ('direct','factored','horner'):
     base=R.emit(S,c,mode,implicit);same=emit(S,R,E,c,mode,implicit,'none')
     need(base['source']==same['source'] and base['output']==same['output'] and base['ledger']==same['ledger'],'Literal projected baseline equality')
     baselines[f'{implicit}:{mode}']=base;counts['literal_baselines']+=1
     for endpoint in ('initial','terminal','both'):
      p=emit(S,R,E,c,mode,implicit,endpoint);key=f'{implicit}:{mode}:{endpoint}';packets[key]=p
      polynomial=S.sourcepoly(p)
      need(polynomial==expected(S,R,c,p),'Full coefficient correction')
      need(max(map(len,polynomial),default=0)==(3 if B>=2 and h else 2),'Exact complete degree')
      need(p['variables']==base['variables'],'Same projected coordinates')
      counts['full_coefficient_corrections']+=1
      for sample in range(2):
       a={n:rng.randrange(-3,4) for n in p['variables']};restored=R.restore(S,c,p,a)
       corr=sum(S.ev(f,restored) for f in p['endpoint_penalties'].values())-sum(S.ev(f,restored)**2 for f in p['removed_endpoint_squares'].values())
       for t,rows in enumerate(c.get('forward_certificate',c)['steps']):
        if p['barrier_weights'][t]==2:
         s=sum(a[r['e']] for r in rows if r['e']not in p['restoration_forms']);corr+=s*(s-1)
       need(S.evaluate(p,a)==S.evaluate(base,a)+corr,'Signed complete correction');counts['signed_corrections']+=1
      for x in (0,4):
       try:o=CT.make_clean_witness(c,{'x':x}) if clean else C.make_witness(c,{'x':x})
       except ValueError:continue
       mass=S.push(c,o);a={n:v for n,v in mass.items() if n not in p['restoration_forms']}
       need(S.evaluate(p,a)==0 and R.restore(S,c,p,a)==mass,'Natural forward graph');counts['natural_forward_zeros']+=1
   bestold=min(baselines,key=lambda k:baselines[k]['ledger']['total']);bestnew=min(packets,key=lambda k:packets[k]['ledger']['total'])
   keep=(name,h,clean) in [('incdec',2,False),('incdec',2,True),('incchain3',3,False),('incchain3',3,True),('zero3',1,False),('empty',0,True),('double-endpoint-trap',1,False)]
   records.append(dict(fixture=name,horizon=h,clean=clean,branches=B,best_baseline=bestold,best_new=bestnew,
                       old_ledger=baselines[bestold]['ledger'],new_ledger=packets[bestnew]['ledger'],
                       natural_witnesses=packets[bestnew]['natural_witnesses'],degree=max(map(len,S.sourcepoly(packets[bestnew])),default=0),
                       all_ledgers={k:p['ledger'] for k,p in packets.items()},
                       complete_best_old=baselines[bestold] if keep else None,complete_best_new=packets[bestnew] if keep else None,
                       certificate=c if keep else None))
  # Exhaust arbitrary endpoint-support masks, including overlap at horizon one.
  for B in range(1,5):
   for es in itertools.product(range(4),repeat=B-1):
    s=sum(es);full=es+(1-s,)
    for masks in itertools.product(range(1<<B),repeat=2):
     r=sum(bool(mask&(1<<(B-1))) for mask in masks);w=2 if r==2 else 1
     K=sum(e for mask in masks for j,e in enumerate(full) if mask&(1<<j))
     for vs in itertools.product(range(2),repeat=B):
      G=w*s*(s-1)+sum((1-e)**2*v for e,v in zip(es,vs))+s*vs[-1]
      out=G+K
      want=s in (0,1) and all(v==0 for e,v in zip(full,vs) if e==0) and all(not(mask&(1<<j)) for mask in masks for j,e in enumerate(full) if e==1)
      need(out>=0 and (out==0)==want,'Grouped natural gate and endpoints')
      counts['masked_natural_gadget_cases']+=1
  fake={'x':2,'e_0_0':1,'e_0_1':1,'v_0_0':1,'v_0_1':1,'v_0_2':0,'y':3,'T':584}
  p=emit(S,R,E,trap,'direct',2,'both');base=R.emit(S,trap,'direct',2);restored=R.restore(S,trap,p,fake)
  naive=S.evaluate(base,fake)+sum(S.ev(f,restored) for f in p['endpoint_penalties'].values())-sum(S.ev(f,restored)**2 for f in p['removed_endpoint_squares'].values())
  need(naive==0 and S.evaluate(p,fake)==2 and p['barrier_weights']==[2],'Actual full one-step counterfeit rejected')
  counterexample=dict(assignment=fake,naive_score=0,safe_score=2,projected_parent_score=S.evaluate(base,fake),restored_implicit_selector=-1,
                      meaning='Raw N0=3 cannot pass the source prime-three zero guard; both endpoint penalties would cancel the single barrier.')
  # Complete natural tuples with all supplied endpoints natural; fixtures include
  # the horizon-one double-negative trap and a true two-step execution.
  for name,h,implicit in [('incdec',2,0),('double-endpoint-trap',1,2),('zero3',1,0)]:
   c=trap if name=='double-endpoint-trap' else S.make_case(C,CT,name,h,False)
   p=emit(S,R,E,c,'horner',implicit,'both');original=S.emit(c);core=[n for n in p['variables'] if n not in ('x','y','T')]
   for vs in itertools.product(range(3),repeat=len(core)):
    for x in range(3):
     a=dict(zip(core,vs));a['x']=x;mass=R.restore(S,c,p,{**a,'y':0,'T':0});off=S.pull(c,mass)
     a['y']=S.ev(c['final_N'],off);a['T']=S.ev(c['physical_time'],off)
     if min(a.values())<0:continue
     value=S.evaluate(p,a);need(value>=0,'Full natural nonnegative output');counts['full_natural_tuples']+=1
     if value==0:
      mass=R.restore(S,c,p,a);need(min(mass.values())>=0 and S.evaluate(original,mass)==0,'Exact natural inverse zero')
      counts['full_natural_inverse_zeros']+=1
 return dict(status='PASS_SAFE_PROJECTED_ENDPOINTS',dependency_pins=PINS,parent_sha256=E.PARENT_SHA,archive_pins=archives,
             counts=dict(counts),cases=records,one_step_unsafe_counterexample=counterexample,
             scope='Complete fixed-external-horizon paid circuits. Natural-zero bijection under the selector restoration; exact polynomial correction. No same-polynomial or universal-bound claim.')

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=verify(a.root,a.repo)
 if a.expect:
  E,R=load(a.root);need(E.exact(r,json.loads(a.expect.read_text())),'Typed saved receipt differs')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],examples=[{k:v for k,v in c.items() if k in ('fixture','horizon','clean','old_ledger','new_ledger','natural_witnesses','degree','best_new')} for c in r['cases'] if c['complete_best_new']]),indent=2))
