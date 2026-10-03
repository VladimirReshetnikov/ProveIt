#!/usr/bin/env python3
"""Paid natural selector projection for the pinned three-mass source family."""
import argparse,copy,hashlib,itertools,json,random,types
from collections import Counter
from pathlib import Path
PARENT='three_mass_arithmetic.py'
PIN='d5607c6cd780d2110491171ec8aeca69e8b92dcff0f2f13eb614ed9ebaa6c7a0'
def need(b,s):
 if not b:raise ValueError(s)
def load(root):
 p=Path(root)/PARENT;raw=p.read_bytes();need(hashlib.sha256(raw).hexdigest()==PIN,'Parent source pin')
 m=types.ModuleType('_mass_projection_parent');m.__file__=str(p);exec(compile(raw,str(p),'exec'),m.__dict__);return m

def layout(S,cert,implicit=None):
 f=cert.get('forward_certificate',cert);B=len(f['branches']);h=f['horizon']
 if implicit is None:implicit=[B-1]*h
 elif type(implicit)is int:implicit=[implicit]*h
 need(type(implicit)is list and len(implicit)==h,'One implicit selector per step')
 if B:need(all(type(i)is int and 0<=i<B for i in implicit),'Implicit selector range')
 groups=[];replace={}
 for t,rows in enumerate(f['steps']):
  if not B:groups.append(([],None,{}));continue
  last=rows[implicit[t]];others=[r for i,r in enumerate(rows) if i!=implicit[t]]
  terms={r['e']:1 for r in others};replace[last['e']]=S.addform({'':1},S.scaled(terms,-1))
  groups.append((others,last,terms))
 return f,groups,replace

def projected_form(S,cert,form,replace):
 out=S.transform(form,S.pairs_for(cert));result={}
 for n,c in out.items():result=S.addform(result,S.scaled(replace[n],c) if n in replace else {n:c})
 return result

def emit(S,cert,mode='direct',implicit=None):
 need(mode in ('direct','factored','horner'),'Projection gate schedule')
 # Reuse only the authenticated prototype's explicit source-interface boundary.
 S.emit(cert)
 f,groups,replace=layout(S,cert,implicit);B=len(f['branches']);d=S.DAG();N0=d.op('+','x',1);cache={}
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
 squares=[];ports={'N0':N0,'squares':[],'projected_gates':[]}
 for row in cert['squares']:
  form=projected_form(S,cert,row['affine'],replace)
  if B and row['label'].endswith(':one-hot'):
   need(not form,'Eliminated selector row must vanish identically');continue
  p=aff(form);ports['squares'].append([row['label'],p]);squares.append(d.op('*',p,p))
 gates=[]
 for others,last,terms in groups:
  if last is None:ports['projected_gates'].append(0);gates.append(0);continue
  sm=aff(terms);vl='v'+last['u'][1:]
  if mode=='horner' and B==2:
   r=others[0];e=r['e'];v='v'+r['u'][1:];complement=aff({'':1,e:-1})
   g=d.op('+',d.op('*',complement,d.op('-',d.op('*',complement,v),e)),d.op('*',e,vl))
  else:
   inner=[]
   for r in others:
    complement=aff({'':1,r['e']:-1});v='v'+r['u'][1:]
    inner.append(d.op('*',d.op('*',complement,complement),v))
   sm1=aff(S.addform(terms,{'':-1}))
   if mode=='factored':inner.append(d.op('*',sm,d.op('+',sm1,vl)))
   else:inner.extend([d.op('*',sm,sm1),d.op('*',sm,vl)])
   g=d.sum(inner)
  gates.append(g);ports['projected_gates'].append(g)
 output=d.sum(squares+gates)
 oldvars=[('v'+n[1:]) if n.startswith('u_') else n for n in cert['variables']]
 variables=[n for n in oldvars if n not in replace]
 p=d.finish(output,variables,ports)
 p.update(mode=mode,implicit_selectors=list(replace),restoration_forms=replace,
          horizon=f['horizon'],branches=B,natural_witnesses=2*B*f['horizon']-len(replace))
 return p

def restore(S,cert,packet,new):
 old=dict(new)
 for n,form in packet['restoration_forms'].items():old[n]=S.ev(form,new)
 return old

def expected(S,cert,p):
 # Independent certificate-level identity: substituted old polynomial plus
 # S(S-1)+sum e_j(e_j-1)v_j at each projected step.
 rep=p['restoration_forms'];out={}
 def conv(f):return S.formpoly(projected_form(S,cert,f,rep))
 for row in cert['squares']:
  r=conv(row['affine']);out=S.padd(out,S.pmul(r,r))
 for row in cert['products']:out=S.padd(out,S.pmul(conv(row['left']),conv(row['right'])))
 f=cert.get('forward_certificate',cert)
 for rows in f['steps']:
  implicit=[r for r in rows if r['e']in rep]
  if not implicit:continue
  need(len(implicit)==1,'Unique implicit branch')
  others=[r for r in rows if r['e']not in rep];sumform={r['e']:1 for r in others}
  sp=S.formpoly(sumform);out=S.padd(out,S.pmul(sp,S.padd(sp,{():1},-1)))
  for r in others:
   ep={(r['e'],):1};vp={('v'+r['u'][1:],):1}
   out=S.padd(out,S.pmul(S.pmul(ep,S.padd(ep,{():1},-1)),vp))
 return out

def verify(root,repo):
 S=load(root);raw,pins=S.source_bytes(repo);rng=random.Random(80338);count=Counter();records=[]
 with S.subjects(raw) as (C,CT):
  cases=[('incdec',h,clean) for h in range(4) for clean in (False,True)]
  cases += [('incchain'+str(k),k,clean) for k in (1,2,3,4,5) for clean in (False,True)]
  cases += [('dec2',1,clean) for clean in (False,True)]
  cases += [(name,h,clean) for name in ('zero3','test3','empty') for h in (0,1,2) for clean in (False,True)]
  for name,h,clean in cases:
   cert=S.make_case(C,CT,name,h,clean);B=len(cert.get('forward_certificate',cert)['branches'])
   baseline={mode:S.emit(cert,'mass',mode) for mode in ('direct','factored')}
   variants={}
   for implicit in range(B) if B else (-1,):
    for mode in ('direct','factored','horner'):
     p=emit(S,cert,mode,implicit);want=expected(S,cert,p)
     need(S.sourcepoly(p)==want,'Complete coefficient identity with explicit correction')
     count['full_coefficient_identities']+=1;key=f'{implicit}:{mode}';variants[key]=p
     for sample in range(4):
      new={n:rng.randrange(-3,4) for n in p['variables']};old=restore(S,cert,p,new)
      val=S.evaluate(baseline['direct'],old);corr=0
      for rows in cert.get('forward_certificate',cert)['steps']:
       others=[r for r in rows if r['e']not in p['restoration_forms']]
       if not rows:continue
       sm=sum(new[r['e']] for r in others);corr+=sm*(sm-1)
       corr+=sum(new[r['e']]*(new[r['e']]-1)*new['v'+r['u'][1:]] for r in others)
      need(S.evaluate(p,new)==val+corr,'Signed complete correction identity');count['signed_identities']+=1
     for x in (0,1,2,4,17,10**30):
      try:old=CT.make_clean_witness(cert,{'x':x}) if clean else C.make_witness(cert,{'x':x})
      except ValueError:continue
      mass=S.push(cert,old);new={n:v for n,v in mass.items() if n not in p['restoration_forms']}
      need(restore(S,cert,p,new)==mass and S.evaluate(p,new)==0,'Complete natural projection');count['projected_natural_zeros']+=1
   best=min(variants,key=lambda k:variants[k]['ledger']['total']);p=variants[best]
   records.append(dict(fixture=name,horizon=h,clean=clean,branches=B,baseline={k:v['ledger'] for k,v in baseline.items()},
      ledgers={k:v['ledger'] for k,v in variants.items()},best=best,witnesses=p['natural_witnesses'],
      old_witnesses=2*B*h,degree=max(map(len,S.sourcepoly(p)),default=0),
      packets=variants if (name,h,clean) in [('incdec',2,False),('incdec',2,True),('incchain3',3,False),('incchain3',3,True),('zero3',1,False),('empty',0,True)] else None))
  inverse_boxes=[]
  for name,h,implicit in [('incdec',1,0),('incdec',2,0),('incchain3',1,1),('zero3',1,0),('test3',1,0)]:
   cert=S.make_case(C,CT,name,h,False);p=emit(S,cert,'horner',implicit)
   core=[n for n in p['variables'] if n not in ('x','y','T')];trials=zeros=0
   for values in itertools.product(range(3),repeat=len(core)):
    for x in range(4):
     new=dict(zip(core,values));new['x']=x
     mass=restore(S,cert,p,{**new,'y':0,'T':0});old=S.pull(cert,mass)
     new['y']=S.ev(cert['final_N'],old);new['T']=S.ev(cert['physical_time'],old)
     if min(new.values())<0:continue
     trials+=1;score=S.evaluate(p,new)
     need(score>=0,'Full natural polynomial must be nonnegative')
     if score==0:
      zeros+=1;mass=restore(S,cert,p,new);old=S.pull(cert,mass)
      need(min(mass.values())>=0 and min(old.values())>=0 and S.oldvalue(cert,old)==0,'Complete natural inverse fiber')
   inverse_boxes.append(dict(fixture=name,horizon=h,implicit=implicit,tuples=trials,zeros=zeros))
   count['full_natural_box_tuples']+=trials;count['full_natural_box_zeros']+=zeros
  # Naively substituting away one selector and omitting the barrier really
  # accepts a false one-step halt of the two-instruction source.
  cert=S.make_case(C,CT,'incdec',1,False);p=emit(S,cert,'horner',1)
  fake={'x':4,'e_0_0':2,'v_0_0':5,'v_0_1':0,'y':10,'T':1508}
  restored=restore(S,cert,p,fake)
  need(restored['e_0_1']==-1 and S.evaluate(S.emit(cert),restored)==0,'Naive projection false zero')
  need(S.evaluate(p,fake)==12,'Projected guard must reject counterfeit')
  naive_counterexample=dict(assignment=fake,restored_selector=-1,naive_complete_score=0,new_complete_score=12,
    meaning='The source requires two steps to reach halt; unguarded selector substitution accepts this natural supplied tuple at horizon one.')
  for B in range(1,5):
   for es in itertools.product(range(4),repeat=B-1):
    sm=sum(es)
    for vs in itertools.product(range(3),repeat=B):
     g=sm*(sm-1)+sum((1-e)**2*v for e,v in zip(es,vs))+sm*vs[-1]
     need(g>=0,'Natural gate nonnegative');count['natural_gate_tuples']+=1
     expected_zero=sm in (0,1) and all(v==0 for e,v in zip(es+(1-sm,),vs) if e==0)
     need((g==0)==expected_zero,'Exact simplex/complementarity zero set');count['natural_gate_zeros']+=g==0
 return dict(status='PASS_SELECTOR_PROJECTION',parent_sha256=PIN,archive_pins=pins,counts=dict(count),cases=records,inverse_boxes=inverse_boxes,naive_projection_counterexample=naive_counterexample,
  scope='Externally fixed source/horizon. One selector removed per nonempty step with full natural-zero bijection; whole polynomial changes by the explicit correction. No universal bound.')
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root,a.repo)
 if a.expect:need(load(a.root).exact(r,json.loads(a.expect.read_text())),'Saved receipt differs')
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 print(json.dumps(dict(counts=r['counts'],examples=[{k:v for k,v in x.items() if k!='packets'} for x in r['cases'] if x['packets']]),indent=2))
