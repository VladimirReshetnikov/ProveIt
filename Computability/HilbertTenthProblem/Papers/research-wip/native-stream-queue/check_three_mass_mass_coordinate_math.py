#!/usr/bin/env python3
"""Bounded independent source-form/counterfeit census, no author tests."""
import argparse,hashlib,types,sys,json,itertools
from pathlib import Path
if not __debug__:
    raise RuntimeError('Run the scratch source checks with normal Python')
PIN='fed96578694af665258fca9eeab14fa94d8a56e810de8f684a2c9fdcd9d751e8'
def clean(d):return {k:v for k,v in d.items() if v}
def plus(*ds):
 o={}
 for d in ds:
  for k,v in d.items():o[k]=o.get(k,0)+v
 return clean(o)
def times(d,c):return clean({k:v*c for k,v in d.items()})
def ev(a,w):return sum(c*(w[k] if k else 1) for k,c in a.items())
def shift_form(a,names):
 o={}
 for k,c in a.items():
  if k in names:
   en,vn=names[k];o=plus(o,{vn:c,en:-c})
  else:o=plus(o,{k:c})
 return o
def val(cert,w,names):
 return sum(ev(shift_form(r['affine'],names),w)**2 for r in cert['squares'])+sum(ev(shift_form(r['left'],names),w)*ev(shift_form(r['right'],names),w) for r in cert['products'])
def run(path):
 b=Path(path).read_bytes();assert hashlib.sha256(b).hexdigest()==PIN
 c=types.ModuleType('_independent_three_mass_math');sys.modules[c.__name__]=c
 exec(compile(b,str(path),'exec'),c.__dict__)
 forms=[];trials=zeros=0;cofactors=set();counterfeit_trials=0
 for p,counter in [(2,0),(3,1)]:
  for op in ('inc','dec','positive','zero','nop'):
   for residue in (range(1,p) if op=='zero' else (0,)):
    br=c.Branch(0,'s','h',op,p,residue)
    actual=[shift_form(a,{'u':('e','v')}) for a in c.branch_forms(br,{'e':1},{'u':1})]
    if op=='inc':old,new={'v':1},{'v':p}
    elif op=='dec':old,new={'v':p},{'v':1}
    elif op=='positive':old=new={'v':p}
    elif op=='zero':old=new={'v':p,'e':residue-p}
    else:old=new={'v':1}
    if op=='inc':ticks=plus(times(old,108),times(new,96),{'e':8})
    elif op=='dec':ticks=plus(times(old,96),times(new,108),{'e':8})
    else:ticks=plus(times(old,192),{'e':8})
    assert actual==[old,new,ticks]
    forms.append({'prime':p,'op':op,'residue':residue,'old':old,'new':new,'ticks':ticks})
   m=c.Machine(('s','h'),'h',(c.Instruction('s','h',op,counter),)).validate()
   cert=c.export_certificate(m,'s',1,{'mode':'free_raw','name':'x'})
   rows=cert['steps'][0];names={r['u']:(r['e'],'v'+str(j)) for j,r in enumerate(rows)}
   for x in range(16):
    for es in itertools.product(range(3),repeat=len(rows)):
     for vs in itertools.product(range(7),repeat=len(rows)):
      w={'x':x}
      for j,r in enumerate(rows):w[r['e']]=es[j];w['v'+str(j)]=vs[j]
      f=val(cert,w,names);trials+=1
      if es.count(1)==1 and sum(es)==1 and vs[es.index(1)]==0:counterfeit_trials+=1;assert f>0
      if f==0:
       zeros+=1;assert all(v>=e for v,e in zip(vs,es))
       oldw={'x':x}
       for j,r in enumerate(rows):oldw[r['e']]=es[j];oldw[r['u']]=vs[j]-es[j]
       oldf=sum(ev(a['affine'],oldw)**2 for a in cert['squares'])+sum(ev(a['left'],oldw)*ev(a['right'],oldw) for a in cert['products'])
       assert oldf==0
       # Independent p-adic remainder is not restricted to cofactor one.
       n=x+1
       while n%2==0:n//=2
       while n%3==0:n//=3
       cofactors.add(n)
 boundary=[]
 for h in range(4):
  for q in ('s','h'):
   cert=c.export_certificate(c.Machine(('s','h'),'h',()),q,h,{'mode':'free_raw','name':'x'})
   f=val(cert,{'x':4},{})
   assert (f==0)==(h==0 and q=='h')
   boundary.append({'B':0,'h':h,'initial':q,'polynomial':f})
 # Positive-horizon no outgoing initial state: a branch exists elsewhere.
 m=c.Machine(('s','t','h'),'h',(c.Instruction('t','h','nop'),))
 for q in ('s','h'):
  cert=c.export_certificate(m,q,1,{'mode':'free_raw','name':'x'})
  r=cert['steps'][0][0];ns={r['u']:(r['e'],'v')}
  for x,e,v in itertools.product(range(5),range(3),range(5)):
   assert val(cert,{'x':x,r['e']:e,'v':v},ns)>0
 return {'source_sha256':PIN,'literal_branch_forms':forms,'complete_natural_one_step_tuples':trials,'complete_natural_zeros':zeros,'selected_v_zero_rejections':counterfeit_trials,'observed_prime_to_six_cofactors':sorted(cofactors),'empty_branch_boundaries':boundary,'terminal_or_stuck_tuples_rejected':150,'scope':'Finite source and counterfeit checks support the separate inductive proof; no author suites, no universal proof by enumeration.'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--core',required=True);p.add_argument('--output',required=True);a=p.parse_args();r=run(a.core);Path(a.output).write_text(json.dumps(r,sort_keys=True,indent=2)+'\n');print(r['complete_natural_one_step_tuples'],r['complete_natural_zeros'],r['selected_v_zero_rejections'])
