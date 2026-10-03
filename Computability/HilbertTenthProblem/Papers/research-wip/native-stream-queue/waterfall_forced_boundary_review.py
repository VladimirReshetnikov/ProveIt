#!/usr/bin/env python3
"""Independent formal-source and guarded-API audit of forced boundaries."""
import argparse, copy, hashlib, importlib.util, json, random, subprocess, sys
from pathlib import Path
if not __debug__:raise RuntimeError('Assertions must be enabled')
def load(path,name):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def review(source,parent,helper):
 assert hashlib.sha256(source.read_bytes()).hexdigest()=='56c2c9eabad9faa51b66e02315264c93da0c9915cb406badfa1822a188f0b747'
 assert hashlib.sha256(parent.read_bytes()).hexdigest()=='506c7d8505e2076628b351a016104a3ad851a4178fa664709ae87774a645dc7f'
 assert hashlib.sha256(helper.read_bytes()).hexdigest()=='c4af73ee8d59fa497f68cf3f6a54fca4146dd759656d57b859c5ccb3f937fd52'
 m=load(source,'waterfall_root_derivative_audit');p=load(parent,'waterfall_parent_derivative_audit');h=load(helper,'waterfall_review_independent_algebra')
 counts={};ledgers=[]
 def tick(k,n=1):counts[k]=counts.get(k,0)+n
 def reject(f):
  try:f()
  except (TypeError,ValueError,KeyError):tick('malformed_rejected');return
  raise AssertionError('Malformed input accepted')
 rng=random.Random(144645)
 for k in (1,2,3,4,5,7,8,10):
  for mode in ('parent','prefix','ends'):
   if mode=='ends' and k<4:continue
   c=m.build(k,mode);pc=p.DirectionalQuadratic(k)
   if mode=='parent':
    restored={};poly=h.source_poly(pc);remain=pc.witnesses
   else:
    kind='first_suffix_head' if mode=='ends' else 'first_head' if k>=2 else 'first'
    _,restored,remain,poly,ledger=h.projection(p,k,kind)
   assert c['witnesses']==tuple(remain)
   actual_rest={n:{((v,) if v else ()):coef for v,coef in terms} for n,terms in c['restoration']}
   assert actual_rest==restored
   assert dict(c['expanded_polynomial'])==poly;tick('complete_source_substitution_identities')
   assert dict(poly)[('tau','tau')]==1
   # Independently expand every arithmetic gate, proving the full SLP identity.
   computed={n:h.var(n) for n in c['parameters']+c['witnesses']}
   refs={n:() for n in computed};M=A=0
   for name,op,a,b in c['source']:
    assert type(name) is str and name not in computed and op in ('*','+','-')
    assert type(a) is int or type(a) is str and a in computed
    assert type(b) is int or type(b) is str and b in computed
    assert not (type(a) is int and type(b) is int)
    x=h.con(a) if type(a) is int else computed[a];y=h.con(b) if type(b) is int else computed[b]
    computed[name]=h.mul(x,y) if op=='*' else h.add(x,h.sc(-1,y) if op=='-' else y)
    refs[name]=tuple(v for v in (a,b) if type(v) is str)
    if op=='*':
     M+=1;assert a not in (0,1) and b not in (0,1)
    else:A+=1
   out=h.con(c['output']) if type(c['output']) is int else computed[c['output']]
   assert out==poly;tick('complete_slp_polynomial_identities')
   used=set();pending=[c['output']]
   while pending:
    n=pending.pop()
    if type(n) is str and n not in used:used.add(n);pending.extend(refs[n])
   assert all(n in used for n,_,_,_ in c['source'])
   assert (M,A,M+A)==(c['ledger']['M'],c['ledger']['A'],c['ledger']['operations'])
   assert c['ledger']['expanded_monomials']==len(poly)
   ledgers.append(dict(k=k,mode=mode,**c['ledger']));tick('literal_gate_counts_and_liveness')
   # All mutable public return fields must be copied across fresh cache reads.
   other=m.build(k,mode);other['ledger'].clear();other['source']=();other['restoration']=();other['parameters']=()
   assert m.checked(c)==c and m.build(k,mode)==c;tick('defensive_export_copies')
   zeros={n:0 for n in c['parameters']+c['witnesses']}
   for _ in range(6):
    env={n:rng.randrange(-3,5) for n in zeros}
    restored_env=m.restore_assignment(c,env,signed=True)
    expected=dict(env);expected.update({n:h.val(a,env) for n,a in restored.items()})
    assert restored_env==expected
    assert m.evaluate(c,env,signed=True)==h.val(poly,env)
    tick('signed_assignment_replays')
   for key in ('horizon','mode','archive_sha256','ledger','restoration','source','squares','products','parameters','witnesses','parent_squares','parent_products','expanded_polynomial'):
    bad=copy.deepcopy(c);bad[key]=None;reject(lambda bad=bad:m.checked(bad))
   bad=copy.deepcopy(c);bad['ledger']['degree']=2.0;reject(lambda:m.checked(bad))
   bad=copy.deepcopy(c);bad['ledger']['degree']=True;reject(lambda:m.checked(bad))
   bad=copy.deepcopy(c);row=list(bad['source'][0]);row[0]='other';bad['source']=(tuple(row),)+bad['source'][1:];reject(lambda:m.checked(bad))
   for name in zeros:
    for val in (False,0.0,-1):
     bad=dict(zeros);bad[name]=val;reject(lambda bad=bad:m.evaluate(c,bad))
   for kwargs in ({'signed':0},{'signed':1},{'signed':None}):
    reject(lambda kwargs=kwargs:m.restore_assignment(c,zeros,**kwargs))
    reject(lambda kwargs=kwargs:m.evaluate(c,zeros,**kwargs))
   bad=dict(zeros);bad['extra']=0;reject(lambda:m.evaluate(c,bad))
   bad=dict(zeros);del bad['L0'];reject(lambda:m.evaluate(c,bad))
   reject(lambda:m.project_assignment(c,m.restore_assignment(c,zeros)))
   # Same-numeric-value coefficient mutations cannot pass exact canonical guard.
   bad=copy.deepcopy(c);row=list(bad['source'][0]);changed=False
   for i in (2,3):
    if type(row[i]) is int:row[i]=float(row[i]);changed=True;break
   if changed:
    bad['source']=(tuple(row),)+bad['source'][1:];reject(lambda:m.checked(bad))
 for k in (1,2,3):reject(lambda k=k:m.build(k,'ends'))
 for mode in ('parent','prefix','ends'):
  for k in (True,False,7.0,0,-1,None):reject(lambda k=k,mode=mode:m.build(k,mode))
 c=m.build();env=m.canonical_assignment(c,6,0);old=m.restore_assignment(c,env)
 assert m.project_assignment(c,old)==env and m.evaluate(c,env)==0
 huge=10**500;bad=dict(env,L0=huge)
 assert type(m.evaluate(c,bad)) is int and m.evaluate(c,bad)==h.val(dict(c['expanded_polynomial']),bad)>0
 assert m.canonical_assignment(m.build(8,'ends'),6,0) is None
 assert m.canonical_assignment(m.build(6,'ends'),6,0) is None
 for field in ('ARCHIVE_SHA256','SOURCE_SHA256'):
  program = """import importlib.util,sys
s=importlib.util.spec_from_file_location('wf_optimized_test',sys.argv[1]);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
setattr(m,sys.argv[2],'0'*64)
try:m.build(1,'parent')
except ValueError:print('PASS')
else:raise RuntimeError('Optimized public build skipped source authentication')
"""
  result=subprocess.run([sys.executable,'-O','-c',program,str(source),field],capture_output=True,text=True,timeout=300)
  assert result.returncode==0 and result.stdout.strip()=='PASS',(field,result.stdout,result.stderr)
  tick('optimized_authentication_rejections')
 return dict(status='PASS',source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),parent_sha256=hashlib.sha256(parent.read_bytes()).hexdigest(),counts=counts,ledgers=ledgers,
 scope='Independent complete sparse-polynomial identities and complete source SLP expansion for 21 schedules, API guards and copies; all-horizon proof reviewed separately.')
def verify(source, parent, helper):
 return review(Path(source).resolve(),Path(parent).resolve(),Path(helper).resolve())

def main():
 p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--parent',type=Path,required=True);p.add_argument('--helper',type=Path,required=True);p.add_argument('--receipt',type=Path,required=True);a=p.parse_args()
 r=review(a.source.resolve(),a.parent.resolve(),a.helper.resolve());a.receipt.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
if __name__=='__main__':main()
