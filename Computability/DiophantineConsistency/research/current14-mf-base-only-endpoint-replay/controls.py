#!/usr/bin/env python3
"""Pure replay comparison and child-wait controls; never launches Lean."""
import copy,importlib.util,json,sys
from pathlib import Path
if not __debug__:raise SystemExit('refusing optimized Python')
p=Path(__file__).resolve().parent;spec=importlib.util.spec_from_file_location('replay_supervisor_controls',p/'supervisor.py');s=importlib.util.module_from_spec(spec);spec.loader.exec_module(s)
rows=[{'module':'A','exit':0,'source_sha256':'sourceA','object_sha256':'objectA','axiom_reports':[['A.t','propext']],
       'direct_inputs':{'Init':{'sha256':'init'}}},
      {'module':'B','exit':0,'source_sha256':'sourceB','object_sha256':'objectB','axiom_reports':[['B.t','Quot.sound']],
       'direct_inputs':{'A':{'sha256':'objectA'},'Init':{'sha256':'init'}}}]
a={'status':'PASS','records':rows};b=copy.deepcopy(a);assert len(s.compare(a,b))==2
results={'identical_rows_accepted':True}
runner_sha='fae89cf5ae51f4ae5b9fe87129be41b38d19b456398cb954af14951fd0f1f7a1'
obs={'observed_session_exit':0,'state_sha256':'state','runner_sha256':runner_sha}
first={'status':'PASS','runner_sha256':runner_sha}
audit={'status':'PASS_RECORDED_CLIENT_ROWS_ARTIFACT_AUDIT','state_sha256':'state',
       'audited_rows':['Current14LiteralPortsMF','StructuredEndpointMF'],'audit_sha256':'audit'}
execution={'exit':0,'audit_sha256':'audit','stdout':json.dumps(audit)}
s.check_first_evidence(obs,audit,execution,first,'state','audit')
def reject_first(label,o=obs,a=audit,e=execution,f=first,state='state',audit_hash='audit'):
 try:s.check_first_evidence(o,a,e,f,state,audit_hash)
 except ValueError as exc:results[label]=repr(exc)
 else:raise AssertionError('unexpected prior evidence acceptance '+label)
reject_first('wrong_prior_state',state='other')
reject_first('wrong_audit_script',audit_hash='other')
reject_first('wrong_prior_exit',o={**obs,'observed_session_exit':1})
reject_first('wrong_audit_exit',e={**execution,'exit':1})
reject_first('wrong_prior_runner',f={**first,'runner_sha256':'other'})

def reject(label,edit,fragment):
 x=copy.deepcopy(b);edit(x)
 try:s.compare(a,x)
 except ValueError as e:
  if fragment not in repr(e):raise
  results[label]=repr(e)
 else:raise AssertionError('unexpected acceptance '+label)
reject('different_object',lambda x:x['records'][0].update(object_sha256='other'),'object digest mismatch')
reject('different_source',lambda x:x['records'][0].update(source_sha256='other'),'row/source mismatch')
reject('different_axioms',lambda x:x['records'][0].update(axiom_reports=[['A.t','sorryAx']]),'axiom report mismatch')
reject('different_dependency',lambda x:x['records'][0]['direct_inputs']['Init'].update(sha256='other'),'direct dependency digest mismatch')
reject('failed_run',lambda x:x.update(status='FAILED'),'run state not PASS')
class Fake:
 def __init__(self):self.n=0
 def wait(self):
  self.n+=1
  if self.n==1:raise RuntimeError('injected wait failure')
  return 19
child=Fake();old=s.time.sleep;s.time.sleep=lambda _:None
try:code,errors=s.wait_owned(child)
finally:s.time.sleep=old
assert code==19 and errors and child.n==2
results['wait_exception_retry']=True
print(json.dumps({'status':'PASS','controls':results,'scope':'Synthetic comparison and wait controls only; no Lean.'},sort_keys=True))
