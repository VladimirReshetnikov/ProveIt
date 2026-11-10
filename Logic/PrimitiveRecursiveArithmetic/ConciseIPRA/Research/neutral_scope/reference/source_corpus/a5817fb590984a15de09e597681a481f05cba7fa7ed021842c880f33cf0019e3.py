import json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent
import validate_counter as v
from produce_scalar import ScalarEmitter,fixtures
import produce_counter
class UnboxedEmitter(ScalarEmitter):
    go=produce_counter.Emitter.go
positive=json.loads((ROOT/'fixtures/scalar_unfocused.json').read_text())['cases']
negative=v.negative_cases(positive)
negative.extend([
 dict(name='true_step_unboxed_zero_restricted',accept=False,packet=[[0,0,0,0],[[[0],0,[]],[]]]),
 dict(name='false_scalar_constant_update',accept=False,packet=[[0,0,0,0],[[[[]],[],[]],[[]]]]),
 dict(name='true_step_unboxed_variable_restricted',accept=False,packet=UnboxedEmitter(focused=False).run(fixtures()['DI_progress_uses_hypothesis']))
])
aliases=[]
for name,seed,accept in [('empty_string','',True),('empty_object',{},True),('empty_key_object',{'':{'unread':'payload'}},True),('fractional_zero',0.5,True),('false_zero',False,True),('true_dummy_one',True,True),('nonempty_string','x',False),('nonempty_object_key',{'x':0},False),('two_object_keys',{'':0,'x':0},False),('nan_root',float('nan'),False),('positive_infinity_root',float('inf'),False),('negative_infinity_root',float('-inf'),False),('none_root',None,False)]:
 packet=[[0,0,0,0],[[[],seed,0],[seed]]]
 aliases.append(dict(name='alias_'+name,packet=packet,accept=accept))
for name,x in [('nan',float('nan')),('positive_infinity',float('inf')),('negative_infinity',float('-inf')),('high_integer',1234567),('high_fraction',1234.5)]:
 p=json.loads(json.dumps(next(c['packet'] for c in positive if c['name']=='reflexivity_zero')))
 p[-2][3][0]=x
 aliases.append(dict(name='hole_'+name,packet=p,accept=True))
results=[]
for opt in (False,True):
 for case in positive+negative+aliases:
  r=v.run(Path(__file__).parent/'kernel_balanced.py',case['packet'],opt)
  results.append(dict(name=case['name'],optimized=opt,expected=case['accept'],passed=r['accept']==case['accept'] and not r['timeout'],**r))
report=dict(positive_cases=len(positive),negative_cases=len(negative),alias_cases=len(aliases),check_count=len(results),passed=sum(x['passed'] for x in results),failures=[x for x in results if not x['passed']],metrics=v.metrics(Path(__file__).parent/'kernel_balanced.py'),checks=results)
(ROOT/'evidence/implementation_balanced_validation.json').write_text(json.dumps(report,indent=2)+'\n')
serialized=[]
for case in positive+negative+aliases:
 try:
  json.dumps(case,allow_nan=False)
  serialized.append(case)
 except ValueError:
  serialized.append({k:w for k,w in case.items() if k!='packet'} | {'packet_json':json.dumps(case['packet'])})
(ROOT/'fixtures/balanced.json').write_text(json.dumps(dict(cases=serialized),indent=2,allow_nan=False)+'\n')
print(json.dumps({k:w for k,w in report.items() if k!='checks'},indent=2))

if report['failures']:raise SystemExit(1)
