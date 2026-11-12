from pathlib import Path
import importlib.util,json
ROOT=Path(__file__).resolve().parents[1]

def load(name):
 spec=importlib.util.spec_from_file_location(name,ROOT/'code'/(name+'.py'))
 m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
k=load('full_normal')
f=load('goal_full_six'); ff=load('goal_full_six_fuel'); zz=load('goal_zero_six')


def convert(p,g,n):
 a=k.infer(p,g,n)
 tag=p[0]
 if tag=='hyp': return p
 if tag=='qe':
  _,t,p,q=p;b=k.infer(p,g,n)[1]
  return ['qe',b,t,convert(p,g,n),convert(q,g,n)]
 if tag=='de':
  _,a,p,q=p;b=k.infer(p,g,n)[1]
  return ['de',b,convert(p,g,n),convert(q,[['q',b]]+[k.shift(x) for x in g],n+1)]
 if tag=='di':
  _,b,t,p=p
  b1=k.sub(['q',b],t)[1]
  h=b1 if b1[0]=='=' and t==['z'] else k.shift(k.sub(b1,['z']))
  return ['di',t,convert(p,[h]+[k.shift(x) for x in g],n+1)]
 if tag=='tr':
  _,h,p,q=p;e=k.infer(p,g,n)
  return ['tr',h,e[1],e[2],convert(p,g,n),convert(q,g,n)]
 return []

c=json.loads((ROOT/'certificates/full_normal_case.json').read_text())
c['proof']=convert(c['proof'],c['context'],c['variables'])
f.check(c)
cf=dict(c);cf['variables']=[c['variables'],1000];ff.check(cf)
# Adequate fuel is essential: the named-zero certificate performs computation.
cf['variables']=[c['variables'],0]
try: ff.check(cf)
except ValueError: pass
else: raise AssertionError('fuel ignored')
zz.check({'variables':0,'context':[],'goal':['=',['i',['s',['z']],['z'],['v',0]],['z']],'proof':[]})
print('goal-directed full, fuelled full, zero-normal tests passed')
