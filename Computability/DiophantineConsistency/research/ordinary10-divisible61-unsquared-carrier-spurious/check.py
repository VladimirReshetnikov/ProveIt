#!/usr/bin/env python3
"""Literal counterexample to replacing one square by its signed residual."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
old=json.loads((root/'research/ordinary10-two-norm-divisible61/candidate.json').read_text())
probe=json.loads((here/'probe.json').read_text())
rows=[]
for row in old['source']:
 if row[0]=='Bsq':assert row==['Bsq','*','Bres','Bres'];continue
 if row[0]=='sum1':assert row==['sum1','+','Bsq','firstsq'];row=['sum1','+','Bres','firstsq']
 rows.append(row)
assert probe['source']==rows and len(rows)==60
assert old['witnesses']==probe['witnesses'] and old['fixed_numerals']==probe['fixed_numerals']
def evaluate(graph,vals,ports):
 env=dict(zip(graph['witnesses'],vals));env.update(zip(graph['fixed_numerals'],ports))
 for n,op,a,b in graph['source']:
  a=env[a] if isinstance(a,str) else a;b=env[b] if isinstance(b,str) else b
  env[n]=a+b if op=='+' else a-b if op=='-' else a*b
 return env
ports=[2,1,1,0]
vals=[1,0,0,1,0,0,8750,0,3,0]
pre=evaluate(old,vals,ports)
assert (pre['q'],pre['C'],pre['X'],pre['Y'],pre['k'],pre['ell'],pre['R'])==(3,1,3,27,4,8748,41)
assert pre['Bt']==3 and pre['firstres']==3 and pre['A1']==-201471201792
num=pre['Bt']+pre['firstres']**2+pre['A1']**2
assert num%pre['qm']==0
vals[5]=num//pre['qm'];assert vals[5]==20295322575756392005638
n=evaluate(probe,vals,ports);o=evaluate(old,vals,ports)
assert n['Bres']==-(n['firstres']**2+n['A1']**2)
assert n['out']==0 and o['out']>0
assert all(x>=0 for x in vals) and ports[0]>0 and ports[1]>0
assert ports[2]<ports[0] and ports[3]<2*ports[0]
assert n['C']>0 and n['X']>0 and n['k']>n['q']
assert 2<=vals[6]-n['ell']<=n['k']-2
# Check the entire 60-row probe is topological and output-live.
available=set(probe['witnesses']+probe['fixed_numerals']);parents={}
for name,op,a,b in probe['source']:
 assert name not in available and all(not isinstance(v,str) or v in available for v in (a,b))
 available.add(name);parents[name]=(a,b)
stack=[probe['output']];seen=set();used=set()
while stack:
 name=stack.pop()
 if not isinstance(name,str):continue
 if name not in parents:used.add(name);continue
 if name in seen:continue
 seen.add(name);stack.extend(parents[name])
assert len(seen)==60 and set(probe['witnesses'])<=used
print(json.dumps({'probe_rows':len(rows),'live_probe_rows':len(seen),
 'beta_K_MC_MF':ports,'input_h':vals[5], 'ell':n['ell'],'tau':vals[6],
 'carrier_B':n['Bt'],'signed_first_residual':n['firstres'],'signed_main_residual':n['A1'],
 'probe_output_zero':True,'original_output_positive':True,
 'positive_port_and_C_X_k_tau_bounds_hold':True,
 'candidate_is_a_proved_simplification':False,'existential_inequivalence_proved':False,
 'lean_executed':False},indent=2,sort_keys=True))
