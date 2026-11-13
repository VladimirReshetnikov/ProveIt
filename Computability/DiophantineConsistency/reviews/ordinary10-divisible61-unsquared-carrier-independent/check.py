from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary10-divisible61-unsquared-carrier-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
old=json.loads(Path('research/ordinary10-two-norm-divisible61/candidate.json').read_text())
probe=json.loads(Path('research/ordinary10-divisible61-unsquared-carrier-spurious/probe.json').read_text())
assert old['domain']==probe['domain']=='nonnegative integers'
assert old['fixed_numerals']==probe['fixed_numerals']==['beta','K0','MC','MF']
assert old['witnesses']==probe['witnesses']==['n_J','n_F','n_alpha','n_w','n_s','n_h','n_tau','n_eta','n_zeta','n_gamma']
assert len(old['source'])==61 and len(probe['source'])==60
assert [r for r in old['source'] if r[0]=='Bsq']==[['Bsq','*','Bres','Bres']]
assert [r for r in old['source'] if r[0]=='sum1']==[['sum1','+','Bsq','firstsq']]
transformed=[(['sum1','+','Bres','firstsq'] if row[0]=='sum1' else row) for row in old['source'] if row[0]!='Bsq']
assert transformed==probe['source']
ports=[2,1,1,0];inputs=[1,0,0,1,0,20295322575756392005638,8750,0,3,0]
assert min(ports+inputs)>=0

def eval_literal(g):
 env=dict(zip(g['fixed_numerals'],ports));env.update(zip(g['witnesses'],inputs))
 live={}
 for name,op,a,b in g['source']:
  assert name not in env and op in ('+','-','*')
  live[name]=(a,b)
  a=a if isinstance(a,int) else env[a];b=b if isinstance(b,int) else env[b]
  env[name]=a+b if op=='+' else a-b if op=='-' else a*b
 seen=set();used=set()
 def walk(x):
  if isinstance(x,int):return
  if x not in live:used.add(x);return
  if x in seen:return
  seen.add(x)
  for j in live[x]:walk(j)
 walk(g['output']);assert len(seen)==len(g['source']) and used==set(g['fixed_numerals']+g['witnesses'])
 return env
oldv=eval_literal(old);newv=eval_literal(probe)
for key in oldv.keys()&newv.keys():
 if key not in ('sum1','out'):assert oldv[key]==newv[key],key
assert (newv['q'],newv['C'],newv['X'],newv['Y'],newv['k'],newv['R'])==(3,1,3,27,4,41)
assert newv['ell']==8748 and newv['Bt']==3 and newv['firstres']==3 and newv['A1']==-201471201792
N=40590645151512784011273
assert N==newv['firstres']**2+newv['A1']**2 and newv['Bres']==-N
assert newv['out']==0 and oldv['out']==N*N+N==1647600473816028280482680991661814740975091802
assert ports[0]>0 and ports[1]>0 and ports[2]<ports[0] and ports[3]<2*ports[0]
assert newv['C']>0 and newv['X']>0 and newv['k']>newv['q']
assert 2<=inputs[6]-newv['ell']<=newv['k']-2
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'exact_one_gate_probe_edit':True,'rows_evaluated':[61,60],
 'probe_zero_original_positive':True,'all_reported_inequalities_checked':True,
 'same_point_counterexample_only':True,'existential_nonequivalence_proved':False,
 'compact_ports_tested':False,'lean_executed':False},indent=2,sort_keys=True))
