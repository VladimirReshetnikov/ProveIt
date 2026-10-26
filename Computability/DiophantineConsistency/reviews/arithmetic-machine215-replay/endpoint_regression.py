"""Two-leaf native regression after the authorized decimal import narrowing."""
from pathlib import Path
import hashlib,json,os,subprocess,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
W=Path('/tmp/current-positive-zero2011-decimal-import-regression')
A=Path('/tmp/arithmetic215-actual-private')
M=R/'Computability/DiophantineConsistency/reviews/current-positive-zero2011-refresh'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(b,s):
 if not b:raise RuntimeError(s)
def verify(r):require(sha(r['path'])==r['sha256'],'Hash drift '+r['path'])
def rec(p):return {'path':str(p),'sha256':sha(p),'bytes':Path(p).stat().st_size}
require(sha(M/'manifest.json')=='1aa0d66e626bff9e03ef1b6317c61518bb520b0eadaf336ff8abfc45357a2e72','Prior manifest')
require(sha(M/'execution-state.json')=='d299eb7e7c213b3db2dc795a85c6c54c872fbc554bef1839002037ba245999a3','Prior state')
m=json.loads((M/'manifest.json').read_text());old=json.loads((M/'execution-state.json').read_text())
require(old['status']=='PASS','Prior refresh not PASS')
changed=json.loads((A/'DecimalMachine215-narrow1.json').read_text());require(changed['exit_code']==0,'Decimal not PASS')
require(sha(changed['source'])==changed['source_sha256'],'Decimal source');require(sha(changed['object'])==changed['object_sha256'],'Decimal object')
fresh={x['module']:x for x in old['completed']}
targets=['DiophantineConsistency.CurrentPositiveZero2011','DiophantineConsistency.CurrentPositiveZero2011Checks']
require(not W.exists(),'New overlay required');W.mkdir();lib=W/'lib';lib.mkdir()
reused=[]
for x in m['modules']:
 n=x['module'];o=fresh[n]['object'] if n in fresh else x['prior_object']
 verify(o)
 if n=='DiophantineConsistency.DecimalMachine215':
  require(sha(x['source']['path'])==changed['source_sha256'],'New decoder source')
  o=rec(changed['object'])
 else:verify(x['source'])
 if n in targets:continue
 p=lib.joinpath(*n.split('.')).with_suffix('.olean');p.parent.mkdir(parents=True,exist_ok=True);p.symlink_to(o['path'])
 reused.append({'module':n,'object':o,'source':rec(x['source']['path'])})
for x in m['external_boundary']:
 for r in [x['object']]+x['companions']+([x['source']] if x['source'] else []):verify(r)
for r in m['toolchain']:verify(r)
lean=next(x['path'] for x in m['toolchain'] if x['path'].endswith('/bin/lean'))
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(lib)]+m['external_lean_path']);env.pop('LEAN_SRC_PATH',None)
s={'scope':'Only two endpoint leaves freshly rebuilt; unchanged intermediate clients reused, not a full closure replay',
 'status':'RUNNING','driver':rec(__file__),'prior_manifest':rec(M/'manifest.json'),'prior_state':rec(M/'execution-state.json'),
 'decimal_replay':rec(A/'DecimalMachine215-narrow1.json'),'reused':reused,'completed':[],'LEAN_PATH':env['LEAN_PATH']}
def save(): (W/'state.json').write_text(json.dumps(s,indent=2)+'\n')
save()
for n in targets:
 x=next(x for x in m['modules'] if x['module']==n);verify(x['source'])
 out=lib.joinpath(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 log=W/(n+'.log');timing=log.with_suffix('.time')
 cmd=['/usr/bin/time','-f','elapsed=%e max_rss_kb=%M','-o',str(timing),lean,'-M6000','-j1','-DElab.async=false','-o',str(out),x['source']['path']]
 start=time.time()
 with log.open('w') as f:
  p=subprocess.Popen(cmd,cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT);s['active']={'module':n,'pid':p.pid};save();code=p.wait()
 s['completed'].append({'module':n,'source':x['source'],'command':cmd,'exit_code':code,'elapsed':time.time()-start,'log':rec(log),'timing':rec(timing),'object':rec(out) if code==0 else None})
 verify(x['source']);save();print(n,code,log.read_text(),flush=True)
 require(code==0,'Endpoint regression failure')
s['active']=None;s['status']='PASS';save();print('PASS',sha(W/'state.json'))
