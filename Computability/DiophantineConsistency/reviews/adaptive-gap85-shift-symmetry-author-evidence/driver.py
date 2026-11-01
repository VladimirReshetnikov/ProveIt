"""Replay the exact 85 shift symmetry on the cross-parent provider."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4];SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
P=Path('/tmp/adaptive86-machine-compat-rebase-v13-jld1zn0t');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');C=Path('/tmp/adaptive-gap85-cross-parent-adapters-6jqu5prd');A=Path('/tmp/adaptive-gap85-merged-adapters-2aaldm9k');S=Path('/tmp/adaptive-gap85-merged-suffix-2tpig005');T=Path('/tmp/adaptive-gap85-merged-suffix-eerd10hd')
name='AdaptiveGap85ShiftSymmetry';sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
ps,bs,cs,aa,ss,tt=[read(x/'state.json') for x in [P,B,C,A,S,T]];assert all(s['status']=='PASS' for s in [ps,bs,cs,aa,ss,tt]);assert len(cs['records'])==len(aa['records'])==10 and len(ss['records'])==len(tt['records'])==29
assert cs['sources']==aa['sources'] and cs['provider_inventory_sha256']==aa['provider_inventory_sha256']
for x,y in zip(cs['records'],aa['records']):assert all(x[k]==y[k] for k in ['name','exit','source_sha256','object_sha256','log_sha256'])
for x,y in zip(ss['records'],tt['records']):assert all(x[k]==y[k] for k in ['name','exit','source_sha256','object_sha256','log_sha256'])
assert ss['source_sha256']==tt['source_sha256'] and ss['graph']==tt['graph'] and ss['parents']==tt['parents']
parents={str(x):sha(x/'state.json') for x in [P,B,C,A,S,T]};extra_parents=ss['parents'];inventory=read(P/'providers.json');ih=sha(P/'providers.json');assert ih==cs['provider_inventory_sha256'] and len(inventory)==507
sourceh=sha(SRC/(name+'.lean'));w=Path(tempfile.mkdtemp(prefix='adaptive-gap85-shift-symmetry-'));lib=w/'lib';lib.mkdir();(w/'logs').mkdir();shutil.copyfile(__file__,w/'driver.py');shutil.copyfile(SRC/(name+'.lean'),w/'logs'/(name+'.lean'))
for top in (C/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   path=Path(root)/f;dest=lib/path.relative_to(C/'lib');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(path.resolve())
state={'status':'RUNNING','private':str(w),'source_sha256':sourceh,'parents':parents,'provider_inventory_sha256':ih,'inherited_objects':len(inventory),'suffix_outputs':len(ss['records']),'adapter_outputs':len(cs['records']),'scope':'The exact 85 integer polynomial is invariant under the stated shift. A positive zero satisfying an explicit T threshold yields another positive zero with failing reverse gap. Existence and the T threshold are not asserted. The 40 other source-graph objects and model/Foundation/package boundary remain historical. No unconditional reverse bound or 85 HA equivalence is asserted.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 return sha(SRC/(name+'.lean'))==sourceh and sha(w/'logs'/(name+'.lean'))==sourceh and all(sha(Path(x)/'state.json')==h for x,h in parents.items()) and all(sha(Path(x)/'state.json')==h for x,h in extra_parents.items()) and all(sha(P/'lib'/(r['name'].replace('.','/')+'.olean'))==r['object_sha256'] and sha(P/'logs'/(r['name'].split('.')[-1]+'.log'))==r['log_sha256'] for r in ps['records']) and all(sha(root/(n+'.olean'))==st['object_sha256'] and sha(root/'logs'/(n+'.log'))==st['log_sha256'] for root,n in [(Path('/tmp/adaptive-gap85-literal-ujfnw2dg'),'AdaptiveGap85Literal'),(Path('/tmp/adaptive-gap85-factors-xtusii0w'),'AdaptiveGap85Factors'),(Path('/tmp/adaptive-gap85-magnitudes-19f4qgaw'),'AdaptiveGap85Magnitudes')] for st in [read(root/'state.json')]) and all(sha(SRC/(n+'.lean'))==h and sha(S/'sources'/(n+'.lean'))==h and sha(T/'sources'/(n+'.lean'))==h for n,h in ss['source_sha256'].items()) and all(sha(SRC/(n+'.lean'))==h and sha(C/'sources'/(n+'.lean'))==h and sha(A/'sources'/(n+'.lean'))==h for n,h in cs['sources'].items()) and sha(P/'providers.json')==ih and all(sha(x['path'])==x['sha256'] for x in inventory.values()) and all(sha(root/'lib/DiophantineConsistency'/(row['name']+'.olean'))==row['object_sha256'] and sha(root/'logs'/(row['name']+'.log'))==row['log_sha256'] for root,rows in [(C,cs['records']),(A,aa['records']),(S,ss['records']),(T,tt['records'])] for row in rows)
save();print('PRIVATE',w,flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);out=w/(name+'.olean');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(SRC/(name+'.lean'))];t=time.monotonic()
 with (w/'logs'/(name+'.log')).open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(w/'logs'/(name+'.time')),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 state.update(exit=code,seconds=time.monotonic()-t,object_sha256=sha(out) if out.exists() else None,log_sha256=sha(w/'logs'/(name+'.log')),time_sha256=sha(w/'logs'/(name+'.time')));save();assert code==0 and auth();state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=repr(e));save();raise
