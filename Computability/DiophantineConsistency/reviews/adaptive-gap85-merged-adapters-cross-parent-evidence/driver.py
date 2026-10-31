"""Replay conditional 85 adapters against an independently rebuilt suffix."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4];SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
P=Path('/tmp/adaptive86-machine-compat-rebase-v13-jld1zn0t');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl');A=Path('/tmp/adaptive-gap85-merged-suffix-eerd10hd')
parser=argparse.ArgumentParser();parser.add_argument('--suffix',type=Path,required=True);S=parser.parse_args().suffix.resolve();assert S!=A
names=['AdaptiveGap85RankOrientation','AdaptiveGap85PortBound','AdaptiveGap85PortBoundary','AdaptiveGap85GenericSignedHalfIndex','AdaptiveGap85FirstRankResidue','AdaptiveGap85OrientedRank','AdaptiveGap85ActualSignedHalf','AdaptiveGap85FixedPortBounds','AdaptiveGap85ActualPortBound','AdaptiveGap85FixedPortClient']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
ps,bs,ss,aa=[read(x/'state.json') for x in [P,B,S,A]];assert all(x['status']=='PASS' for x in [ps,bs,ss,aa]);assert len(ss['records'])==len(aa['records'])==29 and len(ss['source_sha256'])==69
assert all(ss[k]==aa[k] for k in ['roots','graph','source_sha256','changed_seeds','missing_modules','build_order','parents','provider_inventory_sha256','selected_inherited_objects','parent_outputs'])
for ar,br in zip(aa['records'],ss['records']):
 assert all(ar[k]==br[k] for k in ['name','exit','source_sha256','object_sha256','log_sha256'])
parents={str(x):sha(x/'state.json') for x in [P,B,S,A]};ph=ss['parents'];inventory=read(P/'providers.json');ih=sha(P/'providers.json');assert len(inventory)==507 and ih==ss['provider_inventory_sha256']
sourceh={n:sha(SRC/(n+'.lean')) for n in names};assert not set(names)&set(ss['source_sha256'])
w=Path(tempfile.mkdtemp(prefix='adaptive-gap85-cross-parent-adapters-'));lib=w/'lib';lib.mkdir();(w/'logs').mkdir();(w/'sources').mkdir();shutil.copyfile(__file__,w/'driver.py')
for n in names:shutil.copyfile(SRC/(n+'.lean'),w/'sources'/(n+'.lean'))
for top in (S/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   path=Path(root)/f;dest=lib/path.relative_to(S/'lib');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(path.resolve())
state={'status':'RUNNING','private':str(w),'names':names,'sources':sourceh,'parent_state_sha256':parents,'suffix_parent_anchors':ph,'provider_inventory_sha256':ih,'inherited_objects':len(inventory),'suffix_outputs':len(ss['records']),'source_graph_count':len(ss['source_sha256']),'records':[],'scope':'Ten conditional adapters compiled from current sources over a separately rebuilt and hash-matched 29-module merged-source suffix; 40 other project graph objects and model/Foundation/package ancestry remain historical. The small signed-rank, half-size and/or main-index growth hypotheses are explicit where used. No unconditional 85 reverse bound or HA equivalence is claimed.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 return all(sha(SRC/(n+'.lean'))==h and sha(w/'sources'/(n+'.lean'))==h for n,h in sourceh.items()) and all(sha(SRC/(n+'.lean'))==h and sha(S/'sources'/(n+'.lean'))==h and sha(A/'sources'/(n+'.lean'))==h for n,h in ss['source_sha256'].items()) and all(sha(Path(x)/'state.json')==h for x,h in parents.items()) and all(sha(Path(x)/'state.json')==h for x,h in ph.items()) and sha(P/'providers.json')==ih and all(sha(x['path'])==x['sha256'] for x in inventory.values()) and all(sha(S/'lib/DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256'] and sha(S/'logs'/(r['name']+'.log'))==r['log_sha256'] and sha(A/'lib/DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256'] and sha(A/'logs'/(r['name']+'.log'))==r['log_sha256'] for r in ss['records']) and all(sha(P/'lib'/(r['name'].replace('.','/')+'.olean'))==r['object_sha256'] and sha(P/'logs'/(r['name'].split('.')[-1]+'.log'))==r['log_sha256'] for r in ps['records'])
save();print('PRIVATE',w,flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in names:
  assert auth(),('source/provider drift before',n)
  out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists();cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(SRC/(n+'.lean'))];t=time.monotonic()
  with (w/'logs'/(n+'.log')).open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(w/'logs'/(n+'.time')),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  rec={'name':n,'exit':code,'seconds':time.monotonic()-t,'source_sha256':sourceh[n],'object_sha256':sha(out) if out.exists() else None,'log_sha256':sha(w/'logs'/(n+'.log'))};state['records'].append(rec);save();assert code==0 and auth(),('compile/auth failure',n);print('PASS',n,flush=True)
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=repr(e));save();raise
