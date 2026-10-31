"""Refresh a guarded 85 signed-rank source suffix over a historical model boundary."""
from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path(__file__).resolve().parents[4]; SRC=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'; D=Path(__file__).parent
P=Path('/tmp/adaptive86-machine-compat-rebase-v13-jld1zn0t');B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl')
L=Path('/tmp/adaptive-gap85-literal-ujfnw2dg');F=Path('/tmp/adaptive-gap85-factors-xtusii0w');M=Path('/tmp/adaptive-gap85-magnitudes-19f4qgaw')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
parents={str(x):sha(x/'state.json') for x in [P,B,L,F,M]};ps,bs,ls,fs,ms=[read(x/'state.json') for x in [P,B,L,F,M]];assert all(s['status']=='PASS' for s in [ps,bs,ls,fs,ms])
inventory=read(P/'providers.json');ih=sha(P/'providers.json');assert len(inventory)==507
roots=['AdaptiveGap85AuxSigned','AdaptiveGap85ResidueClient','AdaptiveGap85RankCongruence','AdaptiveGap85IndexOrder'];graph={};todo=roots[:]
while todo:
 n=todo.pop()
 if n in graph:continue
 path=SRC/(n+'.lean')
 if not path.exists():continue
 deps=[]
 for line in path.read_text().splitlines():
  if line.startswith('import '):deps+=re.findall(r'DiophantineConsistency\.([A-Za-z0-9_]+)',line)
 graph[n]=deps;todo.extend(deps)
sourceh={n:sha(SRC/(n+'.lean')) for n in graph}
base=P/'lib/DiophantineConsistency';extras={'AdaptiveGap85Literal','AdaptiveGap85Factors','AdaptiveGap85Magnitudes'}
missing={n for n in graph if not (base/(n+'.olean')).exists() and n not in extras}
seeds={'ArithmeticAdaptiveFactorUnits2011','ArithmeticAdaptiveFirstDivisibility2011','ArithmeticAdaptiveRankCongruence2011','ArithmeticAdaptiveTransportQuotient2011','AdaptiveGap85AuxNorm','AdaptiveGap85FirstDivisibility','AdaptiveGap85IndexOrder','AdaptiveGap85StrongNorm','AdaptiveGap85Units'}
affected=(seeds|missing)&graph.keys()
while True:
 fresh={n for n,deps in graph.items() if any(x in affected for x in deps)}-affected
 if not fresh:break
 affected|=fresh
order=[];remaining=set(affected)
while remaining:
 ready=sorted(n for n in remaining if not set(graph[n])&remaining)
 assert ready,('cycle',remaining)
 order.extend(ready);remaining.difference_update(ready)
assert len(graph)==69 and len(order)==29,(len(graph),len(order))
assert sourceh['AdaptiveGap85Literal']==ls['source_sha256'] and sourceh['AdaptiveGap85Factors']==fs['source_sha256'] and sourceh['AdaptiveGap85Magnitudes']==ms['source_sha256']
w=Path(tempfile.mkdtemp(prefix='adaptive-gap85-merged-suffix-'));lib=w/'lib';lib.mkdir();(w/'logs').mkdir();(w/'sources').mkdir();shutil.copyfile(__file__,w/'driver.py')
for n in graph:shutil.copyfile(SRC/(n+'.lean'),w/'sources'/(n+'.lean'))
for top in (P/'lib').iterdir():
 if top.name!='DiophantineConsistency':(lib/top.name).symlink_to(top.resolve(),target_is_directory=top.is_dir());continue
 for root,dirs,files in os.walk(top,followlinks=True):
  for f in files:
   path=Path(root)/f;dest=lib/path.relative_to(P/'lib');dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(path.resolve())
for root,n in [(L,'AdaptiveGap85Literal'),(F,'AdaptiveGap85Factors'),(M,'AdaptiveGap85Magnitudes')]:
 dest=lib/'DiophantineConsistency'/(n+'.olean');assert not dest.exists();dest.symlink_to((root/(n+'.olean')).resolve())
for n in order:
 dest=lib/'DiophantineConsistency'/(n+'.olean')
 if dest.is_symlink():dest.unlink()
 else:assert not dest.exists()
state={'status':'RUNNING','private':str(w),'roots':roots,'graph':graph,'source_sha256':sourceh,'changed_seeds':sorted(seeds&graph.keys()),'missing_modules':sorted(missing),'build_order':order,'parents':parents,'provider_inventory_sha256':ih,'selected_inherited_objects':len(inventory),'parent_outputs':len(ps['records']),'records':[],'scope':'A current-workspace 29-module source suffix over a pinned historical v13 model/project/Foundation/package boundary. All 69 current source graph hashes are guarded; the other 40 graph-node objects are inherited and are not certified from their current source. No 85 reverse bound or equivalence is asserted.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2,sort_keys=True)+'\n')
def auth():
 return all(sha(SRC/(n+'.lean'))==h and sha(w/'sources'/(n+'.lean'))==h for n,h in sourceh.items()) and all(sha(Path(x)/'state.json')==h for x,h in parents.items()) and sha(P/'providers.json')==ih and all(sha(x['path'])==x['sha256'] for x in inventory.values()) and all(sha(P/'lib'/(r['name'].replace('.','/')+'.olean'))==r['object_sha256'] and sha(P/'logs'/(r['name'].split('.')[-1]+'.log'))==r['log_sha256'] for r in ps['records']) and all(sha(root/(n+'.olean'))==st['object_sha256'] and sha(root/'logs'/(n+'.log'))==st['log_sha256'] for root,n,st in [(L,'AdaptiveGap85Literal',ls),(F,'AdaptiveGap85Factors',fs),(M,'AdaptiveGap85Magnitudes',ms)])
save();print('PRIVATE',w,flush=True)
try:
 assert auth();env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*bs['boundary']]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
 for n in order:
  assert auth(),('source/provider drift before',n)
  out=lib/'DiophantineConsistency'/(n+'.olean');cmd=['/usr/bin/ionice','-c','3','/usr/bin/nice','-n','10','/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M6000','-j1','-DElab.async=false','-o',str(out),str(SRC/(n+'.lean'))];t=time.monotonic()
  with (w/'logs'/(n+'.log')).open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(w/'logs'/(n+'.time')),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  rec={'name':n,'exit':code,'seconds':time.monotonic()-t,'source_sha256':sourceh[n],'object_sha256':sha(out) if out.exists() else None,'log_sha256':sha(w/'logs'/(n+'.log'))};state['records'].append(rec);save();assert code==0 and auth(),('compile/auth failure',n);print('PASS',n,flush=True)
 state['status']='PASS';save();print('PASS',w,flush=True)
except BaseException as e:state.update(status='FAILED',failure=repr(e));save();raise
