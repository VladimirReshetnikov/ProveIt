from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,sys,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
V=R/'Computability/DiophantineConsistency/reviews'
P=R/'Computability/DiophantineConsistency/research'
PLAN=P/'c222-command-block-next-cache-plan-20261026.json'
PROPOSAL=P/'c222-command-block-next-proposal-20261026.md'
LOCATION=Path('/tmp/command-blockperm222-controller-location.txt')
NAMES=['DiophantineConsistency.ArithmeticCommandBlockPerm222',
       'DiophantineConsistency.ArithmeticCommandBlockPerm222Checks']
def require(c,m):
 if not c:raise RuntimeError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return {'path':str(Path(p).resolve()),'sha256':sha(p)}
def check(r):require(sha(r['path'])==r['sha256'],'pin '+r['path'])
def imports(p):
 raw=re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',Path(p).read_text(),re.M)
 return list(dict.fromkeys(['Init']+[d for s in raw for d in s.split('--',1)[0].split()]))
def guard():require(shutil.disk_usage('/tmp').free>=512*1024**2,'512MiB reserve')
require(sha(PLAN)=='765882da8d3678e9a1a81804fe411cd6e83a1654856b31acf7a8cc10566530cf','plan')
require(sha(PROPOSAL)=='534e9a186641c99132081afb8bf313a9469f0053c1727e39a5e42a5a31548349','proposal')
plan=json.loads(PLAN.read_text())
def auth():
 count=0
 for r in plan['modules']:
  require(sha(r['source'])==r['source_sha256'],'source '+r['module']);count+=1
  require(imports(r['source'])==r['imports'],'imports '+r['module'])
  for o in r['objects']:check(o);count+=1
 for o in plan['external']:check(o);count+=1
 check(plan['compiler'])
 for q in plan['providers']:check(q)
 return count
auth()
if sys.argv[1]=='setup':
 guard();require(not LOCATION.exists(),'new private setup')
 p=Path(tempfile.mkdtemp(prefix='command-blockperm222-controller-'));lib=p/'lib';lib.mkdir()
 for r in plan['modules']:
  for o in r['objects']:
   target=lib/Path(*r['module'].split('.')[:-1])/Path(o['path']).name
   target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(o['path'])
 base=json.loads(Path(plan['providers'][0]['path']).read_text())
 package_paths=base['lean_path'].split(':')[1:]
 require(all('/.lake/packages/' in q or '/toolchains/' in q for q in package_paths),'external-only paths')
 inputs={'status':'AUTHENTICATED_BEFORE_ANY_LEAN','private':str(p),'proposal':rec(PROPOSAL),
   'plan':rec(PLAN),'driver':rec(__file__),'modules':plan['modules'],'external':plan['external'],
   'compiler':plan['compiler'],'lean_path':':'.join([str(lib),*package_paths]),
   'counts':plan['counts'],'snapshot':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
   'source_artifact_boundary_observations':auth(),'free_bytes':shutil.disk_usage('/tmp').free,
   'scope':'Only the two new block leaves will compile; 122 cached modules/95 Foundation/407 artifacts/38 boundaries. No dependency build; historical254 guides not imported.'}
 (p/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n');LOCATION.write_text(str(p)+'\n')
 print(json.dumps({'private':str(p),'inputs':rec(p/'inputs.json')}));sys.exit(0)
p=Path(LOCATION.read_text().strip());lib=p/'lib';i=json.loads((p/'inputs.json').read_text())
check(i['driver']);check(i['proposal']);check(i['plan'])
for r in i['modules']:
 for o in r['objects']:
  q=lib/Path(*r['module'].split('.')[:-1])/Path(o['path']).name
  require(q.is_symlink() and q.resolve()==Path(o['path']).resolve(),'provider '+str(q))
stage=sys.argv[1];require(stage in ['main','checks'],'stage')
n=NAMES[0 if stage=='main' else 1];source=R/'Computability/DiophantineConsistency/Lean'/Path(*n.split('.')).with_suffix('.lean')
require(imports(source)==['Init','DiophantineConsistency.ArithmeticCommandCompositionPerm222' if stage=='main' else NAMES[0]],'new imports')
attempts=sorted(p.glob(stage+'-attempt-*'));a=p/(stage+'-attempt-'+str(len(attempts)+1));a.mkdir()
snap=a/(n+'.lean');snap.write_bytes(source.read_bytes());out=a/'objects'/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True)
log=a/'lean.txt';timing=a/'time.txt';cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(source)]
r={'module':n,'stage':stage,'source':rec(source),'snapshot':rec(snap),'command':cmd,'driver':rec(__file__),
   'inputs':rec(p/'inputs.json'),'pre_observations':auth(),'free_before':shutil.disk_usage('/tmp').free}
if stage=='checks':
 current=json.loads((p/'accepted-main.json').read_text());check(current['source']);check(current['primary']);r['main_provider']=current['primary']
guard();require(not out.exists() and not out.is_symlink(),'fresh nonsymlink output')
env=dict(os.environ,LEAN_PATH=i['lean_path'],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
print('START '+stage+' '+str(a),flush=True);t=time.monotonic()
with log.open('w') as f:
 code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
r.update(exit_code=code,seconds=time.monotonic()-t,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None)
require(sha(source)==r['source']['sha256'],'source unchanged during compile')
r['post_observations']=auth();r['free_after']=shutil.disk_usage('/tmp').free
raw=log.read_text();r['axioms']=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw,re.S)
(a/'record.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True);print(raw,flush=True)
if code!=0:sys.exit(code)
require(all(set(x.strip()for x in xs.split(','))<={'propext','Classical.choice','Quot.sound'}for _,xs in r['axioms']),'standard axioms')
primary=lib/Path(*n.split('.')).with_suffix('.olean');primary.parent.mkdir(parents=True,exist_ok=True)
require(not primary.is_symlink(),'own regular primary');shutil.copyfile(out,primary)
r['primary']=rec(primary);(a/'record.json').write_text(json.dumps(r,indent=2)+'\n');(p/('accepted-'+stage+'.json')).write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'PASS':stage,'primary':r['primary'],'attempt_record':rec(a/'record.json')}),flush=True)
