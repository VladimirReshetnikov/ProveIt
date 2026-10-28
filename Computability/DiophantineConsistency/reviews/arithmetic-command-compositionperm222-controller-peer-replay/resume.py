from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
p=Path('/tmp/command-compositionperm222-controller-peer-d_j3izsj');lib=p/'lib'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
 if not c:raise RuntimeError(m)
def rec(p):return {'path':str(p),'sha256':sha(p)}
def check(e):require(sha(e['path'])==e['sha256'],'pin '+e['path'])
packet=V/'arithmetic-command-compositionperm222-replay.json'
require(sha(packet)=='030dd9838e7d5d15546f6184922cd7fa543bb4f9ed2bc38ae01049cc967ad957','packet')
a=json.loads(packet.read_text());check(a['inputs']);i=json.loads(Path(a['inputs']['path']).read_text())
result=json.loads((p/'RESULT.json').read_text());require(len(result['records'])==1 and result['records'][0]['exit_code']==0,'single completed main')
check(result['driver']);check(a['driver']);check(a['bundle_manifest'])
for f in json.loads(Path(a['bundle_manifest']['path']).read_text())['files']:
 check({'path':str(Path(a['bundle_manifest']['path']).parent/f['path']),'sha256':f['sha256']})
def recheck():
 for q in i['pins']:check(q)
 check(i['compiler'])
 for q in i['external']:check(q)
 for r in a['records']:check(r['source'])
 for r in i['modules']:
  check({'path':r['source'],'sha256':r['source_sha256']})
  raw=re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',Path(r['source']).read_text(),re.M)
  actual=list(dict.fromkeys(['Init']+[d for line in raw for d in line.split('--',1)[0].split()]))
  require(actual==r['imports'],'imports '+r['module'])
  for o in r['objects']:
   check(o);q=lib/Path(*r['module'].split('.')[:-1])/Path(o['path']).name
   require(q.is_symlink() and q.resolve()==Path(o['path']).resolve(),'private provider '+str(q))
recheck();require(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
main=result['records'][0]
for k in ['source','snapshot','log','timing','object']:check(main[k])
require(Path(main['log']['path']).read_text()=='','empty main')
main['byte_identical_author']=main['object']['sha256']==a['records'][0]['object']['sha256'];main['axioms']=[]
result['resume_driver']=rec(__file__)
result['preserved_partial']=rec(p/'RESULT-before-resume.json')
result['author_receipt']=rec(V/'arithmetic-command-compositionperm222-author.md')
result['interruption']={'reason':'512MiB reserve failed after successful main, before any Checks invocation','observed_free_bytes':535957504,'scope':'No compiler failure, prerequisite rebuild, cleanup or main rerun. Resume compiles only the missing check leaf after full pin reauthentication.'}
result['resume_free_bytes_before']=shutil.disk_usage('/tmp').free
ar=a['records'][1];n=ar['module'];require(n=='DiophantineConsistency.ArithmeticCommandCompositionPerm222Checks','checks only')
source=Path(ar['source']['path']);snap=p/(n+'.lean');require(not snap.exists(),'checks never invoked');snap.write_bytes(source.read_bytes())
out=lib/Path(*n.split('.')).with_suffix('.olean');require(not out.exists(),'fresh output')
log=p/(n+'.txt');timing=p/(n+'.time');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(source)]
env=dict(os.environ,LEAN_PATH=result['lean_path'],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
print('START '+n,flush=True);t=time.monotonic()
with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
r={'module':n,'command':cmd,'source':rec(source),'snapshot':rec(snap),'exit_code':code,'seconds':time.monotonic()-t,'log':rec(log),'timing':rec(timing),'object':rec(out)if code==0 else None}
result['records'].append(r);(p/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(r),flush=True);print(log.read_text(),flush=True);require(code==0,'compiler failure')
r['byte_identical_author']=sha(out)==ar['object']['sha256']
raw=log.read_text();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw,re.S);r['axioms']=reports
require(len(reports)==13 and all(set(x.strip()for x in xs.split(','))=={'propext','Classical.choice','Quot.sound'}for _,xs in reports),'13 standard reports')
require(re.sub(r"'[^']+' depends on axioms: \[[^\]]*\]",'',raw,flags=re.S).strip()=='','no other diagnostics')
recheck();result.update(status='PASS',free_bytes=shutil.disk_usage('/tmp').free)
(p/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
bundle=V/'arithmetic-command-compositionperm222-controller-peer-replay';bundle.mkdir(exist_ok=False)
for r in result['records']:
 for k in ['snapshot','log','timing']:
  q=Path(r[k]['path']);shutil.copyfile(q,bundle/q.name)
shutil.copyfile(result['driver']['path'],bundle/'replay.py');shutil.copyfile(__file__,bundle/'resume.py');shutil.copyfile(p/'RESULT.json',bundle/'RESULT.json')
manifest={'files':[rec(q)for q in sorted(bundle.iterdir())]};(bundle/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n');result['bundle_manifest']=rec(bundle/'FILES.json')
q=V/'arithmetic-command-compositionperm222-controller-peer-replay.json';q.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','record':rec(q),'private':str(p),'matches':[r['byte_identical_author']for r in result['records']]},indent=2))
