from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(c,m):
 if not c:raise RuntimeError(m)
def rec(p):return {'path':str(p),'sha256':sha(p)}
def check(e):require(sha(e['path'])==e['sha256'],'pin '+e['path'])
packet=V/'arithmetic-command-replaceperm222-replay.json'
require(sha(packet)=='7761a874d97aedc5d90557f0bc861b947a146bf60be86bcb41a0ec4099863455','packet')
a=json.loads(packet.read_text());check(a['inputs']);i=json.loads(Path(a['inputs']['path']).read_text());check(a['driver']);check(a['bundle_manifest'])
for f in json.loads(Path(a['bundle_manifest']['path']).read_text())['files']:
 check({'path':str(Path(a['bundle_manifest']['path']).parent/f['path']),'sha256':f['sha256']})
mods={r['module']:r for r in i['modules']};ext={r['module']:r for r in i['external']};seen=set();ex=set()
def visit(n):
 if n in seen or n in ex:return
 if n not in mods:require(n in ext,'external '+n);ex.add(n);return
 r=mods[n];check({'path':r['source'],'sha256':r['source_sha256']})
 raw=re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',Path(r['source']).read_text(),re.M)
 imports=list(dict.fromkeys(['Init']+[d for l in raw for d in l.split('--',1)[0].split()]))
 require(imports==r['imports'],'imports '+n);seen.add(n)
 for d in imports:visit(d)
visit('DiophantineConsistency.ArithmeticCommandStepPerm222')
require(len(seen)==107 and seen==set(mods) and ex==set(ext),'closure')
require(sum(n.startswith('Foundation.') for n in seen)==86,'Foundation86')
require(sum(len(r['objects']) for r in mods.values())==365,'artifacts365')
def recheck():
 for p in i['pins']:check(p)
 check(i['compiler'])
 for e in i['external']:check(e)
 for r in a['records']:check(r['source'])
recheck();require(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
p=Path(tempfile.mkdtemp(prefix='command-replaceperm222-controller-peer-'));lib=p/'lib';lib.mkdir()
for r in i['modules']:
 for o in r['objects']:
  check(o);q=lib/Path(*r['module'].split('.')[:-1])/Path(o['path']).name;q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o['path'])
leanpath=str(lib)+':'+i['lean_path'].split(':',1)[1]
env=dict(os.environ,LEAN_PATH=leanpath,LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
result={'status':'INCOMPLETE','scope':'Independent two-leaf replacement review/replay;107 cached prerequisites,86 Foundation,365 artifacts,37 external boundaries. No old-object or whole-closure replay claim.','author_packet':rec(packet),'author_inputs':a['inputs'],'driver':rec(__file__),'private':str(p),'lean_path':leanpath,'records':[],'counts':[107,86,365,37],'inherited_pin_count':len(i['pins']),'preflight_adjustment':{'prior_driver':rec('/tmp/command-replaceperm222-controller-peer-v1.py'),'scope':'First preflight stopped before overlay creation or Lean: actual public/meta repeated imports were not deduplicated, whereas accepted inventory stores first occurrences. Parser now preserves order and deduplicates identical module names; no dependency removed or source changed.'}}
for ar in a['records']:
 require(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
 n=ar['module'];source=Path(ar['source']['path']);snap=p/(n+'.lean');snap.write_bytes(source.read_bytes());out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);require(not out.exists(),'targets absent')
 log=p/(n+'.txt');timing=p/(n+'.time');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(source)]
 print('START '+n,flush=True);t=time.monotonic()
 with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 r={'module':n,'command':cmd,'source':rec(source),'snapshot':rec(snap),'exit_code':code,'seconds':time.monotonic()-t,'log':rec(log),'timing':rec(timing),'object':rec(out)if code==0 else None}
 result['records'].append(r);(p/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(r),flush=True);print(log.read_text(),flush=True);require(code==0,'compiler failure')
 r['byte_identical_author']=sha(out)==ar['object']['sha256']
 raw=log.read_text();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",raw,re.S);r['axioms']=reports
 require(all(set(x.strip() for x in xs.split(','))=={'propext','Classical.choice','Quot.sound'}for _,xs in reports),'axioms')
 require(re.sub(r"'[^']+' depends on axioms: \[[^\]]*\]",'',raw,flags=re.S).strip()=='','diagnostics')
require(len(result['records'][0]['axioms'])==0 and len(result['records'][1]['axioms'])==13,'reports13')
recheck();result.update(status='PASS',free_bytes=shutil.disk_usage('/tmp').free)
(p/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
bundle=V/'arithmetic-command-replaceperm222-controller-peer-replay';bundle.mkdir(exist_ok=False)
for r in result['records']:
 for k in ['source','snapshot','log','timing']:
  if k=='source':continue
  q=Path(r[k]['path']);shutil.copyfile(q,bundle/q.name)
shutil.copyfile(__file__,bundle/'replay.py');shutil.copyfile(p/'RESULT.json',bundle/'RESULT.json')
manifest={'files':[rec(q)for q in sorted(bundle.iterdir())]};(bundle/'FILES.json').write_text(json.dumps(manifest,indent=2)+'\n');result['bundle_manifest']=rec(bundle/'FILES.json')
q=V/'arithmetic-command-replaceperm222-controller-peer-replay.json';q.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'PASS','record':rec(q),'private':str(p),'matches':[r['byte_identical_author']for r in result['records']]},indent=2))
