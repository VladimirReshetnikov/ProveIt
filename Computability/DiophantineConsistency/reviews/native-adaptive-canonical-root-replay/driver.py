from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
DC=ROOT/'Computability/DiophantineConsistency'
PLAN=DC/'research/adaptive-canonical2011-cache-plan.json'
PROPOSAL=DC/'research/adaptive-canonical2011-proposal.md'
NAMES=['DiophantineConsistency.NativeAdaptiveCanonical','DiophantineConsistency.NativeAdaptiveCanonicalChecks']
pins={}
def record(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def check(p):
 a=record(p['path']);require(a['sha256']==p['sha256'],'hash '+p['path']);pins[a['path']]=a;return a
def save(p,a):Path(p).write_text(json.dumps(a,indent=2)+'\n')
def imports(p):
 s=Path(p).read_text();out=[];i=d=0
 while i<len(s):
  pair=s[i:i+2]
  if d:
   if pair=='/-':d+=1;i+=2
   elif pair=='-/':d-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif pair=='/-':d=1;i+=2
  elif pair=='--':
   while i<len(s) and s[i]!='\n':i+=1
  else:out.append(s[i]);i+=1
 require(d==0,'comment')
 return list(dict.fromkeys(['Init']+[n for l in re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',''.join(out),re.M) for n in l.split()]))
AUTHOR=DC/'reviews/native-adaptive-canonical-replay.json'
check(dict(path=str(AUTHOR),sha256='58de59cb7760d68073683dde5ce0c71c6d8f60634c9946298e1c7e5bc7ccc8f3'))
author=json.loads(AUTHOR.read_text())
check(dict(path=str(DC/'reviews/native-adaptive-canonical-author.md'),sha256='3f18cd5deebc15732107914845ccbcea6aac36770350bf971dc094ba5ab9b6dd'))
manifest=DC/'reviews/native-adaptive-canonical-replay/FILES.json'
check(dict(path=str(manifest),sha256='9d8e0a544ec7b252c29fa394fec0358a2a46cfee286da9b7ab3995730ee1d589'))
items=json.loads(manifest.read_text());require(len(items)==45,'45 author evidence files')
for r in items:check(dict(r,path=str(manifest.parent/r['path'])))
check(author['inputs']);check(author['driver'])
require(author['final']['status']=='PASS','author final pass')
check(dict(path=str(PLAN),sha256='e4f5488109fb5fcb719352e0c4af1043b7446c2928adedb8f2793a059155012a'))
check(dict(path=str(PROPOSAL),sha256='0d92ad3ab179c4193bb5ee6df05b6356d3bf3ec3e905ada98c15fae1811ea57e'))
plan=json.loads(PLAN.read_text());part=plan['canonical']
require(part['counts']==dict(custom=75,external=38,external_companions=114),'scope')
for p in plan['providers']:check(p)
check(plan['compiler'])
byname={r['module']:r for r in plan['selected_custom']}
selected=[byname[n] for n in part['custom_topological']]
boundary=[r for r in plan['external_boundary'] if r['module'] in part['external_boundaries']]
for r in selected:
 for k in ['source','object','original_object']:check(r[k])
 require(imports(r['source']['path'])==r['actual_imports'],'imports '+r['module'])
for r in boundary:
 check(r['source'])
 for p in r['artifacts']:check(p)
known={r['module'] for r in selected};edge={r['module'] for r in boundary};seen=set();used=set()
def visit(n):
 if n not in known:require(n in edge,'unknown '+n);used.add(n);return
 if n in seen:return
 seen.add(n)
 for k in byname[n]['actual_imports']:visit(k)
for n in part['imports']:visit(n)
require(seen==known and used==edge,'closed exact DAG')
sources=[dict(module=n,**record(DC/'Lean'/Path(*n.split('.')).with_suffix('.lean'))) for n in NAMES]
require(imports(sources[0]['path'])==['Init',*part['imports']],'main imports')
require(imports(sources[1]['path'])==['Init',NAMES[0]],'checks imports')
require(sources==[r['source'] for r in author['final']['records']],'frozen source equality')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
private=Path(tempfile.mkdtemp(prefix='native-adaptive-canonical-root-'));lib=private/'lib';logs=private/'logs';lib.mkdir();logs.mkdir()
shutil.copyfile(__file__,private/'driver.py');shutil.copyfile(PLAN,private/'plan.json');shutil.copyfile(PROPOSAL,private/'proposal.md')
for s in sources:shutil.copyfile(s['path'],private/(s['module'].split('.')[-1]+'.input.lean'))
for r in selected:
 out=lib/Path(*r['module'].split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 out.symlink_to(Path(r['object']['path']).resolve())
graphroot=json.loads(Path(plan['providers'][0]['path']).read_text())
paths=[str(lib),*graphroot['LEAN_PATH'][1:]]
inputs=dict(plan=record(PLAN),proposal=record(PROPOSAL),compiler=plan['compiler'],selected_custom=selected,
 external_boundary=boundary,sources=sources,LEAN_PATH=paths,pins=list(pins.values()))
save(private/'inputs.json',inputs)
state=dict(status='RUNNING',private=str(private),driver=record(__file__),inputs=record(private/'inputs.json'),records=[])
save(private/'state.json',state)
Path('/tmp/native-adaptive-canonical-root-latest').write_text(str(private)+'\n')
with Path('/tmp/native-adaptive-canonical-root-attempts').open('a') as f:f.write(str(private)+'\n')
env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
print('PRIVATE '+str(private),flush=True)
try:
 for source,count in zip(sources,[0,6]):
  require(shutil.disk_usage(private).free>=512*1024**2,'command reserve');check(source)
  short=source['module'].split('.')[-1];out=lib/Path(*source['module'].split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
  require(not out.exists() and not out.is_symlink(),'fresh output')
  log=logs/(short+'.log');timing=logs/(short+'.time');snapshot=logs/(short+'.lean');shutil.copyfile(source['path'],snapshot)
  cmd=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),source['path']]
  print('START '+short,flush=True);start=time.monotonic()
  with log.open('w') as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  rec=dict(module=source['module'],source=source,snapshot=record(snapshot),command=cmd,exit_code=code,seconds=time.monotonic()-start,log=record(log),timing=record(timing))
  state['records'].append(rec);save(private/'state.json',state);print(log.read_text(),flush=True)
  require(code==0,'compile '+short);require(not re.search(r'\b(?:warning|error|sorryAx)\b',log.read_text()),'diagnostics')
  reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text())
  require(len(reports)==count,'report count')
  for n,a in reports:require(set(re.findall('[A-Za-z][A-Za-z.]*',a))<={'propext','Classical.choice','Quot.sound'},'axioms '+n)
  require(out.is_file() and not out.is_symlink(),'regular output')
  rec.update(object=record(out),axiom_reports=reports)
  expected=next(r for r in author['final']['records'] if r['module']==source['module'])
  check(expected['object']);check(expected['log'])
  require(rec['object']['sha256']==expected['object']['sha256'],'author/ROOT object equality')
  require(reports==[tuple(x) for x in expected['axiom_reports']],'author/ROOT reports equality')
  require(log.read_bytes()==Path(expected['log']['path']).read_bytes(),'author/ROOT log equality')
  save(private/'state.json',state);check(source)
 for p in list(pins.values()):check(p)
 require(shutil.disk_usage(private).free>=512*1024**2,'final reserve')
 state.update(status='PASS',unique_pins=len(pins),final_free_bytes=shutil.disk_usage(private).free);save(private/'state.json',state);print('PASS '+str(private),flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(private/'state.json',state);raise
