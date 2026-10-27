from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,tempfile,time
ROOT=Path('/home/codex/.codex/worktrees/46be/Proofs')
DC=ROOT/'Computability/DiophantineConsistency'
PLAN=DC/'research/adaptive-canonical2011-cache-plan.json'
PROPOSAL=DC/'research/adaptive-canonical2011-proposal.md'
CANON=DC/'reviews/native-adaptive-canonical-root-replay'
NAMES=['DiophantineConsistency.NativeAdaptiveCurrent2011','DiophantineConsistency.NativeAdaptiveCurrent2011Checks']
IMPORTS=['DiophantineConsistency.NativeAdaptiveCanonical','DiophantineConsistency.NativeOrdinarySourceConstruction']
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
check(dict(path=str(PLAN),sha256='e4f5488109fb5fcb719352e0c4af1043b7446c2928adedb8f2793a059155012a'))
check(dict(path=str(PROPOSAL),sha256='0d92ad3ab179c4193bb5ee6df05b6356d3bf3ec3e905ada98c15fae1811ea57e'))
check(dict(path=str(CANON/'state.json'),sha256='1490938dfc4cc25de991fc547eb1e3b8cbd9a88c8d47102cc1c2169a20a7f9dd'))
check(dict(path=str(CANON/'FILES.json'),sha256='81d517798d2d64461897103d5a7362821fed2978943a41b826b276b89185d363'))
for row in json.loads((CANON/'FILES.json').read_text()):
 check(dict(row,path=str(CANON/row['path'])))
canonical=json.loads((CANON/'state.json').read_text());require(canonical['status']=='PASS','canonical acceptance')
for row in canonical['records']:
 for key in ['source','snapshot','object','log','timing']:check(row[key])
require(len(canonical['records'][1]['axiom_reports'])==6,'canonical reports')
plan=json.loads(PLAN.read_text());part=plan['current']
require(part['counts']==dict(custom=376,external=64,external_companions=192),'planned scope')
for p in plan['providers']:check(p)
check(plan['compiler'])
byname={r['module']:r for r in plan['selected_custom']}
selected=[byname[n] for n in part['custom_topological']]
fresh=canonical['records'][0]
supplement=dict(module=fresh['module'],source=fresh['source'],object=fresh['object'],
 original_object=fresh['object'],actual_imports=imports(fresh['source']['path']),
 provider=str(CANON/'state.json'),accepted_fresh_in_provider=True)
require(supplement['module']==IMPORTS[0],'canonical module')
require(supplement['actual_imports']==['Init','DiophantineConsistency.NativeAdaptiveGraph','DiophantineConsistency.Carrier66Source'],'canonical imports')
selected.append(supplement);byname[supplement['module']]=supplement
require(len(selected)==377 and len({r['module'] for r in selected})==377,'complete custom scope')
boundary=[r for r in plan['external_boundary'] if r['module'] in part['external_boundaries']]
for r in selected:
 for k in ['source','object','original_object']:check(r[k])
 require(imports(r['source']['path'])==r['actual_imports'],'imports '+r['module'])
for r in boundary:
 check(r['source'])
 for p in r['artifacts']:check(p)
require(len(boundary)==64 and sum(len(r['artifacts']) for r in boundary)==192,'external scope')
known={r['module'] for r in selected};edge={r['module'] for r in boundary};seen=set();used=set()
def visit(n):
 if n not in known:require(n in edge,'unknown '+n);used.add(n);return
 if n in seen:return
 seen.add(n)
 for k in byname[n]['actual_imports']:visit(k)
for n in IMPORTS:visit(n)
require(seen==known and used==edge,'closed exact DAG')
sources=[dict(module=n,**record(DC/'Lean'/Path(*n.split('.')).with_suffix('.lean'))) for n in NAMES]
require(imports(sources[0]['path'])==['Init',*IMPORTS],'main imports')
require(imports(sources[1]['path'])==['Init',NAMES[0]],'checks imports')
require(shutil.disk_usage('/tmp').free>=512*1024**2,'reserve')
private=Path(tempfile.mkdtemp(prefix='native-adaptive-current2011-'));lib=private/'lib';logs=private/'logs';lib.mkdir();logs.mkdir()
shutil.copyfile(__file__,private/'driver.py');shutil.copyfile(PLAN,private/'plan.json');shutil.copyfile(PROPOSAL,private/'proposal.md')
shutil.copyfile(CANON/'state.json',private/'canonical-root-state.json');shutil.copyfile(CANON/'FILES.json',private/'canonical-root-FILES.json')
for s in sources:shutil.copyfile(s['path'],private/(s['module'].split('.')[-1]+'.input.lean'))
for r in selected:
 out=lib/Path(*r['module'].split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True)
 out.symlink_to(Path(r['object']['path']).resolve())
graphroot=json.loads(Path(plan['providers'][0]['path']).read_text())
paths=[str(lib),*graphroot['LEAN_PATH'][1:]]
for r in selected+boundary:
 rel=Path(*r['module'].split('.')).with_suffix('.olean')
 first=next((Path(p)/rel for p in paths if (Path(p)/rel).exists()),None)
 require(first is not None,'missing actual provider '+r['module'])
 expected=r['object'] if 'object' in r else next(p for p in r['artifacts'] if p['path'].endswith('.olean'))
 require(record(first)['sha256']==expected['sha256'],'actual provider '+r['module'])
inputs=dict(plan=record(PLAN),proposal=record(PROPOSAL),compiler=plan['compiler'],
 canonical_acceptance=record(CANON/'state.json'),canonical_manifest=record(CANON/'FILES.json'),
 selected_custom=selected,external_boundary=boundary,sources=sources,LEAN_PATH=paths,pins=list(pins.values()))
save(private/'inputs.json',inputs)
state=dict(status='RUNNING',private=str(private),driver=record(__file__),inputs=record(private/'inputs.json'),records=[])
save(private/'state.json',state)
Path('/tmp/native-adaptive-current2011-latest').write_text(str(private)+'\n')
with Path('/tmp/native-adaptive-current2011-attempts').open('a') as f:f.write(str(private)+'\n')
env=dict(os.environ,LEAN_PATH=':'.join(paths),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
print('PRIVATE '+str(private),flush=True)
try:
 for source,count in zip(sources,[0,10]):
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
  require(out.is_file() and not out.is_symlink(),'regular output');rec.update(object=record(out),axiom_reports=reports);save(private/'state.json',state);check(source)
 for p in list(pins.values()):check(p)
 require(shutil.disk_usage(private).free>=512*1024**2,'final reserve')
 state.update(status='PASS',unique_pins=len(pins),final_free_bytes=shutil.disk_usage(private).free);save(private/'state.json',state);print('PASS '+str(private),flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save(private/'state.json',state);raise
