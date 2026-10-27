from pathlib import Path
import json, hashlib, re, os, shutil, subprocess, tempfile, time
R=Path('/home/codex/.codex/worktrees/46be/Proofs')
DC=R/'Computability/DiophantineConsistency'
PLAN=DC/'research/c222-enum-soundness-cache-plan-20261026.json'
NAMES=['ArithmeticEnumSoundnessPerm222','ArithmeticEnumSoundnessPerm222Checks']
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p): return dict(path=str(p),sha256=sha(p))
def check(e): assert sha(e['path'])==e['sha256'],e['path']
def save(p,d): p.write_text(json.dumps(d,indent=2)+'\n')
assert sha(PLAN)=='a05011cfec564ec9a2647ddbbefe87a34c56d4bb5324037d8e27530acd0bf210'
a=json.loads(PLAN.read_text());mods=a['modules'];assert len(mods)==145
assert sum(m['module'].startswith('Foundation.')for m in mods)==95
assert sum(len(m['objects'])for m in mods)==430 and len(a['external'])==38
pins=[rec(PLAN),rec(__file__),*a['pins']]
ROOT=Path('/tmp/command-preservationperm222-root-peer-zgnedt9_/ROOT.json')
assert sha(ROOT)=='2931db9ecf17d6a6ea4b59346ea9d4ffb44a111599590277f27d680a4564f44a'
rroot=json.loads(ROOT.read_text()); assert rroot['status']=='PASS'
r=rroot['records'][0]; assert r['module']=='DiophantineConsistency.ArithmeticCommandPreservationPerm222'
expected='c59af1aeca3ac8b8453ab7255fede4a1c94099e08c3a47187ba2fd90578a6e38'
assert r['object']['sha256']==expected and r['matches_author'] is True
pins.extend([rec(ROOT),rroot['inputs'],rroot['driver']])
for key in ['source','snapshot','object','log','timing']:pins.append(r[key])
m=next(m for m in mods if m['module']==r['module'])
assert m['source_sha256']==r['source']['sha256'] and m['objects'][0]['sha256']==expected
original_preservation_provider=m['objects']; m['objects']=[r['object']]
m['selected_provider']=rec(ROOT);m['provider_status']='Root independent fresh replay PASS, byte-identical to author; explicitly authorized accepted provider.'
for m in mods:
 assert sha(m['source'])==m['source_sha256']
 actual=list(dict.fromkeys(['Init']+[n for line in re.findall(r'^(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',Path(m['source']).read_text(),re.M)for n in line.split('--',1)[0].split()]))
 assert actual==list(dict.fromkeys(m['imports'])),m['module']
 pins.append(dict(path=m['source'],sha256=m['source_sha256']));pins.extend(m['objects'])
pins.extend(a['external']);pins.append(a['compiler'])
for e in pins:check(e)
sources=[rec(DC/'Lean/DiophantineConsistency'/(n+'.lean'))for n in NAMES]
assert re.findall(r'^import (\S+)',Path(sources[0]['path']).read_text(),re.M)==a['direct_imports']
assert re.findall(r'^import (\S+)',Path(sources[1]['path']).read_text(),re.M)==['DiophantineConsistency.'+NAMES[0]]
assert shutil.disk_usage('/tmp').free>=512*1024**2
p=Path(tempfile.mkdtemp(prefix='enum-soundnessperm222-controller-author-'));lib=p/'lib';lib.mkdir()
for m in mods:
 for o in m['objects']:
  q=lib/Path(*m['module'].split('.')[:-1])/Path(o['path']).name
  q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(o['path'])
i=dict(prerequisite_review_status='Root explicitly accepted Preservation after independent fresh byte-identical replay; the original frozen cache plan is retained unchanged.',preservation_root=rec(ROOT),original_preservation_provider=original_preservation_provider,modules=mods,pins=pins,compiler=a['compiler'],lean_path=':'.join([str(lib),*a['inherited_external_search_paths']]),counts=a['counts'],plan=rec(PLAN))
save(p/'inputs.json',i)
s=dict(status='RUNNING',inputs=rec(p/'inputs.json'),driver=rec(__file__),private=str(p),records=[])
save(p/'RESULT.json',s)
Path('/tmp/enum-soundnessperm222-controller-author-location.txt').write_text(str(p))
with Path('/tmp/enum-soundnessperm222-controller-author-attempts.txt').open('a')as f:f.write(str(p)+'\n')
env=dict(os.environ,LEAN_PATH=i['lean_path'],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
print('PRIVATE '+str(p),flush=True)
try:
 for n,src,expected in zip(NAMES,sources,[0,12]):
  assert shutil.disk_usage(p).free>=512*1024**2
  check(src);snap=p/(n+'.lean');shutil.copyfile(src['path'],snap)
  out=lib/'DiophantineConsistency'/(n+'.olean');assert not out.exists()and not out.is_symlink()
  log=p/(n+'.log');timing=p/(n+'.time');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),src['path']];t=time.monotonic()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  r=dict(module='DiophantineConsistency.'+n,source=src,snapshot=rec(snap),command=cmd,seconds=time.monotonic()-t,exit_code=code,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None)
  s['records'].append(r);save(p/'RESULT.json',s);print(json.dumps(r),flush=True);check(src)
  if code:print(log.read_text(),flush=True);raise RuntimeError('Compile failed '+n)
  reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());r['axiom_reports']=reports
  assert len(reports)==expected
  for name,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
  assert not re.search(r'\b(?:error|warning):|sorryAx',log.read_text())
  if expected==0:assert log.read_text()==''
  save(p/'RESULT.json',s)
 for e in pins:check(e)
 for e in sources:check(e)
 assert shutil.disk_usage(p).free>=512*1024**2
 s.update(status='PASS',free_bytes=shutil.disk_usage(p).free);save(p/'RESULT.json',s);print('PASS '+str(p),flush=True)
except BaseException as e:
 s.update(status='FAILED',failure=str(e));save(p/'RESULT.json',s);raise
