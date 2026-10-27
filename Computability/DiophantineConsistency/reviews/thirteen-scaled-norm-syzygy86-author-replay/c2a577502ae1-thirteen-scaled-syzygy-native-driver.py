import hashlib,json,os,pathlib,re,shutil,subprocess,tempfile,time
R=pathlib.Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';BASE=R/'Computability/DiophantineConsistency/Lean'
NAMES=['DiophantineConsistency.ThirteenScaledNormSyzygy86','DiophantineConsistency.ThirteenScaledNormSyzygy86Checks']
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def check(e):require(sha(e['path'])==e['sha256'],'pin '+e['path'])
afile=V/'thirteen-second-first-norm-corrections-replay.json';require(sha(afile)=='42814c37ce37145da10d71f0450c09d892f6c183ae51ad9179538a7ec7d6abeb','parent author receipt')
a=json.loads(afile.read_text());i=a['inputs'];rp=V/'thirteen-second-first-norm-corrections-root-replay/ROOT.json';root=json.loads(rp.read_text());require(root['status']=='PASS','parent root terminal')
for e in root['pins']:check(e)
parent=root['completed'][0];require(parent['module']=='DiophantineConsistency.ThirteenSecondFirstNormCorrections' and parent['exit_code']==0,'exact parent main');check(parent['source']);check(parent['object'])
require(parent['source']['sha256']=='ea83a05732e96ebbadbab135f98018f5bcda115c887c1896b0f4be30a267bd22','parent source')
p=pathlib.Path(tempfile.mkdtemp(prefix='thirteen-scaled-syzygy-native-'));lib=p/'lib';lib.mkdir();(p/'logs').mkdir()
records=list(i['selected_custom'])+[dict(module=parent['module'],source=parent['source'],current_source=rec(parent['source']['path']),object=parent['object'],imports=['DiophantineConsistency.ThirteenFirstNormCorrection92'],origin='root97-fresh-current')]
require(len(records)==371,'exact371 cached custom modules')
pins=[rec(afile),rec(rp),i['parent_plan'],i['parent_state'],i['root84_receipt'],i['compiler'],*i['companions']]
for r in records:
 for k in ('source','current_source','object'):check(r[k]);pins.append(r[k])
 q=lib/(r['module'].replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(pathlib.Path(r['object']['path']).resolve())
# Preserve authenticated companion files needed by the same compiler.
for c in i['companions']:
 check(c);src=pathlib.Path(c['path']);mark=next((str(src).split('/lib/',1)[1] for _ in [0] if '/lib/' in str(src)),None)
 require(mark is not None,'companion relative module path');dst=lib/mark
 if not dst.exists():dst.parent.mkdir(parents=True,exist_ok=True);dst.symlink_to(src.resolve())
for e in pins:check(e)
sources=[dict(module=n,**rec(BASE/(n.replace('.','/')+'.lean'))) for n in NAMES]
inputs=dict(parent_author=rec(afile),parent_root=rec(rp),compiler=i['compiler'],sources=sources,selected_custom=records,companions=i['companions'],pins=pins,LEAN_PATH=[str(lib),*i['LEAN_PATH'][1:]],scope='371 authenticated cached custom dependencies; two fresh leaves only. No Foundation or prerequisite rebuild.')
(p/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n');pathlib.Path('/tmp/thirteen-scaled-syzygy-native-latest').write_text(str(p)+'\n')
env=dict(os.environ,LEAN_PATH=':'.join(inputs['LEAN_PATH']),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None)
state=dict(status='RUNNING',private=str(p),driver=rec(__file__),inputs=rec(p/'inputs.json'),completed=[])
def save():(p/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save()
try:
 for s in sources:
  require(shutil.disk_usage(p).free>=512*1024**2,'512MiB reserve');check(s)
  short=s['module'].split('.')[-1];out=lib/(s['module'].replace('.','/')+'.olean');log=p/'logs'/(short+'.log');tm=p/'logs'/(short+'.time');snap=p/'logs'/(short+'.lean');snap.write_bytes(pathlib.Path(s['path']).read_bytes())
  cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),s['path']];start=time.monotonic();print('START '+s['module'],flush=True)
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(tm),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
  item=dict(module=s['module'],source=s,command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(tm),snapshot=rec(snap));state['completed'].append(item);save();print(log.read_text(),flush=True);require(code==0,'fresh compile '+short)
  reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());require(len(reports)==(12 if short.endswith('Checks')else 0),'axiom report count')
  for title,ax in reports:require(set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'},title)
  item.update(object=rec(out),axiom_reports=reports);save();check(s)
 for e in pins:check(e)
 for s in sources:check(s)
 state['status']='PASS';save();print(json.dumps(state),flush=True)
except BaseException as e:
 state.update(status='FAILED',failure=str(e));save();raise
