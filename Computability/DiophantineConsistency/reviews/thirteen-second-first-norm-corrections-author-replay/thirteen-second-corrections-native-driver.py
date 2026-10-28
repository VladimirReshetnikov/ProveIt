import hashlib,json,os,pathlib,re,shutil,subprocess,tempfile,time
ROOT=pathlib.Path('/home/codex/.codex/worktrees/46be/Proofs')
BASE=ROOT/'Computability/DiophantineConsistency/Lean'
PARENT=pathlib.Path('/tmp/current-narrow-native-root-2wv7shqg')
NAMES=['DiophantineConsistency.ThirteenSecondFirstNormCorrections','DiophantineConsistency.ThirteenSecondFirstNormCorrectionsChecks']
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def pin(p):return {'path':str(p),'sha256':sha(p)}
plan=json.loads((PARENT/'plan.json').read_text());state=json.loads((PARENT/'state.json').read_text())
require(state['status']=='PASS' and sha(PARENT/'plan.json')==state['plan_sha256'],'parent terminal plan')
require(sha(plan['compiler']['path'])==plan['compiler']['sha256'],'compiler')
mods={x['module']:x for x in plan['modules']}; fresh={x['module']:x for x in state['completed']}
selected=set()
def select(n):
 if n in selected:return
 selected.add(n)
 for d in mods[n]['imports']:
  if d in mods:select(d)
select('DiophantineConsistency.ThirteenUnitSphere96')
out=pathlib.Path(tempfile.mkdtemp(prefix='thirteen-second-corrections-native-'))
lib=out/'lib';lib.mkdir();(out/'logs').mkdir()
records=[];companions=[]
for m in plan['modules']:
 n=m['module']
 if n not in selected:continue
 src=m['source'];require(sha(src['path'])==src['sha256'],'current source '+n);obj=fresh[n]['object'] if n in fresh else m['object']
 require(sha(obj['path'])==obj['sha256'],'authenticated object '+n)
 p=PARENT/'lib'/(n.replace('.','/')+'.olean')
 require(sha(p)==obj['sha256'],'parent resolved object '+n)
 records.append({'module':n,'source':src,'current_source':pin(src['path']),'object':obj,'imports':m['imports'],
                 'origin':'parent-fresh' if n in fresh else 'parent-authenticated-reuse'})
 for p0 in sorted(p.parent.glob(p.stem+'.*')):
  if p0.is_file() and p0.suffix in ('.olean','.ilean','.ir','.private','.server'):
   q=lib/p0.relative_to(PARENT/'lib');q.parent.mkdir(parents=True,exist_ok=True)
   q.symlink_to(p0.resolve());companions.append(pin(p0))
ROOT84=pathlib.Path('/tmp/firstnorm92-current-root-kvit12kz')
root84=json.loads((ROOT84/'ROOT.json').read_text())
require(root84['status']=='PASS','root84 terminal')
require(root84['parent_plan_sha256']==sha(PARENT/'plan.json') and
        root84['parent_state_sha256']==sha(PARENT/'state.json'),'root84 same parent')
for x in root84['pins']:require(sha(x['path'])==x['sha256'],'root84 evidence')
r84=root84['completed'][0]
require(r84['module']=='DiophantineConsistency.ThirteenFirstNormCorrection92' and r84['exit_code']==0,'root84 actual module')
for kind in ('source','object'):require(sha(r84[kind]['path'])==r84[kind]['sha256'],'root84 '+kind)
p84=pathlib.Path(r84['object']['path'])
for c in sorted(p84.parent.glob(p84.stem+'.*')):
 if c.is_file() and c.suffix in ('.olean','.ilean','.ir','.private','.server'):
  q=lib/c.relative_to(ROOT84/'lib');q.parent.mkdir(parents=True,exist_ok=True)
  q.symlink_to(c.resolve());companions.append(pin(c))
records.append({'module':r84['module'],'source':r84['source'],'current_source':pin(r84['source']['path']),
 'object':r84['object'],'imports':['DiophantineConsistency.ThirteenUnitSphere96'],
 'origin':'root84-fresh-current'})
sources=[{'module':n,**pin(BASE/(n.replace('.','/')+'.lean'))} for n in NAMES]
inputs={'parent_plan':pin(PARENT/'plan.json'),'parent_state':pin(PARENT/'state.json'),
        'root84_receipt':pin(ROOT84/'ROOT.json'),'compiler':plan['compiler'],'sources':sources,'selected_custom_count':len(records),
        'selected_custom':records,'companions':companions,
        'LEAN_PATH':[str(lib)]+plan['external_lean_path'],
        'scope':'Two fresh leaves over the exact selected current narrow-native parent closure. All selected source and object pins checked before and after. Cached dependencies are reused, not rebuilt.'}
(out/'inputs.json').write_text(json.dumps(inputs,indent=2)+'\n')
pathlib.Path('/tmp/thirteen-second-corrections-native-latest').write_text(str(out)+'\n')
env=dict(os.environ,LEAN_PATH=':'.join(inputs['LEAN_PATH']),LEAN_NUM_THREADS='1');results=[]
for s in sources:
 require(shutil.disk_usage('/tmp').free>512*1024**2,'512MiB reserve')
 short=s['module'].split('.')[-1];log=out/'logs'/(short+'.log');tm=out/'logs'/(short+'.time')
 snap=out/'logs'/(short+'.lean');snap.write_bytes(pathlib.Path(s['path']).read_bytes())
 target=lib/(s['module'].replace('.','/')+'.olean')
 command=[plan['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(target),s['path']]
 print('START '+s['module'],flush=True);start=time.monotonic()
 with log.open('w') as f:
  result=subprocess.run(['/usr/bin/time','-v','-o',str(tm)]+command,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
 reports=re.findall(r"'([^']+)' depends on axioms: \[(.*?)\]",log.read_text(),re.S)
 if result.returncode==0:
  require(all(set(a.replace(' ','').replace('\n','').split(',')) <= {'propext','Classical.choice','Quot.sound'} for _,a in reports),'standard axiom reports')
  require(len(reports)==(10 if short.endswith('Checks') else 0),'expected report count')
 r=dict(s,axiom_reports=reports,command=command,exit_code=result.returncode,seconds=time.monotonic()-start,
        log=pin(log),timing=pin(tm),snapshot=pin(snap))
 require(sha(s['path'])==s['sha256'],'target source drift')
 if result.returncode==0:r['object']=pin(target)
 results.append(r);(out/'run.json').write_text(json.dumps(results,indent=2)+'\n')
 print(json.dumps(r),flush=True);print(log.read_text(),flush=True)
 if result.returncode:raise SystemExit(result.returncode)
for r in records:
 r['post_current_source']=pin(r['source']['path']);require(r['post_current_source']['sha256']==r['source']['sha256'],'current source postcheck')
 require(sha(r['object']['path'])==r['object']['sha256'],'object postcheck')
for r in companions:require(sha(r['path'])==r['sha256'],'companion postcheck')
require(sha(inputs['compiler']['path'])==inputs['compiler']['sha256'],'compiler postcheck')
(out/'post-sources.json').write_text(json.dumps([{'module':r['module'],'source':r['post_current_source']} for r in records],indent=2)+'\n')
print('PASS '+str(out),flush=True)
