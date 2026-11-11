#!/usr/bin/env python3
import hashlib,importlib.util,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];repo=D.parents[1];p=D/'research/current14-coherent-extension-runner';sha=lambda q:hashlib.sha256(Path(q).read_bytes()).hexdigest();pins={'run.py':'7645019eb1aebe3c89b2db585f059625f8d211005f1a0eec08f8732f2a2f55a3','controls.py':'4da54f274e38634555018d39351d2d9940ef312cb15265d4789537b67a5bba9a','monitor.py':'5d4f035c4acc9f2b07c25c5a35f3b1ab147f4f894a4ec1a912ffc33ac2e264b0','make_plan.py':'1b385061265e39389d70b5201595e18f8504f3e9dd04f82086a87c59d63f9579','plan.json':'0f44fb7be1c0b7deb24f7ea5a57a7be91820379f51edb6ee63cecdd424c659e9','Current14CoherentAudit.lean':'b490d50244da4088a3258f290535aceb8b75e89b8cf030277be4cc15e32bf64e'}
for f,h in pins.items():assert sha(p/f)==h
control=json.loads((p/'controls-observation.json').read_bytes());assert control['status']=='PASS_NON_LEAN_CONTROLS_AND_PREFLIGHT' and control['source_sha256']==pins and control['output_absent_before_after']
out=Path('/tmp/current14-coherent490-rebuild-20261110');assert not os.path.lexists(out)
plan=json.loads((p/'plan.json').read_bytes());entries=plan['entries'];names=[e['module'] for e in entries];assert len(names)==len(set(names))==490 and len(plan['external_direct'])==99 and sum(e['old_parent_status']=='FAILED' for e in entries)==7
obs=json.loads((D/'research/current14-coherent-extension-preflight/observation.json').read_bytes());assert names==obs['union']['observed_union_topological_order'];base=json.loads(Path('/tmp/current14-standard-fresh-build-20261104/state.json').read_bytes());base_names={r['module'] for r in base['records']};assert len(base_names)==1000 and not (set(names)&base_names)
seen=set()
for e in entries:
 n=e['module'];src=repo/e['source'];assert not Path(e['source']).is_absolute() and src.is_file() and src.resolve().is_relative_to(repo) and sha(src)==e['source_sha256'];decl=[]
 for line in src.read_text().splitlines():
  if line.startswith('import '):decl.extend(line.split('--',1)[0].split()[1:])
 assert sorted(decl)==sorted(e['imports'])
 for dep in e['imports']:assert dep in seen or dep in base_names or dep in plan['external_direct']
 seen.add(n)
# Independently verify selected tracked source contents against current HEAD blobs.
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip();paths={e['source']:e['source_sha256'] for e in entries};requests=[head+':'+s for s in paths];z=subprocess.run(['git','cat-file','--batch'],input=('\n'.join(requests)+'\n').encode(),stdout=subprocess.PIPE,stderr=subprocess.PIPE,cwd=repo,check=True,timeout=180);assert not z.stderr;buf=z.stdout;at=0
for path in paths:
 end=buf.index(b'\n',at);h=buf[at:end].split();assert len(h)==3 and h[1]==b'blob';size=int(h[2]);start=end+1;assert hashlib.sha256(buf[start:start+size]).hexdigest()==paths[path] and buf[start+size:start+size+1]==b'\n';at=start+size+1
assert at==len(buf)
# Reproduce the plan ignoring only its recorded selection HEAD.
x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'make_plan.py')],cwd=repo,capture_output=True,text=True,check=True,timeout=180);new=json.loads(x.stdout);assert not x.stderr and new['entries']==entries and new['external_direct']==plan['external_direct']
# Independent chunked-hash watchdog fault injection on an existing >4 MiB base file.
spec=importlib.util.spec_from_file_location('independent_coherent_runner',p/'run.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
class StopOnSecond:
 def __init__(self):self.count=0
 def check(self):
  self.count+=1
  if self.count==2:raise mod.Refusal('independent chunk-stop control')
w=StopOnSecond();mod.ACTIVE_WATCH=w
try:
 try:mod.sha('/tmp/current14-standard-fresh-build-20261104/state.json')
 except mod.Refusal as e:assert 'independent chunk-stop' in str(e) and w.count==2
 else:raise AssertionError('hash ignored watchdog')
finally:mod.ACTIVE_WATCH=None
# Controls include two forced receipt faults, exact duplicate axiom rejection,
# preexisting-path refusal, plan pin rejection and a terminated owned non-Lean child.
c=subprocess.run([sys.executable,'-I','-S','-B',str(p/'controls.py')],cwd=repo,capture_output=True,text=True,check=True,timeout=180);assert not c.stderr;lines=[json.loads(v) for v in c.stdout.splitlines()];assert len(lines)==2 and lines[0]['status']=='PASS_SYNTHETIC_CONTROLS' and lines[1]['status']=='PASS_NON_LEAN_CONTROLS' and lines[1]['existing_output_refused'] and lines[1]['bad_plan_pin_refused'] and lines[1]['initial_failure_recorded'] and lines[1]['child_stop_receipt_preserved'] and lines[1]['watchdog_active_during_initial_preflight'] and lines[1]['git_timeout_propagated'] and lines[1]['synthetic_monitor_stop']=='disk_floor' and lines[1]['monitor_child_exit']==-15
f=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],cwd=repo,capture_output=True,text=True,check=True,timeout=180);assert not f.stderr;pre=json.loads(f.stdout);assert pre['status']=='PASS_NO_LEAN_PREFLIGHT' and pre['stages']==490 and pre['partial_parent_stages_to_rebuild']==7 and pre['disk_stop_threshold']==5100000000 and not os.path.lexists(out)
print(json.dumps({'status':'PASS_INDEPENDENT_NO_LEAN_PRELAUNCH','stages':490,'audit_client':1,'external_direct':99,'failed_parent_stages_to_rebuild':7,'selected_source_head_blobs':len(paths),'sampled_free_bytes':pre['disk_free'],'sampled_early_stop_bytes':pre['disk_stop_threshold'],'scope':'source/route/guard/monitor point review only; not build success, full package ancestry or PDF binding'},indent=2))
