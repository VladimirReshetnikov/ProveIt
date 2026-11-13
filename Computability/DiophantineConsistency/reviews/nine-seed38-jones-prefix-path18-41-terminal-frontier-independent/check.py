import hashlib,json,os,subprocess,sys,re
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-prefix-path18-41-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-path18-41-check-20261106');n='Norm38MacroPath18to41';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='170ada4c0c55dc453f1b7247744909bf3af54e6fe2fbb5c15156a4882115eddd';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='964007b336c0b7b38bf49c4ec0f4b98c837ac7cfaa75ee880e4a49fca13b06b8';assert sha(a/'outer-terminal-author-record.json')=='00c94bcf22bc19c0770a246a2b4a549edc8832ede163712f67138d1e5867c5d3';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['session_id']==10243 and o['exit_code']==0 and 'not an independently retained raw transcript' in o['observation']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='2dff4ff4b5b7b8bdeb10a03410b51857a47d50c966efcaa0d4fdb98da30e31bb' and r['object_sha256']=='b245318d9c4049b569f3199955d2df27a31cdcfd49a1205ca2f8475801e32fa9'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['theorem path18_41','theorem lookup18_41']:assert x in t,x
assert 'SemanticTarget' not in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
assert "'DiophantineConsistency.Norm38MacroPath18to41.path18_41' does not depend on any axioms" in log
assert re.search(r"'DiophantineConsistency\.Norm38MacroPath18to41\.lookup18_41' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1224
dep=r['dependencies']['DiophantineConsistency.Norm38MacroPath18to34'];h='25eb31cce810ce42e877e0a36c274999d5344eba255901e8ab828d7905934dae';check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':10243,'author_exit':0,'axiom_reports':'path axiom-free; lookup [propext, Classical.choice, Quot.sound]','guard_slots':100,'overlay_links':1224,'scope':'Concrete d18 to d41 path and lookup only; no recipe semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
