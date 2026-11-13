import hashlib,json,os,subprocess,sys,re
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-prefix-path18-34-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-path18-34-check-20261106');n='Norm38MacroPath18to34';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='e3718acde0142c4736f9b8f145372ac3822e98d009782c570f2d28df7d1b2f93';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='6588946cae30eea1dedf0065337ca019b9d1a8aa0850cfc1b3d6a1667fddcbd4';assert sha(a/'outer-terminal-author-record.json')=='8822567c6371c0047192e75a8b29e46874dfd401a5cf0b4bb85d4d15c6b02efe';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['session_id']==67612 and o['exit_code']==0 and 'not an independently retained raw transcript' in o['observation']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='3be3ce5b6535a492ff295bcdc0a54b9e8ed7addf860e60a0eb37bb80f39a6e34' and r['object_sha256']=='25eb31cce810ce42e877e0a36c274999d5344eba255901e8ab828d7905934dae'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['theorem path18_34','theorem lookup18_34']:assert x in t,x
assert 'SemanticTarget' not in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
assert "'DiophantineConsistency.Norm38MacroPath18to34.path18_34' does not depend on any axioms" in log
assert re.search(r"'DiophantineConsistency\.Norm38MacroPath18to34\.lookup18_34' depends on axioms: \[propext,\s*Classical.choice,\s*Quot.sound\]",log)
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1223
dep=r['dependencies']['DiophantineConsistency.Norm38MacroPath18to27'];h='bf606152c9813c75de33752bb7c510814bf97c1cc2a3cb66faf2a6c56c48ee79';check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':67612,'author_exit':0,'axiom_reports':'path axiom-free; lookup [propext, Classical.choice, Quot.sound]','guard_slots':100,'overlay_links':1223,'scope':'Concrete d18 to d34 path and lookup only; no recipe semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
