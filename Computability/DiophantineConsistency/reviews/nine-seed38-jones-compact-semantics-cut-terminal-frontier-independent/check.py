import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-semantics-cut-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-compact-semantics-cut-check-20261106');n='Norm38MacroCuts';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='d791b0f684bd4c9f6f68c257a687ed97b3a24b469c9eafb852f9935f314e9b81';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='a0f2efd25793092ca45030dccd35a5cfe0bcad8675d9c03c4fcfeee2830b7f9f';assert sha(a/'outer-terminal-author-record.json')=='d3322d074e3318b5765efc3afeefcebd68a0365b2e28afe837a11af507376d3a';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==32687 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='de5a30d88de5f15a6b08f9a450e2b430104928dae8af67888f4bd92fb578da9d' and r['object_sha256']=='9c83339175c439edd66ef5a10e6a192b79621803463dbf9e8420fc6f8725bf36'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['theorem snoc_previous','theorem snoc_last','theorem eval_range','theorem eval_star']:assert x in t,x
assert 'SemanticTarget' not in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='2152350acd9509b9c3936a946c02a876bea7e4726d0fa6f1d0555c25d92af298' and 'warning:' not in log and 'error:' not in log and 'sorryAx' not in log
for theorem in ['snoc_previous','snoc_last','eval_range','eval_star']:assert f"'DiophantineConsistency.Norm38MacroCuts.{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1165
dep=r['dependencies']['DiophantineConsistency.Norm38MacroLanguage'];h='7031d85f55adb8f82f96686c300443da2adf4eeb30ae743fb6f42a08509e8d65';check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':32687,'author_exit':0,'axiom_reports':'four reports each [propext, Classical.choice, Quot.sound]','guard_slots':100,'overlay_links':1165,'scope':'Four generic snoc/range/star identities only; no recipe semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
