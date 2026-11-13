import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-language-retry01';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-compact-language-retry01-20261106');n='Norm38MacroLanguage';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='fe17aee787f4d403017ed5e20bd730455014e12a3a7d097a75e0e2dd3f0d4ae0';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='1c74fc56546e381c1ea5f41031e42ff9cf55a8ef151ee811b1c5b1fb5f6e5396';assert sha(a/'outer-terminal-author-record.json')=='b9f805246e73239e795d9ddf33c183c5599bc38b5512ad9c9941ee84d7212307';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==77556 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='8b25a5ac8047503064f7d044c0d17f36f39b458902b8e927c8ec685fc8677b3f' and r['object_sha256']=='7031d85f55adb8f82f96686c300443da2adf4eeb30ae743fb6f42a08509e8d65'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['inductive NExpr where','inductive Term (n : Nat) where','inductive Dag : Nat → Type where','def NExpr.scoped','def Term.scoped','def Dag.scoped','def NExpr.eval','def Term.eval','def Dag.values','Fin.snoc prev']:assert x in t,x
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
assert (a/f'{n}-compile.txt').read_bytes()==b''
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1164
dep=r['dependencies']['DiophantineConsistency.Norm38NamedFormula'];h='f628947fecd14dec5840ed18aa4b362c8e1173e6cf4fbdb60722c428e23b2725';check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':77556,'author_exit':0,'compile_log':'empty; no axiom reports requested','guard_slots':100,'overlay_links':1164,'scope':'Lean-accepted language definitions only; no recipe, scoping/semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
