import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-recipe-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-compact-recipe-check-20261106');n='Norm38MacroRecipe';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='a50533d46160f3f5d35f9d6cb9e5619b1066e653a4336f552968ca4eb56d4bc8';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='aec7254844545b2ca54818bd3097fac4badf8601e112a8e5a61f0ee7d13de0b6';assert sha(a/'outer-terminal-author-record.json')=='c997e7d197d5cf6877c00bb1cbdd6f92a20fe7213f754b49a11570bfb69dc6af';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==67174 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='3756c5e056e9bfedd28aa1fca5d5aa01c6bbde8163332c70abced196cf6d3979' and r['object_sha256']=='c1c8213d2c752991e7404820521fcd6466511b187a0648c000894254f4bd7129'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['def recipe : Dag 45 := by','def WellScopedTarget : Prop := recipe.scoped = true','def SemanticTarget : Prop :=','recipe.values a (Fin.last 44) = Norm38IPRAEndpoint.expression.evalRing a']:assert x in t,x
assert 'theorem ' not in t and '#print axioms' not in t
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
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1165
dep=r['dependencies']['DiophantineConsistency.Norm38MacroLanguage'];h='7031d85f55adb8f82f96686c300443da2adf4eeb30ae743fb6f42a08509e8d65';check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':67174,'author_exit':0,'compile_log':'empty; no axiom reports requested','guard_slots':100,'overlay_links':1165,'scope':'Lean-accepted recipe and open proposition definitions only; no scoping/semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
