import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-scoped-retry01';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-compact-scoped-retry01-20261106');n='Norm38MacroScoped';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='7dc46548c9fdd1ad5d7759c99ad015bb5119f30fef3336fba16d9bd931814e89';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='99f0c47171d85b425bba573e486a7734e03b7a700160f4046282c2de33658c07';assert sha(a/'outer-terminal-author-record.json')=='232ae32fb5ea988e08cd933ca2e746b61002eb1c2acbcd4aaf3b5b82863acdac';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==74458 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='c69c030ac6de7d911efc08273746f993731861a89ad8e13419640526a4f6a4f4' and r['object_sha256']=='6028ca240156374b27c68d542353cb591eff6367406002df1aedd88ddf0a8bb2'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
assert 'theorem recipe_well_scoped : Norm38MacroRecipe.WellScopedTarget := by' in t and 'change Norm38MacroRecipe.recipe.scoped = true' in t and '#print axioms recipe_well_scoped' in t and 'SemanticTarget' not in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
assert (a/f'{n}-compile.txt').read_text()=="'DiophantineConsistency.Norm38MacroScoped.recipe_well_scoped' does not depend on any axioms\n"
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1166
dep=r['dependencies']['DiophantineConsistency.Norm38MacroRecipe'];h='c1c8213d2c752991e7404820521fcd6466511b187a0648c000894254f4bd7129';check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':74458,'author_exit':0,'axiom_report':'does not depend on any axioms','guard_slots':100,'overlay_links':1166,'scope':'Boolean binder-scoping theorem only; no semantic theorem or JSON binding; no Lean replay.'},indent=2,sort_keys=True))
