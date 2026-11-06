import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-named-formula-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-named-formula-check-20261106');n='Norm38NamedFormula';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='7962fb5811dbb157d8739dad3d856d6fbb42685c1b0842c2d2ba71ab0ba32414';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='d55d3235bbd3636c7a1f7650b306a9786c2e2f3902bbec176599c8565b396ee5' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='0011f65367a47fd89d8ee77e4d1412589df2d0ce6b3df8e44f29561e72cf663a';assert sha(a/'outer-terminal-author-record.json')=='b0b7b6c418c7e8072e70d1e8950666bb78a8cb1220b889f75786a2a748ececfd';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==50677 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='a5a8db6833252881c37016f3b28e006168db45a8119074b04572c8341d2593e6' and r['object_sha256']=='f628947fecd14dec5840ed18aa4b362c8e1173e6cf4fbdb60722c428e23b2725'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['[CommRing R] (a : Fin 9 → R)','Norm38IPRAEndpoint.expression.evalRing a','let ν := 38','let seed := SharingSeed38.seed CurrentWindowCarry2011.ports','let z := indexZ seed 0','let y := indexY seed 0','let aa : Fin 10 → R := Fin.cons 1 a','RefinedPair.value (v.rad 0) (v.rad 1) (v.wt 0) (v.wt 1) (a 8) v.dvsr v.dvnd v.marg']:assert x in t,x
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='b133414033f7e04eda29f11128a967a5d7ac09bafa60ec67c95a89b228732a0d';assert not any(x in log for x in ['warning:','error:','sorryAx']) and "'DiophantineConsistency.Norm38NamedFormula.eval_current' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1163
for name,h in [('Norm38IPRAEndpoint','570952bced71ff043c7fa9f0f84af3e99b8a6fea2f373651f12c01e7e6c72125'),('ModelJonesSyntax','ca320ae03c5aece08482a0eb125d58c12d371ce524cce685428b0550a96c5171')]:
 dep=r['dependencies']['DiophantineConsistency.'+name];check(dep['path'],h,dep['realpath']);assert dep['sha256']==h and r['direct_guard'][dep['path']]=={'sha256':h,'realpath':dep['realpath']}
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_preflight.py')],capture_output=True,timeout=300);assert v.returncode==0 and not v.stderr and json.loads(v.stdout)['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':50677,'author_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'guard_slots':150,'overlay_links':1163,'scope':'Generic-ring evaluation to Lean symbolic RHS; human FORMULA.md is not machine-bound; no Lean replay.'},indent=2,sort_keys=True))
