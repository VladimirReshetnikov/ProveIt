import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-scoped-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-compact-scoped-check-20261106');n='Norm38MacroScoped';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='d6b5fbbc57edfa3fe67537b77402ebe72e196a2557de728bbbe287e508167cd2';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and s['failure']=="RuntimeError('compile failed Norm38MacroScoped')"
assert sha(a/'outer-terminal-author-record.json')=='ff6a5b46fbf0e2373f4826512c114531bd5320914a2a5295b8ea166d62318611';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==15898 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='db7aef04c0088a9e579d8f703489c366fd1e6207edfc37413a20e72fd4b27ba2' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'];assert r['deps']['exit']==0 and r['compile']['exit']==1 and r['compile']['stop_reason'] is None and not r['compile']['monitor_errors'] and not r['compile']['observed_descendant_pids']
for phase in ('deps','compile'):assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==r[phase]['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='8ed78797e0ce65bb0b33b9b0e924c0c17a2f387f51ddc113db0ab7985caf77e7' and 'failed to synthesize' in log and 'Decidable Norm38MacroRecipe.WellScopedTarget' in log and 'sorryAx' in log and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1166
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
dep=r['dependencies']['DiophantineConsistency.Norm38MacroRecipe'];check(dep['path'],'c1c8213d2c752991e7404820521fcd6466511b187a0648c000894254f4bd7129',dep['realpath']);assert dep['sha256']=='c1c8213d2c752991e7404820521fcd6466511b187a0648c000894254f4bd7129' and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
print(json.dumps({'status':'PASS_FAILED_RUN_AUDIT','author_session':15898,'author_exit':1,'failure':'unavailable Decidable instance for opaque WellScopedTarget; sorryAx is failed declaration report','guard_slots':100,'overlay_links':1166,'scope':'No scoping theorem, no postflight or Lean replay.'},indent=2,sort_keys=True))
