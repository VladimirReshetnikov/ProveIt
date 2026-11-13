import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-prefix-group01-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-prefix-group01-check-20261106');n='Norm38MacroPrefixGroup01';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='b5be6f0badd09341fe0ea3c5f8bf0b2022ff52862741f966f14288074e97cfcf';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and s['failure']=="RuntimeError('compile failed Norm38MacroPrefixGroup01')"
assert sha(a/'outer-terminal-author-record.json')=='1fdf3e248bc9fb005a45467ea94a69ca8d958f0d0a926062f54f3d80f3923255';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==35327 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='f0aebaa5f8a5f9cf601efc12d36bc0e14cf54373941f61071abb7898134e6926' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'];assert r['deps']['exit']==0 and r['compile']['exit']==1 and r['compile']['stop_reason'] is None and not r['compile']['monitor_errors'] and not r['compile']['observed_descendant_pids']
for phase in ('deps','compile'):assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==r[phase]['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='a320a8be9c5f41ef3a524005e2840bf5cce1da95fc301919f6d87d8043629310' and log.count('Tactic `rewrite` failed')==2 and "prefix_B' depends on axioms: [propext, Classical.choice, Quot.sound]" in log and log.count('sorryAx')==2 and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
assert len(r['direct_guard'])==100 and len(s['overlay_links'])==1169
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
dep=r['dependencies']['DiophantineConsistency.Norm38MacroPrefixFirst'];check(dep['path'],'a69ba5536b935e388c616cc6c624ecb8da8aaef052b3350bc09d327dd8272c9a',dep['realpath']);assert dep['sha256']=='a69ba5536b935e388c616cc6c624ecb8da8aaef052b3350bc09d327dd8272c9a' and r['direct_guard'][dep['path']]=={'sha256':dep['sha256'],'realpath':dep['realpath']}
print(json.dumps({'status':'PASS_FAILED_RUN_AUDIT','author_session':35327,'author_exit':1,'failure':'q/N rewrites failed on Fin index forms; B report clean, two sorryAx reports from failed declarations','guard_slots':100,'overlay_links':1169,'scope':'No successful module object, no postflight or Lean replay.'},indent=2,sort_keys=True))
