import hashlib,json,os,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-compact-first-node-check';a=p/'attempt01';out=Path('/tmp/nine-seed38-jones-compact-first-node-check-20261106');n='Norm38MacroFirst';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='92fc9f29f2867707b359545fe5a4a434823b91371735a198a85575d3a3f0bcd2';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and s['failure']=="RuntimeError('compile failed Norm38MacroFirst')"
assert sha(a/'outer-terminal-author-record.json')=='48aa63dc1264361d87dfb713e44f3655a6b6bbd4f8ee4552b1d33cad3d04ba73';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==9595 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='1904331aac21711865c0933a2cd441b9354650a63098fc5a9fb5a5d59462607d' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'];assert r['deps']['exit']==0 and r['compile']['exit']==-15 and r['compile']['stop_reason']=='session_rss_limit' and r['compile']['peak_session_rss_bytes']==4303032320 and r['compile']['rss_limit_bytes']==4294967296 and not r['compile']['monitor_errors'] and not r['compile']['observed_descendant_pids']
for phase in ('deps','compile'):assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==r[phase]['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855' and log=='' and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
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
print(json.dumps({'status':'PASS_FAILED_RUN_AUDIT','author_session':9595,'author_exit':1,'failure':'sampled 4-GiB session RSS stop; Lean terminated -15 with empty log','guard_slots':100,'overlay_links':1166,'scope':'No first-node theorem, no postflight or Lean replay.'},indent=2,sort_keys=True))
