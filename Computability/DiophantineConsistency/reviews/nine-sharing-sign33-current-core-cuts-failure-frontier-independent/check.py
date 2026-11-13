import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-current-core-cuts-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-current-core-cuts-check-20261106');n='Sign33CurrentCoreCuts';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='3dbc059a13d3ec74be121ce9092cc2be86416842af9a8e018626063a5f83acc2';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and s['failure']=="RuntimeError('compile failed Sign33CurrentCoreCuts')"
assert sha(a/'outer-observation.json')=='3595c471349531f548a11c998e24137eaca88932029e9fb5fd7ce8e1161c93fb';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==38633 and o['numeric_exit']==1
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='362f8f5fc3e57a338e9f4fa74b8c04674727449ade76481fb326ba656b005322' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'];assert r['deps']['exit']==0 and r['compile']['exit']==1 and r['compile']['stop_reason'] is None and not r['compile']['monitor_errors'] and not r['compile']['observed_descendant_pids']
for phase in ('deps','compile'):assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==r[phase]['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='9bd918689cf72a986d532da9a357b4013df2af5de962cf925a599105c3c58396' and 'error: unsolved goals' in log and log.count('error: Type mismatch')==2 and 'sorryAx' in log and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
assert len(r['direct_guard'])==200 and len(s['overlay_links'])==1172
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY';assert not (a/'survey-after.json').exists()
for k in ('DiophantineConsistency.Sign33CurrentWindows','DiophantineConsistency.Sign33CurrentFiveWitnesses','DiophantineConsistency.ModelThirteenCoreInvariants'):
 dep=r['dependencies'][k];sel=survey['selected'][k];assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
print(json.dumps({'status':'PASS_FAILED_RUN_AUDIT','author_recorded_session':38633,'author_recorded_exit':1,'failure':'Lean three rewrite/normalization errors; sorryAx is failed declaration report','guard_slots':200,'overlay_links':1172,'scope':'No successful theorem/object; no whole-run postflight or Lean replay.'},indent=2,sort_keys=True))
