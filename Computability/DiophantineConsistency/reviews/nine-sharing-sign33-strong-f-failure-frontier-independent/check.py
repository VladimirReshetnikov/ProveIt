import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-strong-f-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-strong-f-check-20261106');n='Sign33StrongF';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='80899a5be35a092903a15ad21e8aba56fbd89b46daa045ea6862c51e6587719a';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and s['failure']=="RuntimeError('compile failed Sign33StrongF')"
assert sha(a/'outer-observation.json')=='bfcb4b2504990f1107ffa6eb81237b11cc125b4fbb490623328f6e5c03558719';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==1359 and o['numeric_exit']==1
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='6dae60f7b531a8af18bc2567f478ae3f26cab5b9d1195651c5c84e5a27bc47cd' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'];assert r['deps']['exit']==0 and r['compile']['exit']==1 and r['compile']['stop_reason'] is None and not r['compile']['monitor_errors'] and not r['compile']['observed_descendant_pids']
for phase in ('deps','compile'):assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==r[phase]['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='6f7c5110898c0c8670d6d5d9e05caf79d75d461235acce36ad30804adf34f47c' and '1 + 1 ≤ f' in log and '2 ≤ f' in log and 'sorryAx' in log and 'warning:' in log and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1162
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY';assert not (a/'survey-after.json').exists()
for n in ('ArithmeticPellFirstIndex','ModelDifferenceRing'):
 k='DiophantineConsistency.'+n;dep=r['dependencies'][k];sel=survey['selected'][k];assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
print(json.dumps({'status':'PASS_FAILED_RUN_AUDIT','author_recorded_session':1359,'author_recorded_exit':1,'failure':'Lean numeral normalization mismatch; sorryAx is failed declaration report','guard_slots':150,'overlay_links':1162,'scope':'No successful theorem/object; no whole-run postflight or Lean replay.'},indent=2,sort_keys=True))
