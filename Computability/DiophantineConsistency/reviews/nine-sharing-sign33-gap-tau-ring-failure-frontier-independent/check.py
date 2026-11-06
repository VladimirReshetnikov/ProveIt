import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-gap-tau-ring-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-gap-tau-ring-check-20261106');n='Sign33GapTauRing';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='6bd1af8637dbaa86d824ddf18a88bc336287cc074b0f640416ad01805611973c';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and s['failure']=="RuntimeError('compile failed Sign33GapTauRing')"
assert sha(a/'outer-observation.json')=='ece01b79453f99b891eefae701c546b1bf9ec4ba534df2c65dfc3f9ba60fcea6';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==86494 and o['numeric_exit']==1
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='9f7bdb432672402030947365c443d2423379dff3a37dbe4284d726d84526ab0f' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'];assert r['deps']['exit']==0 and r['compile']['exit']==1 and r['compile']['stop_reason'] is None and not r['compile']['monitor_errors'] and not r['compile']['observed_descendant_pids']
for phase in ('deps','compile'):assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==r[phase]['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='ad10f96602dfa68cd48d938ff496c71eae31c40bd47d4aed0d1364e85fea3e96' and 'unknown namespace `ModelArithmetic`' in log and 'sorryAx' in log and 'error(lean.unknownIdentifier)' in log and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1164
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY';assert not (a/'survey-after.json').exists()
for k in ('DiophantineConsistency.Sign33Windows','Sign33OrderedRing'):
 dep=r['dependencies'][k];sel=survey['selected'][k];assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
print(json.dumps({'status':'PASS_FAILED_RUN_AUDIT','author_recorded_session':86494,'author_recorded_exit':1,'failure':'Lean unknown namespace ModelArithmetic and cascading identifier errors; sorryAx is failed declaration report','guard_slots':150,'overlay_links':1164,'scope':'No successful theorem/object; no whole-run postflight or Lean replay.'},indent=2,sort_keys=True))
