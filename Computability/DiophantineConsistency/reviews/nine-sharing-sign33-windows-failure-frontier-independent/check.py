import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-windows-check';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-windows-check-20261106');n='Sign33Windows';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='accb8bc5fae815c4a739129b4dc6f9f3d4ee83b811033161fbdc6380e352ab6d';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and len(s['rows'])==1 and s['failure']=="RuntimeError('compile failed Sign33Windows')"
assert sha(a/'outer-observation.json')=='894132238e374194384ed4880aa8b7a70895fc8facb4790ef2574a7431818361';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==50522 and o['numeric_exit']==1
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='01c97dbea6ac97215cc0b50eea54052b1e6d7ab29977902db2568168223a255f' and sha(p/'src/DiophantineConsistency'/f'{n}.lean')==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'];assert r['deps']['exit']==0 and r['compile']['exit']==1 and r['compile']['stop_reason'] is None and not r['compile']['monitor_errors'] and not r['compile']['observed_descendant_pids']
for phase in ('deps','compile'):assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==r[phase]['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='577ca38eca4bcad152d14f6927f7144a5a7e233c5d3e1d650ea1516f23a33d12' and 'Unknown identifier `absdiff`' in log and 'sorryAx' in log and 'error(lean.unknownIdentifier)' in log and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
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
print(json.dumps({'status':'PASS_FAILED_RUN_AUDIT','author_recorded_session':50522,'author_recorded_exit':1,'failure':'Lean unknown identifier absdiff; sorryAx is failed declaration report','guard_slots':150,'overlay_links':1162,'scope':'No successful theorem/object; no whole-run postflight or Lean replay.'},indent=2,sort_keys=True))
