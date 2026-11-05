#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
PKT='nine-current-fresh-jones-client'
TMP='/tmp/nine-fresh-jones-client-20261105'
STATE='469b279c32677e416e757dcd59835ea0514d1e524338d3c451ae8cfa8e446439'
SESSION=78298
BASE='5003d43d0deb8c7339766d9ea62bb3866a66fba9d4d277fcca5f4afcf0db33d4'
RUNNER='48415b604210df155c6803472758e243350600bc8bdc59ba24024b13a526109f'
MOD='NineFreshJones'
SOURCE='f828cdaf1d917dbc0807abc6806db7c96e4649c1983023e9950003cb6b70f2ac'
OBJ='9960f8baa9c5a058d8d472ce1600742bc53fa0030ee78add105b17744912d0df'
GUARDS=300
LINKS=1054
REPORTS=['DiophantineConsistency.NineFreshJones.jonesModel']
SCOPE='All-model generic Jones correspondence, not iPRA endpoint or Lean replay.'
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research';P=R/PKT;A=P/'attempt01';OUT=pathlib.Path(TMP)
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'state.json').read_text());o=json.loads((A/'outer-terminal.json').read_text());assert sha(A/'state.json')==STATE and (d['status'],o['actual_session'],o['exit_code'],d['base_state_sha256'])==('PASS',SESSION,0,BASE)
assert sha(P/'run.py')==d['runner_sha256']==RUNNER and len(d['rows'])==1;r=d['rows'][0];assert r['module']==MOD and r['source_sha256']==SOURCE==sha(P/(MOD+'.lean'))==sha(OUT/'src/DiophantineConsistency'/(MOD+'.lean'))
for typ in ['deps','compile']:
 x=r[typ];log=A/(MOD+'-'+typ+'.txt');assert x['exit']==0 and x['stop_reason'] is None and not x['monitor_errors'] and not x['observed_descendant_pids'] and sha(log)==x['log_sha256']
 assert x['rss_limit_bytes']==4*1024**3 and x['host_floor_bytes']==10*1024**3 and x['timeout_seconds']==120 and x['sampling_interval_seconds']==0.1 and x['peak_session_rss_bytes']<4*1024**3 and x['min_host_available_bytes']>=10*1024**3
assert r['object_sha256']==OBJ==sha(OUT/'lib/DiophantineConsistency'/(MOD+'.olean')) and len(r['direct_guard'])==GUARDS and len(d['overlay_links'])==LINKS
for k,v in r['direct_guard'].items():
 p=pathlib.Path(k)
 if v is None:assert not os.path.lexists(p),p
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
for k,v in d['overlay_links'].items():assert pathlib.Path(k).is_symlink() and str(pathlib.Path(k).resolve())==v,k
log=(A/(MOD+'-compile.txt')).read_text();reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]+)\]",log);assert [x[0] for x in reports]==REPORTS and all([x.strip() for x in a.split(',')]==['propext','Classical.choice','Quot.sound'] for _,a in reports);assert 'sorryAx' not in log and 'error:' not in log
old=(R/'nine-current-lightweight-jones-probe/src/DiophantineConsistency/ModelJonesNine.lean').read_text();new=(P/'NineFreshJones.lean').read_text();assert old.replace('DiophantineConsistency.ModelJonesNine','DiophantineConsistency.NineFreshJones')+'\n#print axioms DiophantineConsistency.NineFreshJones.jonesModel\n'==new
assert r['dependencies']['DiophantineConsistency.NineLightQuartic']['sha256']=='7ac8b9f968ac00677c81d17adb373127631f1bc4614b2abcd57407e181c2af04'

print(json.dumps({'status':'PASS','session':SESSION,'module':MOD,'guard_slots':GUARDS,'overlay_links':LINKS,'axiom_reports':REPORTS,'scope':SCOPE},indent=2))
