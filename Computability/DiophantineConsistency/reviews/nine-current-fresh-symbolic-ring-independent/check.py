#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
PKT='nine-current-fresh-symbolic-ring'
TMP='/tmp/nine-fresh-symbolic-ring-20261105'
STATE='84b7035ec3620d1144d5f868b374b3210577ac078bb6cf0b16713c2dc445eeca'
SESSION=29836
BASE='c48776fcd9993d73cead1321f41a97621967a48b66c8d18d59aa879f6b8f0888'
RUNNER='58edb9224dc90dc7e74e7b6ca0e4e6d5cc3586a8f525cd00e455d8615af09785'
MOD='NineFreshCurrentRing'
SOURCE='3d0cb446bd9c2a4c94069a29d1a3acfd5217a05197be5c55099462e4a582028c'
OBJ='193758cb9ba6a1fc4d0cf3ca4b68392233cfe0118e01a32e20b9cbcab52dca56'
GUARDS=100
LINKS=1056
REPORTS=['DiophantineConsistency.NineFreshCurrentRing.eval_current']
SCOPE='Generic commutative-ring evaluator; natural zero endpoint separately; no literal graph or degree.'
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
assert r['dependencies']['DiophantineConsistency.IPRANineFreshCurrent']['sha256']=='3665f5e9392cc56149d1a8c3f54cc10d18dc8c3c4df828c073e8f0fd2bd459b3'
old=(R/'nine-current-symbolic-ring-generic/NineCurrentRing.lean').read_text();new=(P/'NineFreshCurrentRing.lean').read_text();assert old.replace('IPRANineCurrent','IPRANineFreshCurrent').replace('NineCurrentRing','NineFreshCurrentRing')==new
old=(R/'nine-current-symbolic-ring-generic/EQUATION.md').read_text();new=(P/'EQUATION.md').read_text();assert old.replace('NineCurrentRing.eval_current','NineFreshCurrentRing.eval_current')==new

print(json.dumps({'status':'PASS','session':SESSION,'module':MOD,'guard_slots':GUARDS,'overlay_links':LINKS,'axiom_reports':REPORTS,'scope':SCOPE},indent=2))
