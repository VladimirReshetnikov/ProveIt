import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-gap-tau-ring-retry02';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-gap-tau-ring-retry02-20261106');n='Sign33GapTauRing';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='2293a07d5a524c81ef739382ed92bda7e1e553bf7af9e9b2f031069e8a389299';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='d9a39e77991b12ae4bd09b20e79efbcd42ddc74f6e0ce53ec1ba11866d1d17ae';assert sha(a/'outer-observation.json')=='7214c9b329594f9fe7a4e521f01be18624b23f81aafd6960ee97bba4928650fa';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==88451 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='7076c3cf798e53a22061a097e932114b585143acd4c123c1947a28480952539f' and r['object_sha256']=='3e7fd736fbb3f2ded242eae53e34df62c87709f755752724c6afd028546606bb'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['(hq : 1 ≤ q) (hN : 1 ≤ N)','(hgap : 0 < q-F-alpha) (hr : r+2 < E)','0 ≤ (ι q-1)*(ι q-ι F)+ι alpha ∧ 0 ≤ ι E*ι N+ι k-ι r']:assert x in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='bf510dfe6402014ed9363f2206280e09b4de9fc899a90e8600309a7ed75aa8b4';assert log.count('warning:')==0 and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33GapTauRing.gap_tau_of_windows' depends on axioms: [propext, Classical.choice, Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1164
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')==sha(out/'survey-before.json')==sha(out/'survey-after.json')=='8b46dad21aba666f06f77fbb5ed8f268b4baacfcf477baa29474e1dd4e5f901d';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
for k in ('DiophantineConsistency.Sign33Windows','Sign33OrderedRing'):
 dep=r['dependencies'][k];sel=survey['selected'][k];check(dep['path'],sel['sha256'],sel['realpath']);assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],capture_output=True,timeout=60);assert v.returncode==0 and not v.stderr and hashlib.sha256(v.stdout).hexdigest()=='8b46dad21aba666f06f77fbb5ed8f268b4baacfcf477baa29474e1dd4e5f901d'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':88451,'author_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'lint_warnings':0,'guard_slots':150,'overlay_links':1164,'scope':'Conditional window-to-ring signs only; no sign33 zero bridge or endpoint, no Lean replay.'},indent=2,sort_keys=True))
