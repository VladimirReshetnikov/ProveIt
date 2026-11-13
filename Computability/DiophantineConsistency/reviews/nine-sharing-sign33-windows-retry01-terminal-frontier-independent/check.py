import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-sharing-sign33-windows-retry01';a=p/'attempt01';out=Path('/tmp/nine-sharing-sign33-windows-retry01-20261106');n='Sign33Windows';sha=lambda x:hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='9bba240fcea1e0efc75c9c8022016c61b68a0dfeabb05d66ea4b28786899faa1';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and len(s['rows'])==1
assert sha(p/'run.py')==s['runner_sha256']=='c5eb6c548eb4bf81205f1cab507835ae096852aa12bbe723dab3bf48c2c007af';assert sha(a/'outer-observation.json')=='f4837b98e06bb344508edecc4c1edacf7e3a0df660e8f73f3fd2236161786eaa';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==92352 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
r=s['rows'][0];assert r['module']==n and r['source_sha256']=='085fafe11fc49d341a2eeac64a4cc609133f5dd252d049477f6df9187d1ad70b' and r['object_sha256']=='0fa7c1c14d5b20316780f625ecedf85ea337876f805141dc4adb5db8a23f047b'
src=p/'src/DiophantineConsistency'/f'{n}.lean';assert sha(src)==sha(out/'src/DiophantineConsistency'/f'{n}.lean')==r['source_sha256'] and sha(out/'lib/DiophantineConsistency'/f'{n}.olean')==r['object_sha256'];t=src.read_text()
for x in ['(hbeta : 0<beta)','(hMC : MC<beta)','(hMF : MF<2*beta)','(hf : 0<f)','(hi : 0<i)','(hN : 0<N)','(heta : 0<eta)','(hzeta : 0<zeta)','(hy : 0<y)','(hgamma : 0<gamma)','htransport hfirst hmain hstrict haux','0<q-F-alpha ∧ R+2<E ∧ 2*R<c','maintained_first_indices beta K MC MF J F alpha z f i T s w N eta zeta y gamma']:assert x in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids'];assert sha(a/f'{n}-{phase}.txt')==sha(out/f'{n}-{phase}.txt')==z['log_sha256']
log=(a/f'{n}-compile.txt').read_text();assert sha(a/f'{n}-compile.txt')=='31b74e137a764085e6ef9d56a86c080876427745fae7aa80e329c01df1fd333d';assert log.count('warning:')==0 and 'error:' not in log and 'sorryAx' not in log and "'DiophantineConsistency.Sign33Windows.windows_from_maintained_norms' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log
cache={}
def check(path,h,rp):
 q=Path(path);assert q.is_file() and str(q.resolve())==rp
 if rp not in cache:cache[rp]=sha(q)
 assert cache[rp]==h
for k,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(k)
 else:check(k,v['sha256'],v['realpath'])
for k,v in s['overlay_links'].items():assert Path(k).is_symlink() and str(Path(k).resolve())==v
assert len(r['direct_guard'])==150 and len(s['overlay_links'])==1162
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')==sha(out/'survey-before.json')==sha(out/'survey-after.json')=='5e0a12ddb5419503ab2fc2418ee59db3d0185da0a11c2454870c3f17b34fc5f7';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY'
for name in ('ArithmeticPellFirstIndex','ModelDifferenceRing'):
 k='DiophantineConsistency.'+name;dep=r['dependencies'][k];sel=survey['selected'][k];check(dep['path'],sel['sha256'],sel['realpath']);assert dep['sha256']==sel['sha256'] and dep['realpath']==sel['realpath'] and r['direct_guard'][dep['path']]==sel
v=subprocess.run([sys.executable,'-I','-S','-B',str(p/'provider_survey.py')],capture_output=True,timeout=60);assert v.returncode==0 and not v.stderr and hashlib.sha256(v.stdout).hexdigest()=='5e0a12ddb5419503ab2fc2418ee59db3d0185da0a11c2454870c3f17b34fc5f7'
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','object_sha256':r['object_sha256'],'author_session':92352,'author_exit':0,'axioms':['propext','Classical.choice','Quot.sound'],'lint_warnings':0,'guard_slots':150,'overlay_links':1162,'scope':'Conditional scalar/first-index windows only; no sign33 zero bridge or endpoint, no Lean replay.'},indent=2,sort_keys=True))
