import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-unit-norms-split';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-unit-norms-split-20261106');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38GenericUnitNorms'
assert sha(a/'state.json')==sha(out/'state.json')=='d86bb7430d4c23f93813a71e357e1555b89f95014b7996bedb34f8afd3b210b8';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38GenericUnitNorms')" and s['base_state_sha256']=='f0a9160c385c1f7163c46e8ebfd967a380e122b56190b2a92ec9d13c248454e8'
assert sha(q/'run.py')==s['runner_sha256']=='53573476066580de3a710b626d9acbcd9704207d389eb714b58bcf7acbe5c842' and sha(q/'source-manifest.json')=='6f15604e0d9f148b0a1c48031a94740ffd8f0b09e5163bbd9ee1af8ad902fc0e' and sha(q/'provider_survey.py')=='631812fa3f28d07fafa704f43e152f9b78dd3b1faa6eb8cd0baddc0faa08b783'
assert sha(a/'outer-observation.json')=='c76759c84b03cfa25a2a0948e5c028160ac0bfe3a118ac7d920c6f7dabc9cd0b';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==59916 and o['numeric_exit']==1 and 'not an independent transcript' in o['observation_source']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='edf5ababfee718c0d32fe24f0728f502865dcb2b60bee480f3ac286eff674e02' and 'object_sha256' not in r
assert sha(a/'survey-before.json')=='f69de9b5a9dcc2d6bf93d5ac8e4e6a06353d5645ba8f86c5aeda71a6084697a8';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY' and len(survey['links'])==1138 and len(survey['selected'])==8
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);assert not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==(0 if phase=='deps' else -15) and z['stop_reason']==(None if phase=='deps' else 'timeout') and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
assert (a/f'{n}-compile.txt').read_bytes()==b'' and r['compile']['timeout_seconds']==120 and not (a/'Norm38ShiftedUnitNorms-compile.txt').exists()
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
mod='FreshCarrierSpheres';dep=r['dependencies'][mod];expected=survey['selected'][mod];assert dep['sha256']==expected['sha256'] and dep['realpath']==expected['realpath'];check(dep['path'],dep['sha256'],dep['realpath']);assert r['direct_guard'][dep['path']]['sha256']==dep['sha256'] and r['direct_guard'][dep['path']]['realpath']==dep['realpath']
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_survey.py')],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_POINT_PRODUCER_SURVEY' and z['selected']==survey['selected'] and z['links']==survey['links']
print(json.dumps({'status':'PASS_TIMEOUT_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'author_recorded_session':59916,'author_recorded_exit':1,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'scope':'No Lean replay; first abstract norm theorem timed out with no object, second unrun.'},indent=2,sort_keys=True))
