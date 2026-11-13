import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-fixed-port-norms';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-fixed-port-norms-20261106');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38FixedPortNorms'
assert sha(a/'state.json')==sha(out/'state.json')=='fa850b4ce480ff0f43c38bbaeca4643a90641f7246aa4d3380070c6fc2fc64a8';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='f0a9160c385c1f7163c46e8ebfd967a380e122b56190b2a92ec9d13c248454e8'
assert sha(q/'run.py')==s['runner_sha256']=='d4d5cdb92f44d0280578f68cf2cfec0c170ce1358696a2ab427b7161fae28318' and sha(q/'source-manifest.json')=='4adacee58d8c9f828ad59b8b0a31494e9f7f2d5927a1f6906438315287fbf8ff' and sha(q/'provider_survey.py')=='631812fa3f28d07fafa704f43e152f9b78dd3b1faa6eb8cd0baddc0faa08b783'
assert sha(a/'outer-observation.json')=='f4ef17097617cafc814d7b5de60006e1841dbcb42e5fb016130966a510a7cec5';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==60114 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='e77a7e6792c89c6c25e0d187361c295ff5565427afa719b286dc30e52dc1f050' and r['object_sha256']=='2cfd83ff77fbe9ffe28d9f37b61c2f3c374b59d9aefdce9c28dad55cad11bd7c'
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')=='f69de9b5a9dcc2d6bf93d5ac8e4e6a06353d5645ba8f86c5aeda71a6084697a8';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY' and len(survey['links'])==1138 and len(survey['selected'])==8
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
assert '((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V)' in t and '(hx : ∀ j, (0 : DiffRing V) < x j)' in t and '(hz65 : Carrier65.value ringPorts x = 0)' in t and 'd.P=1 ∧ d.Q=1 ∧ d.U=1 ∧ Carrier65.strong d=1 ∧ d.W=1' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert "carrier_zero_unitNorms' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
mod='FreshCarrierSpheres';dep=r['dependencies'][mod];expected=survey['selected'][mod];assert dep['sha256']==expected['sha256'] and dep['realpath']==expected['realpath'];check(dep['path'],dep['sha256'],dep['realpath']);assert r['direct_guard'][dep['path']]['sha256']==dep['sha256'] and r['direct_guard'][dep['path']]['realpath']==dep['realpath']
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_survey.py')],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_POINT_PRODUCER_SURVEY' and z['selected']==survey['selected'] and z['links']==survey['links']
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':60114,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Fixed-current carrier-zero to five norms for positive ring inputs only; no reverse bridge or endpoint; no Lean replay.'},indent=2,sort_keys=True))
