import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-current-source-to-seed';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-current-source-to-seed-20261106');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38CurrentSourceToSeed'
assert sha(a/'state.json')==sha(out/'state.json')=='706bff9dd72de8b197bca5e69a7a0b91f6138dd7741bf419115865ac94612eb6';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='f0a9160c385c1f7163c46e8ebfd967a380e122b56190b2a92ec9d13c248454e8'
assert sha(q/'run.py')==s['runner_sha256']=='9b6003ee2524059e407720c669adcc4f59aeb9020f015827f3d59a90583804d2' and sha(q/'source-manifest.json')=='f97728420ca14ca5d4619c2e04dee521680b34ceae67c651ea5fb2e3d3018b8e' and sha(q/'provider_survey.py')=='24cf750620633d76b645d870927c83493a57094aea21ef09a6cec8ad4ef089aa'
assert sha(a/'outer-observation.json')=='eb9b818d01ca626ec52f85aae5e8b367f2a69762b824d621acf815fc5c546dc6';o=json.loads((a/'outer-observation.json').read_text());assert o['session_id']==51116 and o['numeric_exit']==0 and 'not an independent transcript' in o['observation_source']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='df0134bfd165dabd265c29257826da1575c50a5562b8dadfe423452ed74c6954' and r['object_sha256']=='8963b7bb31156f726981321e3541eb9b122046381e4457393f63d530c78bb6ca'
assert sha(a/'survey-before.json')==sha(a/'survey-after.json')=='77fc7b7a99f41090effb2015db8f58654dce03dc352c00389d9528d56466cd82';survey=json.loads((a/'survey-before.json').read_text());assert survey['status']=='PASS_POINT_PRODUCER_SURVEY' and len(survey['links'])==1140
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
assert '∀ j, ((CurrentWindowCarry2011.ports j : ℤ) : DiffRing V) = ι (ports j)' in t and 'InternalZero (ObjectCurrentEquation2011.expressionAt CurrentWindowCarry2011.ports)' in t and 'InternalZero (SharingSeed38.seed CurrentWindowCarry2011.ports)' in t and '(Fin.cons (1 : V) (SharingForward38.witnessCoordinates ports u))' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert "source_zero_implies_seed_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,dep in r['dependencies'].items():
 check(dep['path'],dep['sha256'],dep['realpath']);assert r['direct_guard'][dep['path']]['sha256']==dep['sha256'] and r['direct_guard'][dep['path']]['realpath']==dep['realpath']
 if mod!='Init':assert dep['sha256']==survey['selected'][mod]['sha256'] and dep['realpath']==survey['selected'][mod]['realpath']
assert len(r['dependencies'])==6 and survey['providers']['sourcepartial']['rows']==survey['providers']['forwardpartial']['rows']==1
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_survey.py')],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_POINT_PRODUCER_SURVEY' and z['selected']==survey['selected'] and z['links']==survey['links']
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':51116,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Fixed symbolic current source zero to generated seed zero under universal model port-cast hypothesis; no endpoint; no Lean replay.'},indent=2,sort_keys=True))
