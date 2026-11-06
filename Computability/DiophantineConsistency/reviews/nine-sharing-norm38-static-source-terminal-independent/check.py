import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-static-source-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-static-source-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38StaticSource'
assert sha(a/'state.json')==sha(out/'state.json')=='fcff412df865174d5bf4c2e553bc98b13c9bcc86a87821522426adab2625165b';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='454aa2c28427b362766346a5281ceef88d8fc8aae173dc7098032426a8ca409d'
assert sha(q/'run.py')==s['runner_sha256']=='7e02ddf3c7f6bdc974c5373917c8394b48c605143bdf850a56e980c6fe8c9a14' and sha(q/'source-manifest.json')=='049f7f7c34ed16502f134d95249e0a4f14951bd6e614d2c5a60a771b5aefc0e9' and sha(q/'provider_preflight.py')=='efca0d6b2361fcc50df9b26f160174a8f5e2518156eae83579b4a7efa57762b5'
assert sha(a/'outer-terminal-author-record.json')=='b70312fd249fb9454075df7a2a6147fb54a157f2370910bd2ce393d3f78b4c5a';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==92229 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='9472ebddd8fa9d56185a223fb010651321addf2b59fdfc28001d572052ee0362' and r['object_sha256']=='38875a54e297eb2d94aa897c49251177b4b2f904373f7593d153c2a5ebca0384'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
assert '∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)' in t and '(hg : NormAssignment38.gatesHold ι ports w)' in t and '(hn : NormAssignment38.fiveNorms ι ports w)' in t and 'InternalZero (ObjectCurrentEquation2011.expressionAt p)' in t and 'w (Fin.castLE (by decide : 14 ≤ 38) j) + 1' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert "static_implies_source_zero' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'DiophantineConsistency.Norm38StaticCarrierCompose':'7330cef6fb69cd41cab2e9febc17bb9b356a66b68cb16e88725e9a7897712aa1','FreshModel106':'d18cea14c5bf1a363aac4fbc76a9afa72623a4df185eba25070112c514deb942'}.items():
 dep=r['dependencies'][mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath']);assert r['direct_guard'][dep['path']]['sha256']==h and r['direct_guard'][dep['path']]['realpath']==dep['realpath']
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'provider_preflight.py')],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_POINT_IN_TIME_PROVIDER_SURVEY' and len(z['matched_direct_project_modules'])==6
p=D/'reviews/nine-sharing-norm38-static-carrier-compose-terminal-independent';x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),x.stderr
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':92229,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Static to shifted source zero under four generic cast hypotheses; no reverse or endpoint; no Lean replay.'},indent=2,sort_keys=True))
