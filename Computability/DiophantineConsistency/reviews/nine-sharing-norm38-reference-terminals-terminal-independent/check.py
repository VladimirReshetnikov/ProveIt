import hashlib,json,os,re,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-reference-terminals-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-reference-terminals-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38ReferenceTerminals'
assert sha(a/'state.json')==sha(out/'state.json')=='f0a9160c385c1f7163c46e8ebfd967a380e122b56190b2a92ec9d13c248454e8';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='ca49ec6fa785a5ad3eff917d313e83db38464cff16209a646115a8e19cc89d55'
assert sha(q/'run.py')==s['runner_sha256']=='4c6e749ffb18fa550da534a39899a7aed5058eb78a7b2ee24391f8f285d80894' and sha(q/'source-manifest.json')=='c7556a684459c4c9d6f4b5efe417f7adca7764352936f93c5a0f82b6722999cd' and sha(q/'producers_preflight.py')=='89b31955062349913e21ae57a1a0c2113e8ee1da9ba5530b4ca1a23f799a70d2'
assert sha(a/'outer-terminal-author-record.json')=='8fac8a30e97623ee15bf88eeb55e875834f3186503552385b2257453af6e0afd';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==55855 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='a7054b0ba3426cc055226eecfae6b9777cc6e09fa81b17b9989e211e43d72dd2' and r['object_sha256']=='66a0624ab8ec394bffc1f65a905d3362f45ae4201a31b7997d4f2baab390f957'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
assert '(hg : NormAssignment38.gatesHold ι ports w)' in t and '[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in t and [int(i) for i in re.findall(r'pairValue ι \(v (\d+)\)=ref \d+',t)]==[61,44,78,66,80,36]
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert "static_terminals_agree' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'Norm38ReferenceInitialAll':'be80de6feaa282e9b1fa15a265474cecd4f1b20e50d846d78faa049fcbd0a100','Norm38ReferenceGatesAll':'a2ed1f5582804d525fab3ec9bd5fa3346fcfad3036fcdedce8e4654ed4dce7dd'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath']);assert r['direct_guard'][dep['path']]['sha256']==h and r['direct_guard'][dep['path']]['realpath']==dep['realpath']
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'producers_preflight.py')],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_REFERENCE_PRODUCER_SURVEY' and (z['initial_rows'],z['gate_rows'],z['guard_slots'])==(8,13,2950)
for name in ('nine-sharing-norm38-reference-initial-split-terminal-independent','nine-sharing-norm38-reference-gates-batched-terminal-independent'):
 p=D/'reviews'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),(name,x.stderr)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':55855,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'Under gatesHold, six static/reference terminals agree; no seed/source or iPRA endpoint; no Lean replay. Initial provider outer numeric exit uncaptured.'},indent=2,sort_keys=True))
