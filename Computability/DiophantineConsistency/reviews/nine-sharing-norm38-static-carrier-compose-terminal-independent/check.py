import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-static-carrier-compose-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-static-carrier-compose-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38StaticCarrierCompose'
assert sha(a/'state.json')==sha(out/'state.json')=='454aa2c28427b362766346a5281ceef88d8fc8aae173dc7098032426a8ca409d';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='f0a9160c385c1f7163c46e8ebfd967a380e122b56190b2a92ec9d13c248454e8'
assert sha(q/'run.py')==s['runner_sha256']=='4902ca4ff028d93d45b281d22bd783d3106aa4c2fa39031c3a629935749ff96c' and sha(q/'source-manifest.json')=='29160dba24f910c1160c000f0e02ba8497ceb19355516a8970ece937107f4a75' and sha(q/'producers_preflight.py')=='bd9bb79b11a2a91c998f851e3d955e15f592928958f5104a1cc06216758d409b'
assert sha(a/'outer-terminal-author-record.json')=='2b664a8b5c14100f5f6ebbf6830e749b615a9d5772e9cea428997ec1a6484dc4';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==56080 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='3a92fa7a64342374ffd1b31a5e14409363b0c6b81a1fd66a0e05bcae69d375cc' and r['object_sha256']=='7330cef6fb69cd41cab2e9febc17bb9b356a66b68cb16e88725e9a7897712aa1'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256']);t=src.read_text()
assert '(hg : NormAssignment38.gatesHold ι ports w)' in t and '(hn : NormAssignment38.fiveNorms ι ports w)' in t and 'Carrier65.value (fun j => ι (ports j))' in t and 'static_terminals_norms_imply_value ports w (static_terminals_agree ports w hg) hn' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert "static_gates_norms_imply_value' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]" in log and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'Norm38ReferenceTerminals':'66a0624ab8ec394bffc1f65a905d3362f45ae4201a31b7997d4f2baab390f957','Norm38StaticCarrierConditional':'7d0b8cbb7cd6a01447ff710deb1f22336c3765bc4e7b5149b9cc3424eef491f6'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath']);assert r['direct_guard'][dep['path']]['sha256']==h and r['direct_guard'][dep['path']]['realpath']==dep['realpath']
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'producers_preflight.py')],capture_output=True,text=True,timeout=120);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['status']=='PASS_STATIC_CARRIER_PRODUCER_SURVEY' and (z['producers'],z['direct_guard_slots'])==(8,1250)
for name in ('nine-sharing-norm38-reference-terminals-terminal-independent','nine-sharing-norm38-static-carrier-retry02-terminal-independent'):
 p=D/'reviews'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),(name,x.stderr)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':56080,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext','Classical.choice','Quot.sound'],'warnings':0,'scope':'From same-port/same-witness gatesHold and fiveNorms to shifted Carrier65 zero; no reverse or endpoint; no Lean replay.'},indent=2,sort_keys=True))
