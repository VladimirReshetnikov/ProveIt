import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-reference-fields-combine-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-reference-fields-combine-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert sha(a/'state.json')==sha(out/'state.json')=='7bd683c7d990981e7b1172c16c73c294a4da4f88382949da0d88158c5c580fbc';s=json.loads((a/'state.json').read_text());assert s['status']=='FAILED' and s['failure']=="RuntimeError('compile failed Norm38StaticCarrierConditional')" and s['base_state_sha256']=='601a5b75826f06da85743490792dc8816d2c56f8b0a33de669544732c86015e2'
assert sha(q/'run.py')==s['runner_sha256']=='b6b077ec97b366014b7740e250fa5caeed49cb713cce67961f50350c9a694830' and sha(q/'source-manifest.json')=='6884049f228492c7e63bf26c22295249e595fb7ee719748e6cad38e13ba9d6bc' and sha(q/'field_preflight.py')=='4874dede3ed41c8502933a6b2b9a4303557ea203ef13a58a52f18888235e32f4'
assert sha(a/'outer-terminal-author-record.json')=='3a4b54cc8029e6153f40fa66ba0e70c685be9d8d19b1dcf243311310af7e8697';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==27499 and o['outer_exit_code']==1 and 'not independently observed' in o['observation_kind']
rows=s['rows'];assert [r['module'] for r in rows]==['Norm38ReferenceFieldsAll','Norm38StaticCarrierConditional'];m=json.loads((q/'source-manifest.json').read_text())['rows'];assert len(m)==2
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
for i,r in enumerate(rows):
 n=r['module'];assert r['source_sha256']==m[i]['source_sha256'];check(q/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256'])
 for phase in ('deps','compile'):
  z=r[phase];assert z['exit']==(1 if i==1 and phase=='compile' else 0) and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
  for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
 for path,v in r['direct_guard'].items():
  if v is None:assert not os.path.lexists(path)
  else:check(path,v['sha256'],v['realpath'])
 for mod,v in r['dependencies'].items():check(v['path'],v['sha256'],v['realpath'])
 if i==0:assert r['object_sha256']=='3f7e3aea0ca0fa2c9700d128fd6d3a563a2345a0d61b81bcd0d87478c98b2dfd';check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256'])
 else:assert 'object_sha256' not in r and not (out/'lib/DiophantineConsistency'/f'{n}.olean').exists()
good=(a/'Norm38ReferenceFieldsAll-compile.txt').read_text();assert "reference_terminal_fields_combined' depends on axioms: [propext, Quot.sound]" in good and 'warning:' not in good
bad=(a/'Norm38StaticCarrierConditional-compile.txt').read_text();assert 'error: Tactic `rewrite` failed: Did not find an occurrence of the pattern' in bad and 'sorryAx' in bad
assert rows[1]['dependencies']['DiophantineConsistency.Norm38ReferenceFieldsAll']['sha256']==rows[0]['object_sha256']
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
x=subprocess.run([sys.executable,'-I','-S','-B',str(q/'field_preflight.py')],capture_output=True,text=True,timeout=90);z=json.loads(x.stdout);assert x.returncode==0 and not x.stderr and z['producer_count']==5 and z['recorded_direct_guard_slots']==750
for name in ('nine-sharing-norm38-reference-fields01-terminal-independent','nine-sharing-norm38-reference-w-delta-terminal-independent','nine-sharing-norm38-reference-u-factored-terminal-independent','nine-sharing-norm38-reference-z-factored-terminal-independent'):
 p=D/'reviews'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),(name,x.stderr)
print(json.dumps({'status':'PASS_PARTIAL_FAILURE_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'author_recorded_session':27499,'author_recorded_exit':1,'successful_object_sha256':rows[0]['object_sha256'],'guard_slots':sum(len(r['direct_guard']) for r in rows),'overlay_links':len(s['overlay_links']),'scope':'Six-field conjunction checked; conditional carrier failure contains sorryAx and is not proof evidence; no Lean replay.'},indent=2,sort_keys=True))
