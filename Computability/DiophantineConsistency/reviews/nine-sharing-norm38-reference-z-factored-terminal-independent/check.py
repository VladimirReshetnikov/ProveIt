import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-reference-z-factored-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-reference-z-factored-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38ReferenceZFactored'
assert sha(a/'state.json')==sha(out/'state.json')=='601a5b75826f06da85743490792dc8816d2c56f8b0a33de669544732c86015e2';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='4fba8a5d941e00d22e0a43f3ef34a83fb3e69ac59755f6a7602989d30c5630f8'
assert sha(q/'run.py')==s['runner_sha256']=='def9d5aeb1ee26f7538d1e55f6288743bf4bc6819fca27b321f896bdb86d2df7' and sha(q/'source-manifest.json')=='eb10eff8833eb35419865be9f393ff64ec5ecf6299f3e63f604e62e84af60d51' and sha(q/'carrier_preflight.py')=='5ab96370130b8040275c908d8e16319b641dc91ef5267e4d74965d44db61c02c'
assert sha(a/'outer-terminal-author-record.json')=='b971284d6efea9c7a69a66c5046b11f7f1195337589beef7f747f5c01fa32d39';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==19917 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='bf62c03f3295e75f5787fb01718848fcf8ed8afe591c989b2394b50f2bb33bf0' and r['object_sha256']=='a64a0e35d5903db00af87f502a074f8ecb669c9a784bd1464a110e59fc20c89c'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256'])
t=src.read_text();assert '[CommRing R]' in t and 'reference p x 80 = (Carrier65.core p x).Z' in t and 'reference_delta p x' in t and 'reference_S_node p x' in t
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert "'DiophantineConsistency.Norm38Reference.reference_Z_factored' depends on axioms: [propext]" in log and 'warning:' not in log and 'error:' not in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'Norm38ReferenceUFactored':'a0525e2c12c72839474fdfc5562cb3bf723218768616efd7808154866075e42f','Norm38ReferenceDelta':'d43d2cbdd4e19edad31de95b48e51ba1459a4cdc61a286e742d8279e01292a65'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath'])
for name in ('nine-sharing-norm38-reference-u-factored-terminal-independent','nine-sharing-norm38-reference-w-delta-terminal-independent'):
 p=D/'reviews'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),(name,x.stderr)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':19917,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':['propext'],'warnings':0,'scope':'No Lean replay; generic Z field identity only, not final bridge or endpoint.'},indent=2,sort_keys=True))
