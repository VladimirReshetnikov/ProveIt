import hashlib,json,os,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
P=Path(__file__).resolve().parent;D=P.parents[1];R=D/'research';q=R/'nine-sharing-norm38-reference-u-factored-check';a=q/'attempt01';out=Path('/tmp/nine-sharing-norm38-reference-u-factored-check-20261105');sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();n='Norm38ReferenceUFactored'
assert sha(a/'state.json')==sha(out/'state.json')=='4fba8a5d941e00d22e0a43f3ef34a83fb3e69ac59755f6a7602989d30c5630f8';s=json.loads((a/'state.json').read_text());assert s['status']=='PASS' and s['base_state_sha256']=='dbe89b1dd4d849a60008700d2d0274b227658643a3d8441c2159e4ae7e843290'
assert sha(q/'run.py')==s['runner_sha256']=='22d5abc10cbe50dc553cd1fb62dabd8ca93ebb4b68cef9e33be827d8b3fd314d' and sha(q/'source-manifest.json')=='64687f68f2f8668abcf8301d147687af8882d41c1b94aa24e38a474b501ab1e2' and sha(q/'carrier_preflight.py')=='eb0cf0232078a348f9bb5261fe3336fb9b20267cda932b283b8d6269369242eb'
assert sha(a/'outer-terminal-author-record.json')=='69c88456c473b1557b741c16129889a5ed432e832ba719a96de3fefb0d2667ed';o=json.loads((a/'outer-terminal-author-record.json').read_text());assert o['outer_session_id']==58239 and o['outer_exit_code']==0 and 'not independently observed' in o['observation_kind']
assert len(s['rows'])==1;r=s['rows'][0];assert r['module']==n and r['source_sha256']=='0d2bed3c95158470085ba30e3680376729925b0f799c88503e0a3c2bb193ca15' and r['object_sha256']=='a0525e2c12c72839474fdfc5562cb3bf723218768616efd7808154866075e42f'
cache={}
def check(path,h,real=None):
 p=Path(path);assert p.is_file()
 if real is not None:assert str(p.resolve())==real
 k=str(p.resolve())
 if k not in cache:cache[k]=sha(p)
 assert cache[k]==h
src=q/'src/DiophantineConsistency'/f'{n}.lean';check(src,r['source_sha256']);check(out/'src/DiophantineConsistency'/f'{n}.lean',r['source_sha256']);check(out/'lib/DiophantineConsistency'/f'{n}.olean',r['object_sha256'])
t=src.read_text();assert 'reference p x 71 = (Carrier65.core p x).V' in t and 'reference p x 72 = (Carrier65.core p x).S' in t and 'reference p x 78 = (Carrier65.core p x).U' in t and t.count('[CommRing R]')==3
for phase in ('deps','compile'):
 z=r[phase];assert z['exit']==0 and z['stop_reason'] is None and not z['monitor_errors'] and not z['observed_descendant_pids']
 for p in (a,out):check(p/f'{n}-{phase}.txt',z['log_sha256'])
log=(a/f'{n}-compile.txt').read_text();assert log.count('warning:')==2
for thm,axioms in [('reference_V_node','propext, Quot.sound'),('reference_S_node','propext'),('reference_U_factored','propext, Quot.sound')]:assert f"'{ 'DiophantineConsistency.Norm38Reference.'+thm }' depends on axioms: [{axioms}]" in log
for path,v in r['direct_guard'].items():
 if v is None:assert not os.path.lexists(path)
 else:check(path,v['sha256'],v['realpath'])
for path,v in s['overlay_links'].items():assert Path(path).is_symlink() and str(Path(path).resolve())==v
for mod,h in {'Carrier65':'10608a9a444a1e47d62c9093332d63e58f6f7a2b0bc7090f24504ba939c3c42f','Norm38ReferenceUEdges':'7cb827b6b2ef7d5fb503106f7861daa2c8553a00823c798c18f63d2236421fdd'}.items():
 dep=r['dependencies']['DiophantineConsistency.'+mod];assert dep['sha256']==h;check(dep['path'],h,dep['realpath'])
for name in ('nine-sharing-norm38-reference-u-edges-terminal-independent','nine-sharing-norm38-reference-fields01-terminal-independent'):
 p=D/'reviews'/name;x=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,timeout=120);assert x.returncode==0 and not x.stderr and x.stdout==(p/'result.json').read_bytes(),(name,x.stderr)
print(json.dumps({'status':'PASS_TERMINAL_EVIDENCE_ONLY','state_sha256':sha(a/'state.json'),'object_sha256':r['object_sha256'],'author_recorded_session':58239,'author_recorded_exit':0,'guard_slots':len(r['direct_guard']),'overlay_links':len(s['overlay_links']),'axioms':{'V':['propext','Quot.sound'],'S':['propext'],'U':['propext','Quot.sound']},'warnings':2,'scope':'No Lean replay; generic field identities only, not final bridge or endpoint.'},indent=2,sort_keys=True))
