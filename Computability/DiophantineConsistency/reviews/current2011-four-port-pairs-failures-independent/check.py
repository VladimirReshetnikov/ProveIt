#!/usr/bin/env python3
"""Independent receipt and source audit; no Lean invocation."""
import hashlib,json,os,pathlib
D=pathlib.Path(__file__).resolve().parents[2]
R=D/'research'; P=R/'current2011-four-port-byte-pairs'; T=R/'current2011-four-port-byte-tuple'
def sha(p): return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
expected=[(P/'BetaKernelPair-attempt03','PASS',0,29018,0,685),(P/'MaskPair-attempt01','PASS',0,62025,0,685),(R/'current2011-four-port-byte-generic/attempt01','PASS',0,38757,0,685),(T/'attempt01','FAILED',-6,2269,1,685),(T/'attempt02','FAILED',-6,76962,1,801)]
out=[]
for path,status,child,session,outer,n in expected:
 d=load(path/'result.json'); o=load(path/'outer-observation.json')
 assert (d['status'],d['exit'],o['session_id'],o['observed_outer_exit'])==(status,child,session,outer)
 assert d['guards_stable'] and d['guards_before']==d['guards_after'] and len(d['guards_after'])==n
 assert d['stop_reason'] is None and sha(path/'compile.log')==d['log_sha256']
 for key,value in d['guards_after'].items():
  p=pathlib.Path(value.get('path',key.rsplit(':',1)[-1]) if value else key.rsplit(':',1)[-1])
  if p==T/'CurrentFourPortBytes.lean' and status=='FAILED':
   assert sha(path/'source.lean')==value['sha256'];continue
  if value is None: assert not os.path.lexists(p),p
  else: assert p.is_file() and str(p.resolve())==value['realpath'] and sha(p)==value['sha256'],p
 log=(path/'compile.log').read_text()
 if status=='PASS':
  assert 'depends on axioms: [propext, Classical.choice, Quot.sound]' in log
  obj=pathlib.Path(d['command'][d['command'].index('-o')+1]);assert sha(obj)==d['object_sha256']
 else:
  assert 'lean::memory_exception' in log and 'excessive memory consumption' in log and d['object_sha256'] is None
 out.append(dict(attempt=str(path.relative_to(D)),child_exit=child,outer_session=session,outer_exit=outer,guard_slots=n,object_sha256=d['object_sha256'],receipt_sha256=sha(path/'result.json')))
for path,session,reason in [(P/'BetaKernelPair-attempt01',68100,'maximum recursion depth'),(P/'BetaKernelPair-attempt02',21137,'type mismatch')]:
 d=load(path/'result.json');o=load(path/'outer-observation.json');assert (d['status'],d['exit'],o['session_id'],o['observed_outer_exit'])==('FAILED',1,session,1)
 assert reason.lower() in (path/'compile.log').read_text().lower() and sha(path/'compile.log')==d['log_sha256']
for source,pin in [('BetaKernelPair.lean','80ca7c881b25f341ba84c06bd6f2a670a3719feba57fd44ef7056ad36425b02d'),('MaskPair.lean','770db4d3a08d9f072f4ae198e5ad89c1f3f64177ef0db8c0091de1e64ccde661')]: assert sha(P/source)==pin
b=(P/'BetaKernelPair.lean').read_text();m=(P/'MaskPair.lean').read_text();t=(T/'attempt02/source.lean').read_text()
for frag in ['Nat.coe_ofDigits ℤ 256 CurrentBetaBytes.bigBytes.reverse','CurrentBetaBytes.decode_beta','CurrentKernelBytes.recipe (2 ^ 47)','CurrentKernelBytes.decode_kernel','CurrentWindowCarry2011.ports 0','CurrentWindowCarry2011.ports 1']: assert frag in b,frag
for frag in ['CurrentMCBytes.bigBytes.reverse','CurrentMCBytes.decode_mc','CurrentMFRecipe.rho CurrentMFRecipe.maskDigits','CurrentMFRecipe.rho ^ 2011 - 1','CurrentMFDecoderExplicit.decode_mf','CurrentWindowCarry2011.ports 2','CurrentWindowCarry2011.ports 3']: assert frag in m,frag
assert m.count('CurrentMFRecipe.rho ^ 2011 - 1')==1
for mod in ['CurrentBetaBytes.olean','KernelRecipe.olean','CurrentMCBytes.olean','CurrentMFDecoderExplicit.olean']:
 assert any(k.endswith('/'+mod) and v is not None for k,v in load((P/'BetaKernelPair-attempt03')/'result.json')['guards_after'].items()),mod
for frag in ['BetaKernelPair.decode_pair','MaskPair.decode_pair','Nat.ofDigits 256']: assert frag in t,frag
assert sha(T/'attempt02/source.lean')=='ef57d7294bc796e2c1ce5cd406c3337be56f1e7f04e848186ea014ece5acadf7'
g=(R/'current2011-four-port-byte-generic/FourByteGeneric.lean').read_text()
assert sha(R/'current2011-four-port-byte-generic/FourByteGeneric.lean')=='07ad651c97ebc529cc83c4bcd119341e2e5ef4db7661995cee547e4a5cea7123'
for frag in ['![a,b,c,d]','Nat.ofDigits 256','theorem assemble','funext j','fin_cases j','exact h0','exact h1','exact h2','exact h3']: assert frag in g
print(json.dumps({'status':'PASS','checks':out,'scope':'Receipt and static source audit only; pair theorem proofs checked by recorded Lean runs; failed tuple attempts prove no tuple theorem; symbolic recipes only, external gzip bytes are separate.'},indent=2))
