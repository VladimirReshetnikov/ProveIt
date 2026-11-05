#!/usr/bin/env python3
import pathlib,json,hashlib,os,re
D=pathlib.Path(__file__).resolve().parents[2];R=D/'research';T=R/'current2011-four-port-byte-tuple';A=T/'attempt04'
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
d=json.loads((A/'result.json').read_text());o=json.loads((A/'outer-observation.json').read_text());s=(T/'CurrentFourPortBytes.lean').read_text();log=(A/'compile.log').read_text()
assert sha(T/'CurrentFourPortBytes.lean')=='7a36ac70fd6569cecdf79b891535df8f995a18048e7e036e9d2465040676e5f5'
assert sha(A/'source.lean')==sha(T/'CurrentFourPortBytes.lean')
assert sha(A/'result.json')=='606ca5d1e2f13c47921bf472c04ee166273241ff3161bfa42e912c0ba8428691'
assert sha(T/'check04.py')==d['runner_sha256']=='a71762c145af24460b43658baabf76929aa8d81769b18c7b541913df87f0e9d6'
assert (d['status'],d['exit'],o['session_id'],o['observed_outer_exit'],d['stop_reason'])==('PASS',0,69659,0,None)
assert sha(A/'compile.log')==d['log_sha256'] and log.count('depends on axioms:')==2
for report in re.findall(r'depends on axioms: \[([^\]]+)\]',log):assert [x.strip() for x in report.split(',')]==['propext','Classical.choice','Quot.sound']
obj=pathlib.Path(d['command'][d['command'].index('-o')+1]);assert sha(obj)==d['object_sha256']=='9b94acd4e35406559c61c51c0822798ec56737109415a517de9f973c409daa9f'
assert d['guards_stable'] and d['guards_before']==d['guards_after'] and len(d['guards_after'])==874
for key,v in d['guards_after'].items():
 p=pathlib.Path(v.get('path',key.rsplit(':',1)[-1]) if v else key.rsplit(':',1)[-1])
 if v is None:assert not os.path.lexists(p),p
 else:assert p.is_file() and str(p.resolve())==v['realpath'] and sha(p)==v['sha256'],p
for module,h in {'FourByteGeneric.olean':'a56873fdf83e80abd3c5233b6fff93919af0e28d116fe86acd092143d61411eb','BetaKernelPair.olean':'a18e7afc1c8a74124f653d06abeab866b3a80df8c66cb29a3a3bb77d51bbe35a','MaskPair.olean':'f863499874eb6583f2d613429651df373f8b61c2bfe6a3fda4917656d1fc1e2d'}.items():assert any(k.endswith('/'+module) and v and v['sha256']==h for k,v in d['guards_after'].items()),module
args='CurrentBetaBytes.bigBytes ((Nat.digits 256 (CurrentKernelBytes.recipe (2 ^ 47))).reverse)\n    CurrentMCBytes.bigBytes ((Nat.digits 256 (Nat.ofDigits CurrentMFRecipe.rho CurrentMFRecipe.maskDigits + (CurrentMFRecipe.rho ^ 2011 - 1))).reverse)'
assert s.count(args)==3
for fragment in ['theorem decoded_apply (j : Fin 4)', '((Nat.ofDigits 256 ((bigBytes j).reverse) : ℕ) : ℤ)', 'theorem decoded_eq_ports : decoded = CurrentWindowCarry2011.ports','FourByteGeneric.assemble','BetaKernelPair.decode_pair.1 BetaKernelPair.decode_pair.2','MaskPair.decode_pair.1 MaskPair.decode_pair.2']:assert fragment in s
print(json.dumps({'status':'PASS','outer_session':69659,'outer_exit':0,'lean_exit':0,'guard_slots':874,'object_sha256':d['object_sha256'],'scope':'Symbolic list tuple theorem and guarded providers; external file comparisons remain outside Lean.'},indent=2))
