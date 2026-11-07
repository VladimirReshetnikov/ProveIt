#!/usr/bin/env python3
import hashlib,json,shutil,subprocess,sys,tempfile
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign25-zero-assembly-check';Q=D/'research/nine-sharing-sign25-zero-assembly-draft';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'5fc0b256fec537ac0524c46d253d54fa120bf15b464516fa28c744e7325fa47b','source-manifest.json':'c47f47c43cf3cbe6214df2b485f8b93e9d7286154742374ebe1dee598232807f','first-cut-survey.py':'7b604547d6df49e8d3349c086541204318afe5bcc3eafa8c7b5aee52a5ab7687'}.items():assert H(P/n)==h
assert H(Q/'generate.py')=='2043c5e4af8bd7a66304a2b9660fc623779f28103279582a212f8d261a96c1ed';m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign25CoordinateRecover','Sign25CoordinateDrop','Sign25ForwardBridge','Sign25ReverseBridge'];pins=['32100b3564db789bf174c4d87f04030aa960b9d580be54bc857012e4ac0d9a99','bd81cbd03bc7d9291e5ce941192129852ab1564de4bcf5487a747b909aeffe65','6c3b8e2143e6f7e25307a73cad8f69d066fac521c0982487fbd4917f22b5835a','db72a194a2c951a85ee19e4af212e38a06b61d6740c16f195191ada2c6fc5545'];assert len(m)==4
for e,n,h in zip(m,names,pins):assert e['module']=='DiophantineConsistency.'+n and e['source_sha256']==h==H(P/'src/DiophantineConsistency'/f'{n}.lean')==H(D.parents[1]/e['source'])
f=(P/'src/DiophantineConsistency/Sign25ForwardBridge.lean').read_text();b=(P/'src/DiophantineConsistency/Sign25ReverseBridge.lean').read_text();assert all(x in f for x in ['SharingSign25Squares.seed_zero_iff_residuals','SharingSign26Squares.seed_zero_iff_residuals','Sign25FirstCut.old_ell_zero p v','Sign25RemainingCuts.first_eval p v']);assert all(x in b for x in ['Sign25CoordinateRecover.lift_drop p v hz','SharingSign26Squares.seed_zero_iff_residuals','SharingSign25Squares.seed_zero_iff_residuals','Sign25RemainingCuts.first_eval p (Sign25CoordinateRecover.drop v)'])
indices=[1,2,3,5,6,7,8,10,11,12,13,14,15,16]
for i in indices:
 assert f'Sign25RemainingCuts.R{i:02d}_eval p v' in f and f'Sign25RemainingCuts.new_R{i:02d}_row p' in f
 assert f'Sign25RemainingCuts.R{i:02d}_eval p (Sign25CoordinateRecover.drop v)' in b and f'Sign25RemainingCuts.old_R{i:02d}_row p' in b
assert all(x in f for x in ['Sign25FirstCut.N0_eval p v','Sign25FirstCut.new_N0_row p']) and all(x in b for x in ['Sign25FirstCut.N0_eval p (Sign25CoordinateRecover.drop v)','Sign25FirstCut.old_N0_row p'])
assert f.count('  · exact ')==17 and b.count('  · exact ')==16 and '.mpr (hn' in f and '.mp (ho' in b
with tempfile.TemporaryDirectory(prefix='sign25-assembly-review-',dir=D/'research') as t:
 t=Path(t);shutil.copyfile(Q/'generate.py',t/'generate.py');subprocess.run([sys.executable,'-I','-S','-B',str(t/'generate.py')],capture_output=True,text=True,check=True,timeout=120)
 for n in names[2:]:assert (t/f'{n}.lean').read_bytes()==(Q/f'{n}.lean').read_bytes()
up=D/'reviews/nine-sharing-sign25-coordinate-recovery-terminal-frontier-independent/check.py';assert H(up)=='ff1636e4feedd55150154b198d60dbca072a1e3ab6994788069d789b818d783b';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=180);assert json.loads(r.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_PRELAUNCH','scope':'pointwise sign25 to sign26 product lift and reverse drop under IΣ₁; no existential endpoint','old_rows':17,'new_rows':16},sort_keys=True,indent=2))
