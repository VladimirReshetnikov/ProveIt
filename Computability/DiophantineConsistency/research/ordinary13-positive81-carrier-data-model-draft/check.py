from pathlib import Path
from hashlib import sha256
from math import isqrt
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
PINS = {'research/ordinary13-residue-first81/candidate.json': '067d3cf0e92961d272e9018dde38bbe8b00ad55ec8e9145fbdd34c0f13e18352', 'research/ordinary13-qcube-main83/candidate.json': 'd19de596305c838c4b58f011a7fd233fedc4f7a7a87923cca60d00f46b408789', 'research/ordinary13-positive81-to83-model-draft/Positive81To83Transport.lean.src': 'a01d62a2d5572c712c37bb8a4a933bea26f494b143f104bcbe484a58523f7ae0', 'research/ordinary13-positive81-to83-model-draft/CarrierWitnessFacts.lean.src': '1548caa5343dc34f63d64b15764803cf362bff781ddac5393fc8d142ac23f4cc', 'research/ordinary13-residue-root-switch-extraction-draft/ResidueRootSwitchExtract.lean.src': '01d086c7d25b266f2385d9084f24ee8b9fc15e605eee97503a9b7329396e78f3', 'research/ordinary13-positive81-calibration-model-draft/Positive81Calibration.lean.src': 'fe9386694b4ea07e10ea94b6cd8c3810cb70d394e0bfedd985d358183a753086', 'research/ordinary13-positive81-exact-main-model-draft/Positive81ExactMain.lean.src': 'f9a294400eaa1dab6f339f2d746f8ef89e69146f82057baba899513db6cb9686', 'research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src': '6b38dc7c935520220392e6d1b89e36655ef175bbaec9a4d60501adce8a93f863', 'research/ordinary13-positive81-carrier-data-model-draft/CompanionCarrierFacts.lean.src': '33ded2d0df481e3a50a239944a01d4fcd06ef415d04148d80a065c70e76850e7', 'research/ordinary13-positive81-carrier-data-model-draft/Positive81ForwardCarrier.lean.src': '90d3e64d9305af5fe2077d9851e2c9ee2678c51bdc287e1d8014512438a2b994', 'research/ordinary13-positive81-carrier-data-model-draft/Positive81ForwardCompact.lean.src': '75aa8a05b694dfae05ce2b25128b92a80fd3d8bf6b031b55d1d6cd047e800eb1', 'research/ordinary13-positive81-carrier-data-model-draft/PositiveCarrierData.lean.src': 'd223f34c2bd1f493bff5a8925971d8d5a5a3d8b0142377248e9cac4000ea9182'}
for name,digest in PINS.items():
 assert sha256(Path(name).read_bytes()).hexdigest()==digest,name
a,b=(json.loads(Path(p).read_text()) for p in list(PINS)[:2])
assert (len(a["source"]),len(b["source"]))==(81,83)
assert a['witnesses']==b['witnesses']==['J','F','alpha','f','i','T','w','s','r','eta','zeta','y','gamma']
ra,rb=({row[0]:row for row in g['source']} for g in (a,b))
assert ra['g26']==['g26','+','X','K0'] and rb['g26']==['g26','+','X','g25']
assert ra['Bt']==['Bt','-','g27','F'] and rb['Bt']==['Bt','-','g27','g28']
assert rb['g25']==['g25','*','K0','q'] and rb['g28']==['g28','*','F','q']
assert all(ra[n]==rb[n] for n in ra.keys() & rb.keys() if n not in ('g26','Bt'))
assert all(ra[n]==row for n,row in {'qm':['qm','*','J','beta'],'q':['q','+',1,'qm'],'X':['X','*','q','w'],'q3':['q3','*','q','q2'],'Y':['Y','*','q3','s'],'ell':['ell','*','E','kY'],'folded_g31':['folded_g31','-','g31','folded_kBt'],'Z':['Z','-','g32','Bt'],'A0':['A0','-','g38','g42']}.items())
forward=reverse=0
for q in range(2,14):
 b=q-1
 for F in range(1,q):
  for A in range(1,q-F):
   C=q-F-A
   for K in range(5):
    for X in range(1,q*q+4):
     old=C*(X+K)-F; new=C*(X+K*q)-F*q; D=C*K-F
     assert new-old==b*D
     if old%b==0: assert new%b==0
     if new>0: assert old>0; reverse+=1
     if X>=q*q:
      assert F+2<=q and new>0; forward+=1
roots=0
for ell in range(12):
 for k in range(2,18):
  tau=isqrt(1+ell*(ell+k))
  if tau*tau!=1+ell*(ell+k): continue
  assert tau>ell
  for b in range(1,8):
   for t in range(1,8):
    P=b*t; r=k*(P-1)+t+(tau-ell)
    assert r>0 and b*(ell+k+r-k*P)-P==b*tau
    roots+=1
assert min(forward,reverse,roots)>0
print(json.dumps({'sha256':PINS,'graph_first_carrier_rows_checked':True,'finite_companion_cases':{'forward':forward,'reverse':reverse},'finite_positive_branch_cases':roots,'lean_executed':False,'status':'Bounded source and arithmetic checks only; no model proof, provider validation or CrossRootCut.'},sort_keys=True,indent=2))
