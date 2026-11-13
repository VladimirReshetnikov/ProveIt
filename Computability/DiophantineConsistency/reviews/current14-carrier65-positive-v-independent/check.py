from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2];d=root/'research/current14-carrier65-positive-v';p=root/'research/carrier65-independent/PROOF.md'
pins={d/'README.md':'9af4bb4a9b9870ca8addf9d0fd8aab8e5c5654f277ede528b662d4558afa0d90',d/'check.py':'657b4741eca6412d225c2df971affb71fdefe0c37756078d9c4f52d0f0b6585e',d/'result.json':'0d35b9f61277ae84b9d732c0d4f462521c136e660bfbec6a1eac826b389a5b6d',p:'53ec75050c7f4a00386d9738f8c515f3a816d8e4d94afcebb54b3497d972e749'}
for x,h in pins.items():assert hashlib.sha256(x.read_bytes()).hexdigest()==h
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(d/'check.py')])==(d/'result.json').read_bytes()
graph=root/'candidates/one-page-padding-staircase-carrier65-2011/polynomial.json';assert hashlib.sha256(graph.read_bytes()).hexdigest()=='f1f7611842896806fa9e70ad102c6a0e7aa11747a650968f1c74cb169f0e253e';g=json.loads(graph.read_text());rs={r[0]:r[1:] for r in g['source']}
expected={'qm':['*','beta','J'],'q':['+','qm',1],'q2':['*','q','q'],'q3':['*','q2','q'],'X':['*','w','q'],'Y':['*','s','q3'],'E':['*','X','Y'],'k':['+','eta','zeta'],'kY':['*','k','Y'],'ell':['*','E','kY'],'c':['+','kY','eta'],'a':['+','E','Y'],'four_a':['*',4,'a'],'H':['+','four_a',3],'a2':['*','a','a'],'Delta':['+','a2','H'],'qF':['-','q','F'],'C':['-','qF','alpha'],'gap_product':['*','qm','qF'],'gap':['+','gap_product','alpha'],'q2minus1':['-','q2',1],'rproduct':['*','gap','q2minus1'],'qMF':['*','q','MF'],'maskfactor':['+','MC','qMF'],'mask':['*','maskfactor','J'],'R':['+','rproduct','mask'],'En':['*','E','n'],'tau_partial':['+','En','k'],'tau':['-','tau_partial','R'],'Nt':['-','transport_partial','zqm'],'f2':['*','f','f'],'cT':['*','c','T'],'cTminusR':['-','cT','R'],'f2inner':['*','f2','cTminusR'],'V':['-','f2inner','c']}
for n,row in expected.items():assert rs[n]==row,n
for beta in range(31,50):
 for J in range(1,5):
  q=beta*J+1
  for MC,MF in [(1,beta+1),(beta-1,2*beta-1)]:
   mask=(MC+q*MF)*J;assert 0<mask<(1+2*q)*(q-1)
   for u in (2,q-1):
    for alpha in (1,u-1):
     gap=(q-1)*u+alpha;rank=gap*(q*q-1)+mask
     assert 2*q-1<=gap<=q*q-q-1 and 1<rank<q**4-q**3<q**4
# Mod-four factor signs: squares and delta = (a+2)^2-1.
for a in range(4):
 delta=((a+2)**2-1)%4
 for x in range(4):
  for y in range(4):
   assert (x*x-delta*y*y)%4!=3
for S in range(4):
 for V in range(4):
  for y in range(4):assert (S*S*(V*V-y*y)+y*y)%4!=3
print(json.dumps({'status':'PASS_EXTERNAL_MATHEMATICAL_REVIEW','scope':'Maintained positive-zero V>0 only; transport-eliminated family, Lean and circuit savings not established'},indent=2))
