#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'ModelMap.lean').read_text()
for t in ('P72ExactIndices84Draft.exact_indices','gamma_gt_from_modified_balance','map_84_to_85','4*X*q*(v 7)*s','hMC : MC<beta','hMF : MF<2*beta','(hz : InternalZero (P84QcubeGraph.graph p).output v)'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
rng=random.Random(840115)
for _ in range(200):
 q=rng.randint(1,12);w=rng.randint(1,8);ss=rng.randint(1,8);r=rng.randint(0,20);n=rng.randint(1,20);t=rng.randint(0,10);X=q*w;Y=q**3*ss;U=Y*q*q;W=4*X*q*ss*t
 assert 4*(X*Y)*Y*t==U*W
 R=2*n-1;k=2*n+4*(X*Y)*Y*t;assert k==R+1+U*W
for name in ('ordinary14-84-p72-exact-indices-draft','ordinary14-modified-carrier-gamma-model-draft','ordinary14-84-85-conditional-model-draft'):
 p=D/'research'/name;r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
 assert not r.stderr and r.stdout==(p/'observation.json').read_bytes(),name
paths=[P/'ModelMap.lean',D/'research/ordinary14-84-p72-exact-indices-draft/P72ExactIndices.lean',D/'research/ordinary14-modified-carrier-gamma-model-draft/CarrierGamma.lean',D/'research/ordinary14-84-85-conditional-model-draft/ConditionalComparison.lean']
print(json.dumps({'scope':'source interface inventory, finite quotient-identity controls and draft receipt replays; no Lean invocation','finite_controls':200,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
