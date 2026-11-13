#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,random,re,subprocess,sys
D=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
s=(P/'FirstIndex.lean').read_text()
for t in ('positive_parameter_solution Q tau K hQ hnorm','first_norm p beta v hbeta hJ hport hz','(hbeta : 0<beta)','(hJ : 0<v 0)','(hw : 0<v 6)','(hs : 0<v 7)'):assert t in s
assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide)\b',re.sub(r'#print axioms.*','',s))
rng=random.Random(840108)
for _ in range(200):
 X=rng.randint(1,8);Y=rng.randint(1,8);k=rng.randint(0,8);Q=X*Y*Y;ell=Q*k
 assert 1+ell*(ell+k)==1+Q*(Q+1)*k*k
for Q in range(1,17):
 k=2;tau=2*Q+1;b=2*(Q-1)+1;x1=b+2;y1=1
 assert tau*tau==1+Q*(Q+1)*k*k and x1==tau and 2*y1==k
p=D/'research/ordinary14-84-first-norm-client-draft';r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60)
assert not r.stderr and r.stdout==(p/'observation.json').read_bytes()
paths=[P/'FirstIndex.lean',p/'FirstNormClient.lean',D/'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean']
print(json.dumps({'scope':'source inventory, finite norm/first-step controls and draft receipt replay; no Lean invocation','norm_controls':200,'first_step_controls':16,'sha256':{str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}},sort_keys=True,indent=2))
