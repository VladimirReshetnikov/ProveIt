#!/usr/bin/env python3
"""Independent 74 first-factor and natural-size audit; no Lean."""
from pathlib import Path
from itertools import product
import hashlib,json,random,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-74-first-factor-client-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'README.md':'0ba7e71f590ae0bf3e4d9611277db0a963a357596a9f3d9243a0c28db5b65148','FirstFactor74.lean':'fca24f5e8e3be0743e3423f66573e099a211f3c2cfc973d69f77c0a2ff8d62f4','check_source.py':'e57eb86a85416862059a0b803853c43318b49c0731b93bff873b93891345de43','observation.json':'baa5e23e97cc3a43e14626392c20bbb7fc6cdb4cbd62630287dc71bc43394f0a'}
tail=b"\nIndependent source review: [74 first-factor client](../../reviews/ordinary14-74-first-factor-client-independent/README.md).\n"
final=(A/'README.md').read_bytes()
assert hashlib.sha256(final).hexdigest()=='17a37f4c22fc49dad3d291a07109573fa769e3bbcc4b40c00deaa6204270ee79'
assert final.endswith(tail) and hashlib.sha256(final[:-len(tail)]).hexdigest()==pins['README.md']
for n,h in pins.items():
 if n!='README.md':assert sha(A/n)==h,n
s=(A/'FirstFactor74.lean').read_text();graph=D/'research/ordinary14-unit75-guard74-lean-draft/P74PositiveGuard.lean';bridge=D/'research/ordinary14-pair-eval-ring-bridge-draft/PairEvalRingBridge.lean';cand=D/'research/ordinary14-positive-guard74/candidate.json'
for p,h in [(graph,'5c441b8df055693e745967f01ef8128d808f5915e3cffb906473499745c4c11b'),(bridge,'0fdb641db2008362ae3ec363bea66f6b4a4b475c1de2d5d00b7c1e9a81adc510'),(cand,'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093')]:assert sha(p)==h
for token in ['def q (beta : V) (v : Fin 14 → V) : V := 1+v 0*beta','def X (beta : V) (v : Fin 14 → V) : V := q beta v*v 6','def Y (beta : V) (v : Fin 14 → V) : V := (q beta v*(q beta v*q beta v))*v 7','def m (beta : V) (v : Fin 14 → V) : V := X beta v*Y beta v*Y beta v','(hbeta : (p 0 : DiffRing V)=ι beta)','(hb : 0<beta) (hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)','(m_at_least_two beta v hb hJ hw hs) a b guard t','(first_eval p beta v hbeta) hp ha hb\' ht']:
 assert token in s,token
bt=bridge.read_text()
for token in ['theorem five_positive_of_first_eval','(m x k : V) (hm : 2≤m) (q r s t : Pair V)','(hq : pairResidue q ≠ -1) (hr : pairResidue r ≠ -1)','(ht : pairResidue t ≠ -1)']:
 assert token in bt,token
# Independently authenticate the graph rows that enter first factor.
rows={row[0]:row[1:] for row in json.loads(cand.read_text())['source']}
for name,definition in {'qm':['*','J','beta'],'q':['+',1,'qm'],'X':['*','q','w'],'q2':['*','q','q'],'q3':['*','q','q2'],'Y':['*','q3','s'],'E':['*','X','Y'],'k':['+','eta','zeta'],'kY':['*','Y','k'],'ell':['*','E','kY'],'g30':['+','ell','k'],'g38':['*','r','r'],'g40':['*','ell','g30'],'F0':['-','g38','g40']}.items():assert rows[name]==definition,(name,rows[name])
size=0
for beta,J,w,s0 in product(range(1,9),repeat=4):
 q=1+J*beta;X=q*w;Y=q*q*q*s0;m=X*Y*Y
 assert q>=2 and X>=2 and Y>=1 and m>=2
 size+=1
rng=random.Random(747400)
for _ in range(2000):
 X,Y,k,r=[rng.randrange(-10,11) for _ in range(4)];ell=(X*Y)*(Y*k);m=X*Y*Y
 assert ell==m*k and r*r-ell*(ell+k)==r*r-(m*k)*(m*k+k)
assert subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,check=True,capture_output=True).stdout==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source-interface and finite controls; pair-eval bridge is an explicit unreviewed dependency; no Lean or endpoint','author_pins':pins,'graph_sha256':sha(graph),'unreviewed_bridge_sha256':sha(bridge),'positive_size_controls':size,'signed_first_identity_controls':2000,'author_receipt_reproduced':True},sort_keys=True,indent=2))
