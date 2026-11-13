from pathlib import Path
import hashlib,json,random
p=Path(__file__).resolve().parent;s=(p/'ParentTo88FirstCut.lean').read_text()
for t in ('[CommRing R]','hY : Y=q3*s','ell+k+s+tau','fresh_first_cut'):assert t in s
rng=random.Random(138813)
for _ in range(2000):
 q3,b,ell,k,s0,tau=[rng.randrange(-9,10) for _ in range(6)]
 Y=q3*s0;M=q3*b
 assert M*(ell+k-(ell+k+s0+tau))+Y*b==-M*tau
print(json.dumps({'signed_controls':2000,'lean_run':False,'source_sha256':hashlib.sha256((p/'ParentTo88FirstCut.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
