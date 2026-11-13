from pathlib import Path
import hashlib,json,random
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'ParentScaledNorms.lean').read_text()
for t in ('first_factor_eval','main_factor_eval','FreeJ13.unit_iff_one','unit_square_norm','first_rhs_pair p v','main_rhs_pair p v','ScaledNorms p v'):assert t in s
rng=random.Random(133881)
for _ in range(1500):
 q3,b,P,r,k,Bt,Y=[rng.randrange(-5,6) for _ in range(7)]
 M=q3*b
 folded=M*(P+r-k*Bt)+Y*b-q3*Bt
 adaptive=M*(P+r)+Y*b-q3*(1+k*b)*Bt
 assert folded==adaptive
print(json.dumps({'folded_identity_controls':1500,'lean_run':False,'source_sha256':hashlib.sha256((p/'ParentScaledNorms.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
