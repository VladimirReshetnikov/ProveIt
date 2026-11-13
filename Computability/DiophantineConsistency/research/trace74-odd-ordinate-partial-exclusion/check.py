#!/usr/bin/env python3
"""Exact sparse-polynomial exclusion of one prior partial tuple; not a Lean check."""
import gzip, hashlib, json, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('invoke python3 -I -S -B')
root=Path(__file__).resolve().parents[2]
def sha(x): return hashlib.sha256(x).hexdigest()
pins={
'research/trace75-root-probe/Trace75Factors.lean':'14667194d1027fb9c5b23825165efdf67488c0f2632dedd62e3c1075fdce8eb2',
'research/trace74-guardfree-fold-draft/Trace74Fold.lean':'27fdb1e75e0dde20e132f37bb8eb117a5b7090de8eb5f8153c042368568810ae',
'research/trace74-large-f-positive-carrier-scalar/check.py':'4c2adc4812244b917e8526fc7eada30220624049ceb026098acae0795e7e3a08',
'research/trace74-mask-coordinate-probe/candidate.json':'dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'}
for path,digest in pins.items(): assert sha((root/path).read_bytes())==digest
candidate=json.loads((root/'research/trace74-mask-coordinate-probe/candidate.json').read_text())
binding=candidate['coefficient_binding']['ports']['beta']; compressed=(root/'candidates/ten-positive-qcube-product-square/coefficients'/binding['file']).read_bytes(); raw=gzip.decompress(compressed)
assert sha(compressed)==binding['parent_gzip_sha256'] and sha(raw)==binding['raw_sha256']
beta=int.from_bytes(raw,'little'); q=beta+1
assert q==2**(67*8807) and q>=32
# Sparse polynomials over Z, coefficients keyed by degree in q.
def add(a,b,sign=1):
    out=dict(a)
    for i,v in b.items(): out[i]=out.get(i,0)+sign*v
    return {i:v for i,v in out.items() if v}
def mul(a,b):
    out={}
    for i,x in a.items():
        for j,y in b.items(): out[i+j]=out.get(i+j,0)+x*y
    return {i:v for i,v in out.items() if v}
one={0:1}; X={4:1}; Y={3:1}; k={10:8,0:4}; eta=one
A=add(mul(X,Y),Y); c=add(mul(k,Y),eta)
assert A=={7:1,3:1} and c=={13:8,3:4,0:1}
# Pell recurrence for b=A-1 has base b+2=A+1, delta=(b+1)(b+3)=A(A+2).
base=add(A,one); delta=mul(A,add(A,{0:2})); x=one; y={}
ys=[]
for _ in range(3):
    x,y=add(mul(base,x),mul(delta,y)),add(x,mul(base,y));ys.append(y)
assert ys[0]==one
# y_3-c = 4q^13(q-2)+8q^10+8q^7+4q^6+4q^3+2 > 0 for q>=32.
gap=add(ys[2],c,-1)
expected={14:4,13:-8,10:8,7:8,6:4,3:4,0:2}
assert gap==expected, (gap, expected)
assert 4*(q-2)>0
assert c[0]>1 or any(i>0 and v>0 for i,v in c.items())
for path,digest in pins.items(): assert sha((root/path).read_bytes())==digest
print(json.dumps({'status':'PASS','input_pins':pins,'beta_raw_sha256':sha(raw),'beta_gzip_sha256':sha(compressed),'q':'2^(67*8807)','q_ge_32':True,'tuple':{'X':'q^4','Y':'q^3','k':'8*q^10+4','eta':1},'A':'q^7+q^3','c':'8*q^13+4*q^3+1','ordinate_1':1,'ordinate_3_minus_c':'4*q^13*(q-2)+8*q^10+8*q^7+4*q^6+4*q^3+2','one_lt_c_lt_ordinate_3':True,'scope':'External exact polynomial check of this partial assignment against a separately checked graph-zero odd-ordinate consequence; no symbolic fixed-port binding, no full graph zero or general bound.'},sort_keys=True,indent=2))
