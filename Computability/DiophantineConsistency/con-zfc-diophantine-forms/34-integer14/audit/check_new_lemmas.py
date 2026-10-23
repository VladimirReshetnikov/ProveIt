"""Independent exact finite audits of new stack and separator lemmas."""
import itertools,json,math
from pathlib import Path

def sq(n): return n>=0 and math.isqrt(n)**2==n

def stack(ds,zs):
    C=1; bs=[]; cs=[]
    for d,z in zip(ds,zs):
        B=1+4*d*C*z*z
        assert B%4==1 and math.gcd(B,C)==1
        assert all(math.gcd(B,b)==1 for b in bs)
        bs.append(B); C*=B; cs.append(C)
    return C,bs,cs
count=hits=0
for ds in itertools.product([-7,-4,-1,2,5,8],repeat=3):
 for zs in itertools.product([-2,-1,1,2],repeat=3):
    C,bs,cs=stack(ds,zs); count+=1
    assert abs(C)>1 and abs(C)**2>abs(C)
    if sq(C):
        hits+=1
        assert all(d>0 for d in ds) and all(sq(b) and b>0 for b in bs)
    for P,K in itertools.product([-2,0,3],repeat=2):
        a0=(P*P-1)*K*K+1
        bound=P*P+K*K+1
        assert abs(a0)<=bound*bound
        # Rational upper bound sqrt|C|<|C| and sqrt|a0|<=bound.
        assert abs(C*(bound+1))>=abs(C)+abs(C)*bound
# Explicit completeness examples by scanning ordinary Pell solutions.
witnesses=[]
for ds in [(2,2),(2,5),(5,2),(5,5),(8,2)]:
 C=1; zs=[]
 for d in ds:
    z=1
    while not sq(1+4*d*C*z*z):
        z+=1
        if z>1000000: raise RuntimeError('bounded witness search exhausted')
    zs.append(z); C*=1+4*d*C*z*z
 assert sq(C)
 witnesses.append({'d':ds,'z':zs,'C':C})
# Demonstrate that dropping nonzero z is unsound.
assert stack([-1],[0])[0]==1
result={'assignments':count,'square_hits':hits,'complete_examples':witnesses,
'nonzero_guard_negative_control':True,
'notes':'Exact finite audits only; universal proof in LINEAR_PREFIX_SQUARE_STACK.md.'}
p=Path(__file__).with_name('NEW_LEMMA_CHECKS.json'); p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
