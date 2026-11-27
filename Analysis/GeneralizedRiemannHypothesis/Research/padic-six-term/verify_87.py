"""Mixed-residue certificate replay for discriminant -87."""
from math import comb
# H_-87, in ascending degree; pinned fixture indicated in report.tex.
H=[549806430204864490157810211181640625,432181202257616392838287353515625,
   497577733884372638735595703125,28321090578679361484375000,
   85585228375218750,5321761711875,1]

def x_times(q):
    v=[0]+q
    return [(v[i]-v[6]*H[i])%32 for i in range(6)]

v=[1,0,0,0,0,0]
for _ in range(63):v=x_times(v)
assert v==[1,16,16,16,0,0]
assert tuple(c%2 for c in H)==(1,1,1,0,0,1,1)

def mul(x,y):
    z=0
    while y:
        if y&1:z^=x
        y>>=1
        x<<=1
        if x&64:x^=103 # X^6+X^5+X^2+X+1
    return z

xp=[1]
lp=[1]
for _ in range(62):xp.append(mul(xp[-1],2))
for _ in range(5):lp.append(mul(lp[-1],14))
assert len(set(xp))==63 and mul(xp[-1],2)==1
assert lp==[1,14,51,7,42,48]
vectors=[[mul(x,y) for y in lp] for x in xp]

def add(B,v):
    while v:
        j=v.bit_length()-1
        if not B[j]:
            C=B[:]
            C[j]=v
            return C
        v^=B[j]
    return None

def dfs(B,a,m,k):
    if not k:return 1
    s=0
    for b in range(a,63):
        j=m if a==b else 0
        C=add(B,vectors[b][j])
        if C is not None:s+=dfs(C,b,j+1,k-1)
    return s

B=add([0]*6,1)
count=dfs(B,0,1,5)
assert count==3892897
print(count,'certified anchored multisets out of',comb(67,5))
