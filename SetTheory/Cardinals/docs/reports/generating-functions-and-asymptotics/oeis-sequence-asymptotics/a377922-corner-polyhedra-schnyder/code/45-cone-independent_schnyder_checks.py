from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
(ROOT / "results").mkdir(exist_ok=True)
"""Independent exact derivation and coefficient audit for S companion."""
from collections import defaultdict
import sympy as s,json
x,y,u=s.symbols('x y u');a=x**-2;b=y**2;D=1-a-b
faces=s.Matrix([[a*b/D,y**3/x/D],[y/x**3/D,a*b/D]])
M=s.simplify(s.Matrix([[0,x/y],[x/y,0]])*(s.eye(2)-faces).inv())
H=1-a-b-2*a*b;B=x/y+y/x/H
expected=s.Matrix([[a/H,B],[B,b/H]])
assert s.simplify(M-expected)==s.zeros(2)
K=s.simplify(s.Rational(3,16)*M.subs({x:2*x,y:y/2},simultaneous=True))
ev=lambda f:s.simplify(f.subs({x:1,y:1,u:1}));dg=lambda f,z:z*s.diff(f,z)
P=K.subs({x:1,y:1});h=[-s.Rational(1,14),s.Rational(1,14)]
for i in range(2):
 for z in[x,y]:assert ev(dg(sum(K[i,j] for j in range(2)),z))+sum(P[i,j]*(h[j]-h[i]) for j in range(2))==0
 j=1-i;R=u*K[i,i]+u*u*K[i,j]*K[j,i]/(1-u*K[j,j])
 assert ev(s.diff(R,u))==2
 assert [ev(dg(R,z)) for z in[x,y]]==[0,0]
 assert [[ev(dg(dg(R,z),w)) for w in[x,y]] for z in[x,y]]==[[s.Rational(72,7),-s.Rational(176,21)],[-s.Rational(176,21),s.Rational(72,7)]]
 assert ev(s.diff(R,u,2)+s.diff(R,u))-4==s.Rational(2,7)
hc=defaultdict(int);hc[0,0]=1
for i in range(24):
 for j in range(24):
  if i+j:hc[i,j]=hc[i-1,j]+hc[i,j-1]+2*hc[i-1,j-1]
def sprime(n):
 N=n+1; d={(0,2):1}
 for t in range(N):
  rem=N-t-1;nd=defaultdict(int)
  for (xx,yy),c in d.items():
   if 1<=yy-1<=1+rem:nd[xx+1,yy-1]+=c
   for i in range(xx//2+1):
    for j in range(max(0,(1+rem-yy)//2)+1):
     if yy+2*j>1+rem:continue
     w=hc[i-1,j] if yy%2==0 and i>=1 else (hc[i,j-1] if yy%2==1 and j>=1 else 0)
     if w:nd[xx-2*i,yy+2*j]+=c*w
   for i in range((xx-1)//2+1):
    for j in range(max(0,(rem-yy)//2)+1):
     if yy+2*j+1<=1+rem:nd[xx-2*i-1,yy+2*j+1]+=c*hc[i,j]
  d=nd
 return d.get((1,1),0)
sp=[sprime(n) for n in range(15)]
ss=[sp[n]+2*sp[n-1]+sp[n-2] for n in range(4,15)]
assert ss[:8]==[3,6,14,36,102,306,972,3216]
r={'face_resolvent_kernel':'PASS','both_parity_cycle_moments':'PASS','corrector':'PASS','sprime_n_0_to_14':sp,'s_n_4_to_14':ss,'paper_coefficient_match':'PASS'}
print(json.dumps(r,indent=2));open(ROOT / "results" / "independent-schnyder-checks.json",'w').write(json.dumps(r,indent=2))
