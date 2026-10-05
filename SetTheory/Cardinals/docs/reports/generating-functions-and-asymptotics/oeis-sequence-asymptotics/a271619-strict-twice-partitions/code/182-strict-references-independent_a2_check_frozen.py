from fractions import Fraction as Q
import sympy as s
import json
from pathlib import Path
N=20

def partitions(n, mx=None):
    if n==0:
        yield ()
        return
    if mx is None: mx=n
    for k in range(min(n,mx),0,-1):
        for t in partitions(n-k,k): yield (k,)+t

def shifted(lam,j):
    return sum((Q(2*v-2*i+1,2)**j-Q(-2*i+1,2)**j for i,v in enumerate(lam,1)),Q(0))

def mul(a,b):
    return [sum((a[k]*b[n-k] for k in range(n+1)),Q(0)) for n in range(N+1)]
def power(a,k):
    z=[Q(1)]+[Q(0)]*N
    for _ in range(k): z=mul(z,a)
    return z
P=[0]*(N+1); raw=[[Q(0)]*(N+1) for _ in range(3)]
for n in range(N+1):
    for lam in partitions(n):
        P[n]+=1
        q2=shifted(lam,2); q3=shifted(lam,3)+Q(7,960)
        for row,v in zip(raw,[q3*q3,q2*q2*q3,q2**4]): row[n]+=v
E=[]
for wt,mult in [(2,-24),(4,240),(6,-504)]:
    E.append([Q(1)]+[Q(mult*sum(d**(wt-1) for d in range(1,n+1) if n%d==0)) for n in range(1,N+1)])
inv=[Q(1)]+[Q(0)]*N
for n in range(1,N+1): inv[n]=-sum((Q(P[k])*inv[n-k] for k in range(1,n+1)),Q(0))
t,p=s.symbols('t p', nonzero=True)
subs=[-4*p**2/t**2+12/t,16*p**4/t**4,-64*p**6/t**6]
result={}
for name,wt,data in zip(['Q3hat_squared','Q2_squared_Q3hat','Q2_fourth'],[8,10,12],raw):
    bracket=mul(data,inv)
    mon=[(a,b,c) for a in range(wt//2+1) for b in range(wt//4+1) for c in range(wt//6+1) if 2*a+4*b+6*c==wt]
    col=[mul(mul(power(E[0],a),power(E[1],b)),power(E[2],c)) for a,b,c in mon]
    mat=s.Matrix([[v[n] for v in col] for n in range(len(mon))])
    coeff=mat.inv()*s.Matrix(bracket[:len(mon)])
    for n in range(N+1):
        if sum(coeff[j]*col[j][n] for j in range(len(mon)))!=bracket[n]: raise RuntimeError((name,n))
    laurent=s.expand(sum(co*subs[0]**a*subs[1]**b*subs[2]**c for co,(a,b,c) in zip(coeff,mon)))
    result[name]={'weight':wt,'basis':mon,'coefficient':[str(v) for v in coeff], 'initial_determinant':str(mat.det()),'laurent':str(laurent),'checked_coefficients':N+1}
print(json.dumps(result,indent=2))
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
