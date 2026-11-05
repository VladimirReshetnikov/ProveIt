#!/usr/bin/env python3
"""Exact finite premises and DAG controls for symbolic equal-rank witness."""
import hashlib, json, math, operator, random, sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('requires python3 -I -S -B without optimization')
root=Path(__file__).resolve().parents[2]
graph=root/'research/p64-qcube72-free-main-candidate/graph.json'
expected='875a9d0972c350e6858e25b68f2dc794b1f330e61f29cd52a5853ece90b24806'
if hashlib.sha256(graph.read_bytes()).hexdigest()!=expected:
    raise RuntimeError('graph pin mismatch')
a=json.loads(graph.read_bytes())
if len(a['source'])!=72: raise RuntimeError('wrong graph size')
D=36480; P=4374; U=729; H=759; X=6; A=189; m=19259; j=11720

def mul(a,b,d):
    x,y=a; u,v=b
    return (x*u+d*y*v,x*v+y*u)
def power(base,n,d):
    ans=(1,0)
    while n:
        if n&1: ans=mul(ans,base,d)
        n//=2
        if n: base=mul(base,base,d)
    return ans

g,c=power((191,1),m,D)
t,k=power((2*P+1,2),j,P*(P+1))
if g*g-D*c*c!=1 or t*t-P*(P+1)*k*k!=1: raise RuntimeError('Pell norm')
if not 27*k<c<28*k: raise RuntimeError('strict scale')
eta,zeta=c-27*k,28*k-c
if not (eta>0 and zeta>0 and eta+zeta==k):raise RuntimeError('witness positivity')
numerator=U*(g-X-A*c)
h,r=divmod(numerator,H)
if r or h<=0:raise RuntimeError('free carrier divisibility or sign')
R=40+19219
if (R,m)!=(19259,19259):raise RuntimeError('actual rank')
if (h%U,k%U,m%U,(h+k-R-1)%U)!=(486,112,305,292):raise RuntimeError('inverse residue')
mu=U//math.gcd(U,H)
if (mu,(2*j-m-1)%mu)!=(243,49):raise RuntimeError('first-index residue')
if not (m%4==3 and 19219>2 and R+1>3**4):raise RuntimeError('scope/window controls')
# Exercise the real 72-row graph against independently written residual formulas.
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}; rng=random.Random(722025)
for _ in range(160):
    v={n:rng.randrange(1,6) for n in a['witnesses']}
    v.update({n:rng.randrange(0,6) for n in a['fixed_numerals']})
    d=v.copy()
    for name,op,x,y in a['source']:
        d[name]=ops[op](d[x] if isinstance(x,str) else x,d[y] if isinstance(y,str) else y)
    q=v['beta']*v['J']+1; Y=q**3*v['s']; X0=v['w']*q; U0=Y**2
    ell=X0*Y*Y*(v['eta']+v['zeta']); k0=v['eta']+v['zeta']
    c0=k0*Y+v['eta']; a0=X0*Y+Y; H0=4*a0+3; D0=a0*a0+H0
    C=q-v['F']-v['alpha']; R0=((q-1)*(q-v['F'])+v['alpha'])*(q*q-1)+(v['MC']+q*v['MF'])*v['J']
    t0=v['t']**2-ell*(ell+k0)
    M=(U0*(X0+a0*c0)+H0*v['h'])**2-U0**2*(1+D0*c0*c0)
    W=(v['i']*c0*c0)**2-D0*(v['f']**2-1)
    V=v['f']**2*(c0*v['T']-R0)-c0
    Na=D0*(v['f']**2-1)*(V*V-v['y']**2)+v['y']**2
    Lt=(v['K0']+v['w'])*C-v['F']-v['z']*(q-1)
    vals={'q':q,'Y':Y,'X':X0,'U':U0,'c':c0,'a':a0,'H':H0,'Delta':D0,'R':R0,'A0':t0,'M':M,'W':W,'V':V,'Na':Na,'Lt':Lt,'polynomial':(t0*Na-1)**2+M*M+W*W+Lt*Lt}
    if any(d[n]!=val for n,val in vals.items()):raise RuntimeError('graph formula mismatch')
print(json.dumps({'status':'PASS_EXACT_FINITE_PREMISES','m':m,'j':j,'R':R,'g_bits':g.bit_length(),'c_bits':c.bit_length(),'t_bits':t.bit_length(),'k_bits':k.bit_length(),'h_mod_729':h%U,'k_mod_729':k%U,'R_mod_729':R%U,'old_carrier_mod_729':(h+k-R-1)%U,'mu':mu,'first_index_mod_mu':(2*j-R-1)%mu,'graph_formula_controls':160,'graph_sha256':expected,'scope':'Exact finite Pell coordinates and modular/size premises; bounded graph formula controls. Strong and auxiliary witnesses are symbolic and are not expanded or Lean-checked.'},sort_keys=True))
