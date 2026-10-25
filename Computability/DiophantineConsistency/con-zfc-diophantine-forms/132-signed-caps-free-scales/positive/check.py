#!/usr/bin/env python3
"""Independent exact arithmetic controls; Python standard library only."""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import gzip,json,random
H=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok:raise ValueError(msg)

def ev(rows,env,mod=None):
    env=dict(env)
    for n,op,a,b in rows:
        a=env[a] if isinstance(a,str) else a;b=env[b] if isinstance(b,str) else b
        v=a*b if op=='*' else a+b if op=='+' else a-b
        env[n]=v if mod is None else v%mod
    return env

def add(a,b,sgn=1):
    c=[0]*max(len(a),len(b))
    for j,x in enumerate(a):c[j]+=x
    for j,x in enumerate(b):c[j]+=sgn*x
    while len(c)>1 and c[-1]==0:c.pop()
    return c

def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for j,x in enumerate(a):
        if x:
            for k,y in enumerate(b):c[j+k]+=x*y
    while len(c)>1 and c[-1]==0:c.pop()
    return c

def ray(obj,ports,weights,mod=None):
    e={n:[0,weights[n]] for n in obj['witnesses']}|{n:[ports[n]] for n in obj['fixed_numerals']}
    for n,op,a,b in obj['source']:
        a=e[a] if isinstance(a,str) else [a];b=e[b] if isinstance(b,str) else [b]
        v=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
        if mod:
            v=[x%mod for x in v]
            while len(v)>1 and v[-1]==0:v.pop()
        e[n]=v
    return e['N']

def leading(kind,w,p):
    q=p['beta']*w['J'];X=q+w['x'];k=w['eta']+w['zeta']
    return (-1 if kind=='first' else 1)*2**20*q**122*X**(27 if kind=='first' else 26)*w['Y']**60*w['i']**10*k**32*(q-w['F'])**2

# Sparse free-polynomial verification, independent of sample points.
def pc(x,d=3):return {(0,)*d:x} if x else {}
def pv(j,d=3):return {tuple(int(i==j) for i in range(d)):1}
def pa(a,b,sgn=1):
    c=dict(a)
    for m,v in b.items():c[m]=c.get(m,0)+sgn*v
    return {m:v for m,v in c.items() if v}
def ps(a,b):return pa(a,b,-1)
def pm(a,b):
    c={}
    for m,v in a.items():
        for n,w in b.items():
            k=tuple(x+y for x,y in zip(m,n));c[k]=c.get(k,0)+v*w
    return {m:v for m,v in c.items() if v}
p,X,k=[pv(j) for j in range(3)];one=pc(1);p2=pm(p,p);p3=pm(p2,p);p4=pm(p2,p2);k2=pm(k,k)
v0=pm(p2,X);A=pa(pm(p,pa(X,one)),one);D=pa(pm(pm(v0,pa(v0,one)),k2),one)
Q1=pm(pm(p,v0),k2);Q2=pm(pm(p,ps(v0,p2)),k2)
R1=pa(pm(pm(v0,ps(one,pa(p2,p))),k2),one)
R2=pa(pm(pa(pa(ps(p4,pm(p3,X)),p3),pm(p2,X)),k2),one)
need(ps(D,pm(A,Q1))==R1,'free polynomial remainder1')
need(ps(D,pm(A,Q2))==R2,'free polynomial remainder2')
# Whole-carrier shift n_old=n+S is a universal polynomial identity.
n,S,V,pb,other=[pv(j,5) for j in range(5)]
need(pa(ps(pa(pa(n,S),V),pb),other)==pa(ps(pa(n,pa(V,S)),pb),other),'universal carrier identity')

prior=json.loads((H/'prior/uncentered.json').read_text())
sharp=json.loads((H/'prior/sharp.json').read_text())
ports={}
for n,d in prior['coefficient_binding']['ports'].items():
    b=(H/'coefficients'/d['file']).read_bytes();r=gzip.decompress(b)
    need(sha256(b).hexdigest()==d['gzip_sha256'],'gzip hash '+n)
    need(sha256(r).hexdigest()==d['raw_sha256'],'payload hash '+n)
    ports[n]=int.from_bytes(r,'little');need(ports[n].bit_length()==d['bits'],'bit length '+n)
need(ports['beta']%2==1 and ports['beta']>=31 and ports['K0']>0 and 0<ports['MC']<ports['beta']<ports['MF']<2*ports['beta'],'coherent coefficient box')
rng=random.Random(16252);out={}
for kind,count,degree in [('first',102,253),('second',104,252)]:
    obj=json.loads((H/(kind+'.json')).read_text())
    need(obj['coefficient_binding']==prior['coefficient_binding'],'unaltered coefficient binding')
    need(obj['parent_sha256']==sha256((H/'prior/sharp.json').read_bytes()).hexdigest(),'parent source pin')
    rows=obj['source'];names={r[0] for r in rows};need(len(names)==len(rows)==count,'gate count')
    need(dict(Counter(r[1] for r in rows))==obj['operation_breakdown'],'operation breakdown')
    dg={n:1 for n in obj['witnesses']}|{n:0 for n in obj['fixed_numerals']};live={'N'}
    for name,op,a,b in rows:
        need(name not in dg and op in ['+','-','*'],'topological register')
        da=dg[a] if isinstance(a,str) else 0;db=dg[b] if isinstance(b,str) else 0
        dg[name]=da+db if op=='*' else max(da,db)
    for name,op,a,b in reversed(rows):
        if name in live:live.update(x for x in [a,b] if isinstance(x,str))
    need(set(dg)==live,'whole DAG liveness');need(dg==obj['register_degrees'],'syntactic degree schedule')
    base={r[0]:r for r in sharp['source']};new={r[0]:r for r in rows}
    for name,r in base.items():
        if name not in {'I','Cg'}:need(new[name]==r,'retained register '+name)
    expected=[['E0','*','i','c2'],['I','*',2,'E0'],['Cg0','*','Afull','DtauI'],['pk','*','muY','k'],['correction','*','E0','Qapprox'],['Cg','-','Cg0','correction']]
    expected+=([['Qapprox','*','pk','V0k']] if kind=='first' else [['vminus','-','V0','muY2'],['vminusk','*','vminus','k'],['Qapprox','*','pk','vminusk']])
    for r in expected:need(new[r[0]]==r,'changed register '+r[0])
    need(names==set(base)|{r[0] for r in expected},'entire changed gate set')
    # Exact identity on signed inputs, including degenerate denominator loci.
    for z in range(96):
        env={n:rng.randint(-3,4) for n in obj['witnesses']}|{'beta':3,'K0':5,'MC':1,'MF':4}
        got=ev(rows,env);oldenv=dict(env);oldenv['i']*=2;oldenv['n']+=got['Cg'];old=ev(prior['source'],oldenv)
        for key in ['Dtau','Df','Q','V','Mtot','Znum','N']:need(got[key]==old[key],'whole-polynomial translation '+key)
    # Closed formula controls and unconditional positive-coordinate map.
    for z in range(32):
        e={n:rng.randint(1,5) for n in obj['witnesses']}|{'beta':31,'K0':7,'MC':5,'MF':37};v=ev(rows,e)
        q=e['beta']*e['J']+1;X=q+e['x'];mu=q*q+1;p=mu*e['Y'];A=p*(X+1)+1;k=e['eta']+e['zeta'];cc=k*e['Y']+e['eta'];v0=p*p*X;D=v0*(v0+1)*k*k+1;E0=e['i']*cc*cc;E=2*E0;dA=A*A-1
        qa=p*(v0 if kind=='first' else v0-p*p)*k*k;S=A*D*E-E0*qa
        Fs=1+dA*D*E*E;Q=dA*dA*D*E*E;delta=Q-1;R=((q-1)*(q-e['F'])+e['alpha'])*(q*q-1)+(e['MC']+q*e['MF'])*e['J'];b=cc*(e['T']+e['alpha'])-R;VV=Fs*b-cc
        B=(q*e['K0']+X)*(q-e['F']-e['alpha'])-q*e['F'];Hh=4*A-5;P=q**4*(q-1);M=P*mu*mu*Hh;K=X*(3*cc-2*X)+2
        Z=P*mu*mu*(Hh*(e['n']+VV+S-b*B)+K)+Hh*(mu*mu*(q*(q-1)*e['Y']-q**3*B-(q-1)*X)-P*(k-R-1))
        u=delta*M*M*D*Fs;vv=M*M*(Q*VV*VV-1);ss=delta*Z*Z
        need(v['Znum']==Z and v['N']==(ss-u-vv)**2-4*u*vv,'independent literal formula')
        need(0<qa<D and 0<S<A*D*E and e['n']+S>0,'unconditional positive map')
    toy={'beta':2,'K0':3,'MC':5,'MF':7};w={n:1 for n in obj['witnesses']};rr=ray(obj,toy,w)
    need(len(rr)-1==degree and rr[-1]==leading(kind,w,toy),'exact integer ray')
    modular=[]
    for prime in [1000000007,1000000009,998244353]:
        pp={n:v%prime for n,v in ports.items()};w={n:rng.randint(1,9) for n in obj['witnesses']};rr=ray(obj,pp,w,prime);want=leading(kind,w,pp)%prime
        need(want!=0 and len(rr)-1==degree and rr[-1]==want,'actual payload ray')
        modular.append({'prime':prime,'degree':degree,'leading_coefficient':want})
    out[kind]={'operations':count,'exact_degree':degree,'signed_polynomial_identity_controls':96,'positive_formula_controls':32,'integer_ray_degree':degree,'actual_payload_controls':modular}

# Finite exact controls for the strengthened 2*tau*c^2 period requirement.
periods=[]
for A,c,tau in [(2,15,1),(3,35,1),(3,35,2)]:
    modulus=2*tau*c*c
    a,b,cc,d=1,0,0,1
    for m in range(1,1000000):
        a,b,cc,d=(2*A*a+b)%modulus,(-a)%modulus,(2*A*cc+d)%modulus,(-cc)%modulus
        if (a,b,cc,d)==(1,0,0,1):break
    else:raise ValueError('period test budget exhausted')
    need(cc==0,'ordinate divisibility at identity')
    periods.append({'A':A,'c':c,'tau':tau,'modulus':modulus,'matrix_identity_period':m})
print(json.dumps({'status':'PASS','free_polynomial_remainder_identities':2,'free_polynomial_carrier_identity':True,'coherent_payload_hashes_verified':True,'circuits':out,'doubled_pell_period_controls':periods,'scope':'Finite controls and universal polynomial identities supplement, not replace, the unbounded proof.'},indent=2))
