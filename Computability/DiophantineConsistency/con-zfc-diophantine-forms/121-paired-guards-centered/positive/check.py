#!/usr/bin/env python3
"""Independent graph, exact-carrier, coefficient, Pell, and degree controls."""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import gzip,importlib.util,json,random
H=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('oldcheck',H/'source/prior_check.py');oldcheck=importlib.util.module_from_spec(spec);spec.loader.exec_module(oldcheck)
def need(p,s):
    if not p:raise ValueError(s)
def evaluate(rows,e,m=None):return oldcheck.eval_rows(rows,e,m)
def add(a,b,sign=1):
    c=[0]*max(len(a),len(b))
    for j,x in enumerate(a):c[j]+=x
    for j,x in enumerate(b):c[j]+=sign*x
    while len(c)>1 and not c[-1]:c.pop()
    return c
def mul(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b):c[i+j]+=x*y
    while len(c)>1 and not c[-1]:c.pop()
    return c
def ray(c,ports,weights,mod=None):
    e={n:[0,weights[n]] for n in c['witnesses']}|{n:[ports[n]] for n in c['fixed_numerals']}
    for n,op,a,b in c['source']:
        a=e[a] if isinstance(a,str) else [a];b=e[b] if isinstance(b,str) else [b]
        v=mul(a,b) if op=='*' else add(a,b,1 if op=='+' else -1)
        if mod:
            v=[x%mod for x in v]
            while len(v)>1 and not v[-1]:v.pop()
        e[n]=v
    return e['N']
def leading(kind,w,p):
    q=p['beta']*w['J'];X=q+w['x'];k=w['eta']+w['zeta'];j=w['i'];Y=w['Y'];F=w['F']
    c,qp,xp,yp={'uncentered':(-2**10,126,30,62),'upper':(2**11,124,29,61),'sharp':(2**10,122,28,60)}[kind]
    return c*q**qp*X**xp*Y**yp*j**10*k**32*(q-F)**2
parent=json.loads((H/'source/prior96_equation.json').read_text());pr={r[0]:r for r in parent['source']}
ports={}
for n,d in parent['coefficient_binding']['ports'].items():
    data=(H/'coefficients'/d['file']).read_bytes();raw=gzip.decompress(data)
    need(sha256(data).hexdigest()==d['gzip_sha256'],'gzip hash '+n);need(sha256(raw).hexdigest()==d['raw_sha256'],'raw hash '+n)
    ports[n]=int.from_bytes(raw,'little');need(ports[n].bit_length()==d['bits'],'bit length '+n)
need(ports['beta']%2==1 and 0<ports['MC']<ports['beta']<ports['MF']<2*ports['beta'] and ports['K0']>0,'coherent ports bounds')
rng=random.Random(1510);results={}
for kind,count,degree in [('uncentered',94,262),('upper',96,258),('sharp',97,254)]:
    c=json.loads((H/(kind+'.json')).read_text());nr={r[0]:r for r in c['source']}
    inserted=set() if kind=='uncentered' else {'Cg','nVCg'}|({'Afull'} if kind=='sharp' else set())
    need(set(nr)==(set(pr)-{'HI','L'})|inserted,'whole row map '+kind)
    changed={'LB':['LB','*','cTR','B']}
    if kind!='uncentered':changed['nVL']=['nVL','-','nVCg','LB']
    for n in set(pr)&set(nr):need(nr[n]==changed.get(n,pr[n]),'retained gate '+n)
    explicit=[]
    if kind!='uncentered':explicit=[['Cg','*','Afull' if kind=='sharp' else 'Ap1','DtauI'],['nVCg','+','nV','Cg']]
    if kind=='sharp':explicit+=[['Afull','+','Am1',1]]
    for r in explicit:need(nr[r[0]]==r,'new gate '+r[0])
    env={n:1 for n in c['witnesses']}|{n:0 for n in c['fixed_numerals']};live={'N'}
    for n,op,a,b in c['source']:
        need(n not in env and op in ['+','-','*'],'DAG topology')
        da=env[a] if isinstance(a,str) else 0;db=env[b] if isinstance(b,str) else 0
        env[n]=da+db if op=='*' else max(da,db)
    for n,op,a,b in reversed(c['source']):
        if n in live:live.update(x for x in [a,b] if isinstance(x,str))
    need(set(env)==live,'all vertices live');need(env==c['register_degrees'],'degree schedule')
    need(len(nr)==len(c['source'])==count and dict(Counter(r[1] for r in c['source']))==c['operation_breakdown'],'gate count')
    # Identity n_old=n_new+C_g+H D E B, valid for all integers, no positivity premises.
    for j in range(64):
        e={n:rng.randint(-3,5) for n in c['witnesses']}|{'beta':3,'K0':5,'MC':1,'MF':4}
        new=evaluate(c['source'],e);oldenv=dict(e);oldenv['n']+=new.get('Cg',0)+new['Hp']*new['DtauI']*new['B']
        old=evaluate(parent['source'],oldenv)
        need(new['Znum']==old['Znum'] and new['N']==old['N'],'whole carrier/norm translation')
    toy={'beta':2,'K0':3,'MC':5,'MF':7};weights={n:1 for n in c['witnesses']};v=ray(c,toy,weights)
    need(len(v)-1==degree and v[-1]==leading(kind,weights,toy),'exact integer ray')
    modular=[]
    for prime in [1000000007,1000000009,998244353]:
        pp={n:x%prime for n,x in ports.items()};w={n:rng.randint(1,9) for n in c['witnesses']};v=ray(c,pp,w,prime)
        expected=leading(kind,w,pp)%prime
        need(expected!=0 and len(v)-1==degree and v[-1]==expected,'actual-port nonzero leading form')
        modular.append({'prime':prime,'degree':degree,'leading_coefficient':expected})
    # Independent literal formula at positive toy points.
    for j in range(12):
        e={n:rng.randint(1,4) for n in c['witnesses']}|{'beta':31,'K0':7,'MC':5,'MF':37};v=evaluate(c['source'],e)
        q=e['beta']*e['J']+1;X=q+e['x'];mu=q*q+1;A=mu*e['Y']*(X+1)+1;deltaA=A*A-1;k=e['eta']+e['zeta'];cc=k*e['Y']+e['eta'];u=e['i']*cc*cc
        first=X*mu*mu*e['Y']**2;D=first*(first+1)*k*k+1;Fs=1+deltaA*D*u*u;Q=deltaA*deltaA*D*u*u;dd=Q-1
        R=((q-1)*(q-e['F'])+e['alpha'])*(q*q-1)+(e['MC']+q*e['MF'])*e['J'];b=cc*(e['T']+e['alpha'])-R;V=Fs*b-cc
        B=(q*e['K0']+X)*(q-e['F']-e['alpha'])-q*e['F'];h=4*A-5;P=q**4*(q-1);M=P*mu*mu*h;K=X*(3*cc-2*X)+2
        S=0 if kind=='uncentered' else (A+(kind=='upper'))*D*u
        Z=P*mu*mu*(h*(e['n']+V+S-b*B)+K)+h*(mu*mu*(q*(q-1)*e['Y']-q**3*B-(q-1)*X)-P*(k-R-1))
        aa=dd*M*M*D*Fs;vv=M*M*(Q*V*V-1);ss=dd*Z*Z
        need(v['Znum']==Z and v['N']==(ss-aa-vv)**2-4*aa*vv,'independent formula')
    results[kind]={'operations':count,'degree':degree,'integer_ray_degree':len(ray(c,toy,weights))-1,'signed_translation_controls':64,'formula_controls':12,'actual_ports':modular}
# Universal new transport identity (free polynomial coefficients), not merely controls.
d=7;n,S,h,D,E,B,b=[oldcheck.pv(i,d) for i in range(d)]
plus=oldcheck.pa;minus=oldcheck.ps;times=oldcheck.pm
old_center=minus(plus(n,plus(S,times(times(times(h,D),E),B))),times(plus(times(times(h,D),E),b),B))
new_center=minus(plus(n,S),times(b,B));need(old_center==new_center,'universal free-ring transport identity')
receipt={'status':'PASS','algebra':oldcheck.algebra(),'finite_pell_controls':oldcheck.finite_pell(),'circuits':results,'scope':'Finite replay and algebra controls supplement the unbounded proof, not replace it.'}
print(json.dumps(receipt,indent=2))
