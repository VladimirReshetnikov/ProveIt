#!/usr/bin/env python3
"""Independent arithmetic, coefficient, and exact-degree audit (stdlib).

This does not verify the unbounded compiler or decide Con(ZFC).
"""
import gzip
import hashlib
import json
from collections import Counter
from pathlib import Path
import random

ROOT=Path(__file__).resolve().parent

def need(ok,message):
    if not ok: raise ValueError(message)

def add(a,b,sign=1):
    c=dict(a)
    for m,v in b.items():
        c[m]=c.get(m,0)+sign*v
        if not c[m]: del c[m]
    return c

def mul(a,b):
    c={}
    for m,v in a.items():
        for n,w in b.items():
            p=tuple(x+y for x,y in zip(m,n))
            c[p]=c.get(p,0)+v*w
    return {m:v for m,v in c.items() if v}

def poly_power(a,n,one):
    b=one
    while n:
        if n&1:b=mul(b,a)
        a=mul(a,a);n//=2
    return b

def uni_add(a,b,p,sign=1):
    c=[0]*max(len(a),len(b))
    for j,v in enumerate(a):c[j]+=v
    for j,v in enumerate(b):c[j]+=sign*v
    c=[v%p for v in c]
    while len(c)>1 and not c[-1]:c.pop()
    return c

def uni_mul(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for j,v in enumerate(a):
        for k,w in enumerate(b):c[j+k]=(c[j+k]+v*w)%p
    while len(c)>1 and not c[-1]:c.pop()
    return c

def pell(a,n):
    # Binary exponentiation of a+sqrt(a^2-1), independently of the emitter.
    delta=a*a-1
    def product(x,y):
        return (x[0]*y[0]+delta*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
    out=(1,0);base=(a,1)
    while n:
        if n&1:out=product(out,base)
        n//=2
        if n:base=product(base,base)
    return out

def quotient_poly(r,t):
    if r==0:return 1
    q0,q1=1,4*t-3
    for _ in range(1,r):q0,q1=q1,(4*t-2)*q1-q0
    return q1

def main():
    d=json.loads((ROOT/'polynomial.json').read_text())
    variables=d['witnesses'];ports=d['fixed_numerals'];names=variables+ports
    need(len(variables)==14 and len(set(names))==18,'input interface')
    Z=(0,)*len(names)
    def lit(n):return {Z:n} if n else {}
    def var(n):
        t=list(Z);t[names.index(n)]=1
        return {tuple(t):1}
    def power(a,n):return poly_power(a,n,lit(1))
    top={n:(1 if n in variables else 0,var(n)) for n in names}
    full={n:var(n) for n in names};main_expansion=None
    producers={};count=Counter()
    for name,op,a,b in d['source']:
        need(name not in top,'duplicate producer')
        need(op in ('+','-','*'),'unknown operation')
        da,pa=(0,lit(a)) if isinstance(a,int) else top[a]
        db,pb=(0,lit(b)) if isinstance(b,int) else top[b]
        degree=da+db if op=='*' else max(da,db)
        hp=mul(pa,pb) if op=='*' else add(pa if da==degree else {},pb if db==degree else {},1 if op=='+' else -1)
        if main_expansion is None:
            aa=lit(a) if isinstance(a,int) else full[a]
            bb=lit(b) if isinstance(b,int) else full[b]
            full[name]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
            if name=='main_residual':
                main_expansion=full[name]
                degree=max(sum(m[:14]) for m in main_expansion)
                hp={m:v for m,v in main_expansion.items() if sum(m[:14])==degree}
                need(degree==26,'main residual exact degree')
        if name=='square_gap':
            # Literal identity checked below: V^2-(V+e)^2=-e*(2V+e).
            need(producers['y']==('V','e'),'gap definition')
            degree=top['V'][0]+1
            hp=mul(lit(-2),mul(top['V'][1],var('e')))
        top[name]=(degree,hp);producers[name]=(a,b);count[op]+=1
    live=set();todo=[d['output']]
    while todo:
        n=todo.pop()
        if isinstance(n,int) or n in live:continue
        live.add(n);todo.extend(producers.get(n,()))
    need(live==set(top),'unused producer or port')
    need(len(d['source'])==79,'operation count')
    q0=mul(var('beta'),var('J'));k0=add(var('eta'),var('zeta'))
    expected=mul(lit(16384),mul(power(q0,38),power(k0,2)))
    for n,e in [('w',4),('s',6),('gamma',2)]:expected=mul(expected,power(var(n),e))
    need(top['polynomial'][0]==52 and top['polynomial'][1]==expected,'degree-52 leading form')
    need(top['Na'][0]==23 and top['strong_residual'][0]==22,'secondary degrees')
    # Exact three-symbol identity, including degenerate values.
    vv,ee,uu=var('T'),var('e'),var('i')
    yy=add(vv,ee)
    lhs=add(mul(uu,add(mul(vv,vv),mul(yy,yy),-1)),mul(yy,yy))
    rhs=add(mul(vv,vv),mul(add(uu,lit(1),-1),mul(ee,add(mul(lit(2),vv),ee))),-1)
    need(lhs==rhs,'gap cancellation identity')
    binding=json.loads((ROOT/'coefficients/ports.json').read_text())
    fixed={}
    for item in binding['ports']:
        packed=(ROOT/'coefficients'/item['file']).read_bytes();raw=gzip.decompress(packed)
        need(hashlib.sha256(packed).hexdigest()==item['gzip_sha256'],'compressed fixed port hash')
        need(hashlib.sha256(raw).hexdigest()==item['sha256'],'fixed port hash')
        need(len(raw)==item['bytes'],'fixed port length')
        fixed[item['port']]=int.from_bytes(raw,'little')
    need(set(fixed)==set(ports),'complete four-port tuple')
    need(fixed['beta']==(1<<1064921)-1,'literal selected beta')
    rng=random.Random(14005279);formula_checks=0;degree_checks=[]
    for prime in (1009,10007,1000003):
        # Complete univariate polynomial replay, not interpolation.
        env={n:[0,1] for n in variables}
        env.update({n:[v%prime] for n,v in fixed.items()})
        for name,op,a,b in d['source']:
            aa=[a%prime] if isinstance(a,int) else env[a]
            bb=[b%prime] if isinstance(b,int) else env[b]
            env[name]=uni_mul(aa,bb,prime) if op=='*' else uni_add(aa,bb,prime,1 if op=='+' else -1)
        leading=65536*pow(fixed['beta']%prime,38,prime)%prime
        need(len(env['polynomial'])==53 and env['polynomial'][-1]==leading!=0,'bound tuple full diagonal replay')
        degree_checks.append({'prime':prime,'degree':52,'leading_coefficient':leading})
        for _ in range(24):
            x={n:rng.randrange(prime) for n in variables}
            en={**x,**{n:v%prime for n,v in fixed.items()}}
            for name,op,a,b in d['source']:
                aa=a if isinstance(a,int) else en[a];bb=b if isinstance(b,int) else en[b]
                en[name]=(aa*bb if op=='*' else aa+bb if op=='+' else aa-bb)%prime
            q=(fixed['beta']%prime*x['J']+1)%prime;X=x['w']*q;Y=x['s']*q**3;E=X*Y
            k=x['eta']+x['zeta'];c=k*Y+x['eta'];a=E+Y;H=4*a+3;delta=a*a+H
            C=q-x['F']-x['alpha'];R=((q-1)*(q-x['F'])+x['alpha'])*(q*q-1)+((fixed['MC']%prime)+q*(fixed['MF']%prime))*x['J']
            U=4*q**4;r=k-R-1;D=U*(X+a*c)+H*(U*x['gamma']-r)
            M=D*D-U*U*(1+delta*c*c);I=x['i']*c*c;A=delta*(x['f']**2-1)
            V=x['f']**2*(c*x['T']-R)-c;y=V+x['e'];Na=A*(V*V-y*y)+y*y
            N0=x['tau']**2-X*Y*Y*(X*Y*Y+1)*k*k
            Nt=((fixed['K0']%prime)+x['w'])*C+q-x['F']-x['z']*(q-1)
            explicit=(M*M+(I*I-A)**2+Na*Na+(N0*Nt-1)**2-1)%prime
            need(explicit==en['polynomial'],'explicit formula replay')
            formula_checks+=1
    quotient_checks=0
    for a in range(2,21):
        for R in (3,7,11,15):
            need(quotient_poly((R-1)//2,1-a*a)==-pell(a,R)[1],'odd polynomial projection')
            quotient_checks+=1
    canonical_controls=0
    for a in range(2,7):
        R=3;c=pell(a,R)[1];delta=a*a-1;m=2*c*R
        f,psi=pell(a,m);need(psi%(c*c)==0,'normalized divisibility')
        rho=delta*psi;V=quotient_poly(1,rho*rho);y=pell(rho,R)[1]
        need((V+c)%(f*f)==0,'stronger f-squared congruence')
        o=(V+c)//(f*f);need((o+R)%c==0,'new positive quotient integrality')
        T=(o+R)//c;e=y-V
        need(T>0 and e>0 and V==f*f*(c*T-R)-c,'constructive squared quotient and gap')
        need(rho*rho*V*V-(rho*rho-1)*y*y==1,'canonical auxiliary norm')
        canonical_controls+=1
    # Exhaustive minimum-block controls include negative V and y.
    minimum_controls=0
    for A in range(0,10):
        for I in range(2,8):
            for V in range(-8,9):
                for e in range(1,5):
                    Na=A*(V*V-(V+e)**2)+(V+e)**2;W=I*I-A
                    if A==1:continue # Aaux is either 0 or at least 2.
                    need(Na*Na+W*W>=1,'minimum block lower bound')
                    need((Na*Na+W*W==1)==(Na==1 and W==0),'minimum equality')
                    minimum_controls+=1
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for item in pins['copied_files']:
        need(hashlib.sha256((ROOT/item['local']).read_bytes()).hexdigest()==item['sha256'],'source pin')
    result={'status':'PASS','witnesses':14,'degree':52,'operations':79,
            'counts':dict(count),'all_gates_and_ports_live':True,
            'main_residual_expansion_terms':len(main_expansion),'main_degree':26,
            'auxiliary_gap_degree':23,'strong_degree':22,
            'leading_form':'16384*w^4*s^6*(eta+zeta)^2*gamma^2*(beta*J)^38',
            'diagonal_leader':'65536*beta^38','full_univariate_replays':degree_checks,
            'formula_replays_with_actual_coefficients':formula_checks,
            'odd_polynomial_identity_controls':quotient_checks,
            'canonical_auxiliary_controls':canonical_controls,
            'minimum_block_controls':minimum_controls,
            'coefficient_hashes_verified':True,'provenance_hashes_verified':True,
            'polynomial_sha256':hashlib.sha256((ROOT/'polynomial.json').read_bytes()).hexdigest(),
            'scope':'Finite arithmetic verification; unbounded proof in PROOF.md and inherited source texts.'}
    (ROOT/'AUDIT.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
