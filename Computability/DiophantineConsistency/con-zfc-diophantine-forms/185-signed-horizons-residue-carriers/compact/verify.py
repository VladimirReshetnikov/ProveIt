#!/usr/bin/env python3
"""Exact leader/liveness checks and independent formula replay for P14.

No search for a Diophantine zero is performed. The unbounded proof is PROOF.md.
Only Python's standard library is required.
"""
import hashlib
import json
import random
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise ValueError(message)


def check(path, weights=None, expected_degree=None):
    spec = json.loads(path.read_text())
    variables = spec['witnesses']
    ports = spec['fixed_numerals']
    symbols = variables + ports
    nv = len(variables)
    weights = weights or {x:1 for x in variables}
    zero = (0,)*len(symbols)

    def const(c):
        return {zero:c} if c else {}

    def var(s):
        m=list(zero); m[symbols.index(s)]=1
        return {tuple(m):1}

    def add(a,b,sign=1):
        c=dict(a)
        for m,v in b.items():
            c[m]=c.get(m,0)+sign*v
            if not c[m]: del c[m]
        return c

    def mul(a,b):
        c={}
        for ma,va in a.items():
            for mb,vb in b.items():
                m=tuple(x+y for x,y in zip(ma,mb))
                c[m]=c.get(m,0)+va*vb
        return {m:v for m,v in c.items() if v}

    def power(a,k):
        c=const(1)
        while k:
            if k&1: c=mul(c,a)
            k//=2
            if k: a=mul(a,a)
        return c

    def deg(a):
        require(bool(a), 'A supposedly nonzero polynomial is zero')
        return max(sum(m[i]*weights[x] for i,x in enumerate(variables)) for m in a)

    def lead(a):
        d=deg(a)
        return {m:v for m,v in a.items() if sum(m[i]*weights[x] for i,x in enumerate(variables))==d}

    rowmap={}
    defined=set(symbols)
    for name,op,a,b in spec['source']:
        require(name not in defined,'Duplicate definition '+name)
        require(op in ('+','-','*'),'Bad operator')
        for arg in (a,b):
            require(isinstance(arg,int) or arg in defined,'Undefined argument '+str(arg))
        defined.add(name); rowmap[name]=(op,a,b)
    require(len(rowmap)==spec['operations'],'Incorrect operation count')
    require(nv==14,'Incorrect variable count')
    live=set()

    def mark(s):
        if isinstance(s,int) or s in live: return
        live.add(s)
        if s in rowmap:
            _,a,b=rowmap[s]; mark(a); mark(b)

    mark(spec['output'])
    require(set(rowmap)<=live,'Dead operations')
    require(set(symbols)<=live,'Dead variables or fixed coefficients')

    full={s:var(s) for s in symbols}

    def exact(s):
        if isinstance(s,int): return const(s)
        if s not in full:
            op,a,b=rowmap[s]; aa,bb=exact(a),exact(b)
            full[s]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
        return full[s]

    n1=exact('N1')
    zz=add(exact('X'),exact('gammaH'))
    n1_alt=add(add(mul(const(2),mul(mul(exact('a'),exact('c')),zz)),mul(zz,zz)),mul(exact('H'),exact('c2')),-1)
    require(n1==n1_alt,'Main-norm cancellation identity failed')
    require(deg(n1)==18*weights['J'],'Main norm degree mismatch')

    leaders={s:var(s) for s in symbols}
    degrees={s:(weights[s] if s in variables else 0) for s in symbols}

    def lp(s): return const(s) if isinstance(s,int) else leaders[s]
    def dd(s): return 0 if isinstance(s,int) else degrees[s]

    for name,op,a,b in spec['source']:
        if name=='N1':
            leaders[name]=lead(n1); degrees[name]=deg(n1); continue
        aa,bb=lp(a),lp(b)
        da,db=dd(a),dd(b)
        if op=='*':
            cc=mul(aa,bb); d=da+db
        elif da>db:
            cc=aa; d=da
        elif db>da:
            cc=bb if op=='+' else mul(const(-1),bb); d=db
        else:
            cc=add(aa,bb,1 if op=='+' else -1); d=da
        require(bool(cc),'Unaccounted leading cancellation at '+name)
        require(deg(cc)==d,'Leading degree mismatch at '+name)
        leaders[name]=cc; degrees[name]=d

    q0=mul(var('beta'),var('J'))
    k0=add(var('eta'),var('zeta'))
    b0=add(mul(var('w'),add(add(q0,var('F'),-1),var('alpha'),-1)),mul(var('z'),q0),-1)
    if spec['operations']==66: exponents=(103,16,29)
    elif spec['operations']==67: exponents=(95,12,25)
    else:
        require(spec['operations']==68,'Unexpected graph profile')
        exponents=(87,10,23)
    q_exp,w_exp,s_exp=exponents
    expected=mul(const(8),b0)
    for p,k in ((q0,q_exp),(var('gamma'),1),(var('i'),4),(k0,13),(var('w'),w_exp),(var('s'),s_exp),(var('T'),2),(var('f'),4)):
        expected=mul(expected,power(p,k))
    require(leaders[spec['output']]==expected,'Full top homogeneous component mismatch')
    require(degrees[spec['output']]==(expected_degree or spec['exact_degree']),'Incorrect reported exact degree')

    def evaluate(assignment,modulus):
        vals=dict(assignment)
        def val(x): return x if isinstance(x,int) else vals[x]
        for name,op,a,b in spec['source']:
            aa,bb=val(a),val(b)
            vals[name] = (aa*bb if op=='*' else aa+bb if op=='+' else aa-bb)%modulus
        return vals[spec['output']]

    def formula(v,mod):
        J,F,alpha,z,f,n,i,T,s,w,tau,eta,zeta,gamma=[v[x] for x in variables]
        beta,K0,MC,MF=[v[x] for x in ports]
        q=beta*J+1; C=q-F-alpha; X=w*q; Y=s*q**3
        E=X*Y; k=eta+zeta; ell=E*k*Y; c=k*Y+eta
        a=E+Y; H=4*a+3; Delta=a*a+H
        D=X+a*c+gamma*H
        R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
        V=f*f*(c*T-R)-c
        M,d=(E,E) if spec['operations']==66 else (q**4,q*q)
        u=k-M*n-R; I=d*i*c*c; S=Delta*I
        N0=tau*tau-ell*(ell+k); N1=D*D-Delta*c*c
        Na=S*S*(V*V-u*u)+u*u
        Nt=(K0+w)*C+(q-F)-z*(q-1)
        if spec['operations']==68:
            return (N0*N1*Na*Nt*(f*f-Delta*I*I)-1)%mod
        return (N0*N1*Na*Nt*(Delta*f*f-S*S)-Delta)%mod

    rng=random.Random(831745)
    for _ in range(128):
        vals={x:rng.randint(-12,12) for x in symbols}
        vals['beta']=rng.choice([31,37,101])
        mod=1000000007
        require(evaluate(vals,mod)==formula(vals,mod),'Literal graph differs from displayed formula')

    parent=(ROOT/'inherited/P66.json').read_bytes()
    require(hashlib.sha256(parent).hexdigest()==spec['parent']['sha256'],'Parent file identity mismatch')
    parent_spec=json.loads(parent)
    require(spec['coefficient_binding']['ports']==parent_spec['coefficient_binding']['ports'],'Coherent fixed coefficient tuple changed')
    binding=spec['coefficient_binding']
    for field,hashfield in [('certificate','certificate_sha256'),('ordinary_proof','ordinary_proof_sha256')]:
        retained=(path.parent/binding[field]).resolve()
        require(hashlib.sha256(retained.read_bytes()).hexdigest()==binding[hashfield],'Retained native '+field+' identity mismatch')
    coefdir=ROOT/'coefficients'
    checked_bytes=False
    if coefdir.exists():
        for name,info in spec['coefficient_binding']['ports'].items():
            b=(coefdir/info['file']).read_bytes()
            require(len(b)==info['bytes'],'Coefficient byte length mismatch')
            require(hashlib.sha256(b).hexdigest()==info['sha256'],'Coefficient byte hash mismatch')
        checked_bytes=True
    return {'name':spec['name'],'variables':nv,'operations':len(rowmap),
            'operation_counts':{x:sum(r[1]==x for r in spec['source']) for x in ('*','+','-')},
            'degree':degrees[spec['output']], 'leader_monomials':len(expected),
            'full_main_norm_monomials':len(n1), 'formula_replays':128,
            'fixed_tuple_binding_matches':True,'coefficient_bytes_checked':checked_bytes,
            'status':'PASS'}


if __name__=='__main__':
    result=[check(p) for p in sorted((ROOT/'equations').glob('*.json'))]
    print(json.dumps({'checks':result,'scope':'Exact finite algebra and binding checks; the unbounded theorem is PROOF.md.'},indent=2))
