#!/usr/bin/env python3
"""Portable checks of the delivered finite specifications.

The unbounded semantic theorem and global degree proofs are in report.pdf.
Finite tests never assert that a consistency polynomial has no zeros.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib, importlib.util, json, random, subprocess, sys

ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True

def need(ok,message):
    if not ok: raise ValueError(message)

def load(path):return json.loads(path.read_text())
def module(path,name):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def evaluate(rows,inputs,p):
    env=dict(inputs)
    for n,op,a,b in rows:
        a=env[a] if isinstance(a,str) else a;b=env[b] if isinstance(b,str) else b
        env[n]=(a+b if op=='+' else a-b if op=='-' else a*b)%p
    return env

def reference(inputs,p,direct=False,both=False,saturated=False,sharp=False):
    # Direct transcription of the manuscript, independent of the row producer.
    J,F,alpha,i,T,Y,n,eta,zeta=[inputs[x] for x in ['J','F','alpha','i','T','Y','n','eta','zeta']]
    beta,K,MC,MF=[inputs[x] for x in ['beta','K0','MC','MF']]
    q=(beta*J+1)%p;k=(eta+zeta)%p;c=(k*Y+eta)%p;mu=(q*q+1)%p
    X=(q+inputs['x'] if direct else inputs['w']*q)%p
    a=(mu*Y*(X+1))%p;Cf=((a+2)*i*c*c)%p;I=(i*c*c)%p
    V0=X*(mu*Y)**2%p;Ct=(V0+1)*k%p;Dtau=(V0*(V0+1)*k*k+1)%p
    if saturated:
        Delta=a*(a+2)%p;Df=(1+Delta*I*I*Dtau)%p;Q=Delta*Delta*I*I*Dtau%p
        Cf=((a+(1 if sharp else 2))*I*Dtau)%p
    else:
        S=(a*Cf)%p;Df=(S*I+1)%p;Q=S*S%p
    delta=(Q-1)%p
    R=(((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J)%p
    b=(c*(T+alpha)-R)%p;V=(Df*b-c)%p;Dnum=(Q*V*V-1)%p
    C=(q-F-alpha)%p;H=(4*a-1)%p;Kpos=(X*(3*c-2*X)+2)%p;e=(k-R-1)%p
    L=k*(T+alpha)%p;Bt=(((q*K+X)*C-q*F) if direct else ((K+inputs['w'])*C-F))%p
    P1=pow(q,4 if direct else 3,p)*(q-1)%p;M=P1*mu*mu*H%p
    center=(n+V+Cf+(3*Ct if both else 0)-L*Bt)%p
    low=((q*(q-1)*Y-(q-1)*X) if direct else (q-1)*Y)%p
    Z=(P1*mu*mu*(H*center+Kpos)+H*(mu*mu*(low-q**3*Bt)-P1*e))%p
    fs=delta*Z*Z%p;fa=9*delta*M*M*Dtau%p;fb=delta*M*M*Df%p;fc=M*M*Dnum%p
    if saturated:
        fg=delta*M*M*Dtau*Df%p
        return ((fs-fg-fc)**2-4*fg*fc)%p
    return (((fs+fc-fa-fb)**2-4*(fs*fc+fa*fb))**2-64*fs*fc*fa*fb)%p

# Sparse exact polynomial arithmetic for a four-indeterminate norm identity.
def add(a,b,sign=1):
    d=dict(a)
    for e,c in b.items():
        d[e]=d.get(e,0)+sign*c
        if d[e]==0:del d[e]
    return d
def mul(a,b):
    d={}
    for e,c in a.items():
        for f,v in b.items():
            g=tuple(x+y for x,y in zip(e,f));d[g]=d.get(g,0)+c*v
    return {e:c for e,c in d.items() if c}
def scale(a,c):return {e:c*v for e,v in a.items() if c*v}
def square(a):return mul(a,a)
def exact_norm():
    one={(0,0,0,0):1};z,a,b,c=[{tuple(int(i==j) for i in range(4)):1} for j in range(4)]
    product_poly=one
    for sa,sb,sc in product([-1,1],repeat=3):
        factor=add(add(add(z,scale(a,sa)),scale(b,sb)),scale(c,sc))
        product_poly=mul(product_poly,factor)
    s,aa,bb,cc=[square(t) for t in [z,a,b,c]]
    P=add(add(add(s,cc),aa,-1),bb,-1)
    u=mul(s,cc);v=mul(aa,bb)
    E=add(square(P),scale(add(u,v),4),-1)
    formula=add(square(E),scale(mul(u,v),64),-1)
    need(formula==product_poly,'all coefficients of universal eight-factor norm')
    # Full central identities used to share the strong ordinate.
    A=z;I=a;cf=mul(add(A,one),I);S=mul(add(A,one,-1),cf)
    delta=add(square(A),one,-1)
    need(S==mul(delta,I),'S=(A-1)(A+1)I')
    need(mul(S,I)==mul(delta,square(I)),'Df prefix sharing')
    need(square(S)==mul(square(delta),square(I)),'Q prefix sharing')
    two=one
    for sa,sb in product([-1,1],repeat=2):two=mul(two,add(add(z,scale(a,sa)),scale(b,sb)))
    gap=add(add(square(z),square(a),-1),square(b),-1)
    formula2=add(square(gap),scale(mul(square(a),square(b)),4),-1)
    need(two==formula2,'complete two-root norm identity')
    # Q=E*t and Df=1+E*d: the difference of squared radicals cannot
    # vanish, since its integer numerator is -1 modulo E>1.
    E,t,d,V=z,a,b,c;Q=mul(E,t);Df=add(one,mul(E,d));de=add(Q,one,-1)
    numerator=add(add(mul(Q,square(V)),one,-1),mul(mul(de,E),Df),-1)
    identity=add(mul(E,add(mul(t,square(V)),mul(de,Df),-1)),one,-1)
    need(numerator==identity,'anti-cancellation identity modulo E')
    return {'three_root_norm_terms':len(formula),'two_root_norm_terms':len(formula2),'free_ring_identities':6}

def topology(data):
    known=set(data['witnesses']+data['fixed_numerals']);deps={}
    for name,op,a,b in data['source']:
        need(name not in known and op in ['+','-','*'],'acyclic unique arithmetic gate')
        need(all(type(t)is int or t in known for t in [a,b]),'defined operand')
        known.add(name);deps[name]=[a,b]
    live=set();todo=[data['output']]
    while todo:
        name=todo.pop()
        if not isinstance(name,str) or name in live:continue
        live.add(name);todo.extend(deps.get(name,[]))
    need(live==known,'every port, input, and gate is live')
    need(len(deps)==data['operations'],'complete operation count')
    need(dict(Counter(r[1] for r in data['source']))==data['operation_breakdown'],'binary operation census')

def main():
    recipe=module(ROOT/'coefficients/recipe_compact44.py','coefficient_recipe')
    coefficients=recipe.verify();actual=recipe.recipe();summary={'status':'PASS','optimized_python':bool(sys.flags.optimize),'coefficient_reconstruction':coefficients,'exact_identities':exact_norm()}
    rng=random.Random(20261024);out=[]
    for name,expected_ops,degree in [('strong_center',98,358),('both_centers',100,354),('direct_strong_center',104,330),('direct_both_centers',106,327),('saturated_upper',92,283),('saturated_sharp',93,278),('direct_saturated_upper',98,258),('direct_saturated_sharp',99,254)]:
        d=load(ROOT/'equations'/f'{name}.json');topology(d)
        need(d['operations']==expected_ops and d['exact_degree']==degree,'pinned circuit metrics')
        direct=name.startswith('direct_');both='both_centers' in name
        for j in range(72):
            p=[1000000007,1000000009,998244353][j%3]
            ports={k:v%p for k,v in actual.items()} if j<36 else {k:rng.randrange(p) for k in actual}
            inp={v:rng.randrange(-11,12) for v in d['witnesses']}|ports
            got=evaluate(d['source'],inp,p)['N'];want=reference(inp,p,direct,both,'saturated' in name,'sharp' in name)
            need(got==want,'complete independently transcribed polynomial: '+name)
        out.append({'name':name,'operations':expected_ops,'degree':degree,'whole_formula_modular_controls':72})
    # A finite diagnostic for the proved domination premise, including its
    # earliest possible k, with all inequalities compared exactly.
    dominance=0
    for V0 in range(1,65):
        for offset in range(8):
            k=8*V0+4+offset;c=k+1;I=c*c
            need(9*(V0*(V0+1)*k*k+1)<I*I,'3 tau < I exact-square diagnostic')
            dominance+=1
    summary.update(circuits=out,dominance_controls=dominance,
                   scope='Finite specification checks. Unbounded equivalence and exact global degree are established by the ordinary proofs, not by sampling.')
    ray=subprocess.run([sys.executable,str(ROOT/'checks/verify_all_degree_rays.py'),str(ROOT/'equations')],text=True,capture_output=True)
    need(ray.returncode==0,'independent exact degree-ray check: '+ray.stderr)
    summary['exact_degree_rays']=json.loads(ray.stdout)
    satray=subprocess.run([sys.executable,str(ROOT/'checks/verify_saturated_degree_rays.py'),str(ROOT/'equations')],text=True,capture_output=True)
    need(satray.returncode==0,'independent saturated exact degree-ray check: '+satray.stderr)
    summary['saturated_exact_degree_rays']=json.loads(satray.stdout)
    bindings=module(ROOT/'checks/verify_saturated_bindings.py','independent_saturated_bindings')
    summary['exact_saturated_formula_bindings']=bindings.run()
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
