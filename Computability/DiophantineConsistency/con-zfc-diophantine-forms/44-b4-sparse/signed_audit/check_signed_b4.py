#!/usr/bin/env python3
"""Independent direct formulas and finite arithmetic tests; not kernel verification."""
from pathlib import Path
from itertools import product,combinations_with_replacement
from math import factorial
import json,random,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'sun/sources'))
import verify_signed10 as source
from circuit import evaluate
from build_signed_b4 import construct,degree_certificate,KAPPA

def literal(v,fixed,constants,weights,p,norm,count=14):
    r=lambda x:x%p
    t=max(weights);L=4*t
    b=r(2*v['epsilon']**2);B=r(fixed['base_scale']*pow(b,4,p))
    ell=sum(pow(B,w,p) for w in weights)%p
    Dcode=sum(fixed[row['name']]*pow(B,L-sum(a*w for a,w in zip(row['alpha'][1:],weights)),p) for row in constants['coefficient_records'])%p
    N0=pow(B,t+1,p);N1=r(2*pow(B,8*t+1,p));N=r(N0*N1)
    Mcode=r(N0-1-(b-1)*ell)
    Tcode=r(Mcode+(B-2)*pow(B,L,p)*N0)
    Jcode=r(2*pow(1+v['g'],4,p)*Dcode+B*source.geometric(B,8*t+1,p))
    Scode=r(v['g']+Jcode*N0)
    R=r(Scode*(N*N-N)+(Tcode+1)*(N*N-1));Gcap=r(32*b*pow(B,t,p))
    omega=r(v['w']**2);U=r(N*N*omega);Y=r(N*N*v['s']);MM=r(R*Y)
    P=r(2*MM*MM*U);K=r(R+1+v['h']*(P-1));A=r(MM*(U+1))
    B1=r(2*R+1);W1=r(b*omega);C=r(B1+W1+v['phi']);J=r(4*A-5)
    Q=r(3*W1*C-2*(W1*W1-1));D=r((A*A-1)*C*C+1);E=r(v['i']*J*D*C*C)
    F=r((A*A-1)*E*E+1);G=r(A+F*(C*D+1-A));H=r(B1+v['j']*C)
    I=r((G*G-1)*H*H+1);a0=r((P*P-1)*K*K+1);a1=r(D*F*I)
    margin=r(K*K*Gcap-4*(C-K*Y)**2*Gcap-8*v['g']*K*K)
    cap=r(b*pow(B,t,p));merged=r(v['g']*(cap-v['g'])*K*K-cap*cap*(C-K*Y)**2)
    discriminants=[3*v['g']-1,3*v['s']-1,3*v['phi']+2,3*margin-1] if count==14 else [3*v['s']-1,3*v['phi']+2,3*merged-1]
    stack=1
    for k,disc in enumerate(discriminants,1):
        stack=r(stack*(1+4*disc*stack*v['z'+str(k)]**2))
    Ddiv=r(J*F);Tdiv=r(Q*F+J*(H-C))
    Z=r(v['epsilon']*v['w']*v['i']*v['z1']*v['z2']*v['z3']*(v['z4'] if count==14 else 1))
    denom=r(Z*pow(Ddiv,5,p));rr=r(Tdiv+Ddiv*v['residue'])
    target=r((rr**3-Ddiv**2*rr-Ddiv**3)*(rr**2+23*Ddiv**2))
    w1=stack;w2=r(stack*(P*P+K*K+2));center=r(denom*v['normroot']-target)
    ai=[r(denom**2*stack),r(denom**2*w1**2*a0),r(denom**2*w2**2*a1)]
    output=source.evaluate_norm(norm,[center]+ai,p)
    named=dict(b=b,base=B,ell=ell,Dcode=Dcode,N0=N0,N1=N1,N=N,Mcode=Mcode,Tcode=Tcode,Jcode=Jcode,Scode=Scode,R=R,Gcap=Gcap,omega=omega,U=U,Y=Y,M=MM,P=P,K=K,A=A,B1=B1,W1=W1,C=C,J=J,Q=Q,D=D,E=E,F=F,G=G,H=H,I=I,a0=a0,a1=a1,margin=margin,Cguard=stack,Ddiv=Ddiv,Tdiv=Tdiv,Znonzero=Z,Smerge=denom,Tmerge=target,weight1=w1,weight2=w2,Xnorm=center,signed14_b4=output)
    if count==13:
        for name in ['Gcap','margin','signed14_b4']:named.pop(name,None)
        named.update(cap=cap,Delta=merged,signed13_b4=output)
    return output,named

def toy_checks():
    # Exact coefficient extraction, shifted binary carry, and central binomial
    # coding on P=(x-1)^2+(y-2)^2; large integers are evaluated, not sampled mod p.
    weights=[1,5];t=5;L=20;m=41
    coeff={(0,0):5,(1,0):-2,(0,1):-4,(2,0):1,(0,2):1}
    cs={ex:co*factorial(4-sum(ex))*factorial(ex[0])*factorial(ex[1]) for ex,co in coeff.items()}
    z=256;a=2**21;b=8;B=a*b**4
    assert a>max(2*z*3**4,2048*z)
    Dcode=sum(co*B**(L-sum(a*w for a,w in zip(ex,weights))) for ex,co in cs.items())
    N0=B**(t+1);N1=2*B**m;N=N0*N1
    mask=N0-1-(b-1)*sum(B**w for w in weights)
    offset=B*sum(B**j for j in range(m));Tcarry=(B-2)*B**L
    count=0
    for x,y in product(range(4),repeat=2):
        g=x*B+y*B**5
        Jcarry=2*(1+g)**4*Dcode+offset
        assert Jcarry>0 and Jcarry<2*B**m
        assert (g&mask)==0
        assert ((Jcarry&Tcarry)==0)==((x-1)**2+(y-2)**2==0)
        S=g+N0*Jcarry;T=mask+N0*Tcarry
        R=S*(N*N-N)+(T+1)*(N*N-1)
        assert 0<=S<N and 0<=T<N
        assert ((S&T)==0)==(R.bit_count()>=2*(N.bit_length()-1))
        assert R%N0==(b-1)*sum(B**w for w in weights)
        count+=1
    rng=random.Random(610895)
    for bits in range(1,25):
        N=2**bits
        for _ in range(70):
            S=rng.randrange(N);T=rng.randrange(N)
            R=S*(N*N-N)+(T+1)*(N*N-1)
            assert ((S&T)==0)==(R.bit_count()>=2*bits)
    bound_cases=0
    for b in (2,3,4,8):
        B=a*b**4; cap=b*B**t;N0=B**(t+1);N=2*B**(9*t+2)
        ell=sum(B**w for w in weights)
        Dcode=sum(co*B**(L-sum(x*w for x,w in zip(ex,weights))) for ex,co in cs.items())
        mask=N0-1-(b-1)*ell
        Tcarry=(B-2)*B**L;T=mask+N0*Tcarry
        offset=B*sum(B**j for j in range(m))
        assert B>4*b and Dcode>0 and 0<=mask<N0
        for g in (1,cap-1,cap,4*cap-1):
            Jcarry=2*(1+g)**4*Dcode+offset;S=g+N0*Jcarry
            R=S*(N*N-N)+(T+1)*(N*N-1)
            assert 0<Jcarry<2*B**m and 0<=S<N and 0<=T<N
            assert 8<=N<=R and b<=N and cap*b<=N*N
            bound_cases+=1
        for g in (-4*cap,-1,0,4*cap,100*cap):
            Jcarry=2*(1+g)**4*Dcode+offset;S=g+N0*Jcarry
            R=S*(N*N-N)+(T+1)*(N*N-1)
            assert R%N0==(b-1)*ell and R!=0
            bound_cases+=1
    return {'exact_toy_code_cases':count,'central_binomial_binary_cases':24*70,
      'quartic_radix_signed_bound_cases':bound_cases}

def merged_guard_checks():
    # Exact symbolic four-variable identity, independent of circuit evaluation.
    basis=[]
    for k in range(4):
        ex=[0]*4;ex[k]=1;basis.append({tuple(ex):1})
    c,g,K,dd=basis
    add=source.sparse_add;mul=source.sparse_mul
    scale=source.sparse_scale
    sub=lambda a,b:add(a,scale(b,-1))
    sq=lambda a:mul(a,a)
    delta=sub(mul(mul(g,sub(c,g)),sq(K)),mul(sq(c),sq(dd)))
    lhs=mul(sq(c),sub(sq(K),scale(sq(dd),4)))
    rhs=add(scale(delta,4),mul(sq(sub(c,scale(g,2))),sq(K)))
    assert sub(lhs,rhs)=={}
    finite=0
    for c0 in range(1,13):
        for g0 in range(-5,19):
            for k0 in range(-6,7):
                for d0 in range(-8,9):
                    de=g0*(c0-g0)*k0*k0-c0*c0*d0*d0
                    if de>0:assert 0<g0<c0 and 4*d0*d0<k0*k0
                    finite+=1
    def psi(a,n):
        x,y=0,1
        for _ in range(n):x,y=y,2*a*y-x
        return x
    actual=0
    for R in (8,9,10,12):
        for N in (8,16,32):
            for b in (2,4,8):
                U=N*N*2**(2*R+1)//b
                Y=(U+1)**(2*R)//U**R
                M=R*Y;A=M*(U+1);P=2*M*M*U
                K=psi(P,R+1);C=psi(A,2*R+1)
                error=abs(C-K*Y)
                assert error*N*N < K*b
                for cap in (2,3,7,N):
                    for g in (1,cap//2,cap-1):
                        assert g*(cap-g)*K*K-cap*cap*error*error>0
                actual+=1
    return {'exact_interval_identity':True,'finite_signed_implication_cases':finite,
      'exact_canonical_ratio_bound_cases':actual,
      'note':'Canonical bound tested without requiring the separate central-binomial divisibility; universal proof supplies that condition.'}

def run(count=14):
    constants,coefficient_report=source.source_coefficients()
    ports,fixed_report=source.fixed_ports(constants)
    (source.ROOT/'generated').mkdir(exist_ok=True)
    norm,norm_report=source.norm_polynomial(3)
    body,aliases=construct(count)
    base=ROOT/'generated'
    actual=json.loads((base/f'signed{count}_b4.json').read_text())
    assert actual==dict(body,exact_degree=degree_certificate(body)['exact_degree'])
    assert (base/body['fixed_binding']).resolve().is_file()
    assert (base/body['fixed_recipes']['source_coefficients']).resolve().is_file()
    for proof in body['proof']:assert (base/proof).resolve().is_file()
    binding=json.loads((base/body['fixed_binding']).read_text())
    assert json.loads((base/body['fixed_recipes']['source_coefficients']).read_text())==constants
    assert body['fixed_recipes']['base_scale']==f'2^{KAPPA}'
    seen=set();ws=[0]+body['witness_weights']
    for ix in combinations_with_replacement(range(32),4):
        value=sum(ws[k] for k in ix)
        assert value not in seen
        seen.add(value)
    assert len(seen)==52360
    rng=random.Random(20261023610895);compared=0;degrees=[]
    for p in (101,1009,1000003):
        fixed=source.fixed_leaves(constants,ports,p);fixed['base_scale']=pow(2,KAPPA,p)
        degrees.append(degree_certificate(body,p))
        for _ in range(50):
            v={name:rng.randrange(-15,16) for name in body['variables']}
            got,gn=evaluate(body,fixed,v,p)
            expected,en=literal(v,fixed,constants,body['witness_weights'],p,norm,count)
            assert got==expected
            for name,value in en.items():
                assert gn[name]==value,(p,name,gn[name],value)
                compared+=1
    report={'status':'PASS','unknowns':count,'operations':sum(body['operation_counts'].values()),
      'operation_counts':body['operation_counts'],'exact_degree':degrees[0]['exact_degree'],
      'B4_checked_multisets':len(seen),'source_coefficient_reconstruction':coefficient_report,
      'source_fixed_ports':fixed_report,'norm_identity':norm_report,'degree_certificates':degrees,
      'literal_modular_assignments':150,'named_value_comparisons':compared,'toy_carry_checks':toy_checks(),'merged_guard_checks':merged_guard_checks(),
      'scope':'Finite exact/modular checks accompany the universal proofs; no end-to-end Lean rebuild and no consistency computation.'}
    (ROOT/f'SIGNED{count}_B4_CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ['degree_certificates','source_fixed_ports']},indent=2))
if __name__=='__main__':
    for count in (13,14):run(count)
