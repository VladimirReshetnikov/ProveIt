#!/usr/bin/env python3
"""Exact finite certificates and independent modular checks, not a consistency proof."""
from pathlib import Path
from itertools import combinations_with_replacement,product
from math import isqrt
import hashlib,json,random,sys
ROOT=Path(__file__).resolve().parent
sys.path.append(str(ROOT.parent/'sun/sources'))
import verify_signed10 as source
from build_nine_b4 import construct,degree_certificate,KAPPA,INDEX_EXPONENT
from circuit import evaluate


def literal(v,fixed,constants,weights,p):
    red=lambda x:x%p
    pp=lambda x,e:pow(x,e,p)
    t=max(weights);b=red(2+v['epsilon']);B=red(fixed['base_scale']*pp(b,4))
    g,h,s,w,i,j=(red(v[n+'0']+1) for n in ('g','h','s','w','i','j'))
    ell=sum(pp(B,x) for x in weights)%p;top=pp(B,t);q=pp(B,4*t)
    dc=sum(fixed[row['name']]*pp(B,4*t-sum(a*x for a,x in zip(row['alpha'][1:],weights))) for row in constants['coefficient_records'])%p
    N0=pp(B,t+1);N1=red(2*pp(B,8*t+1));N=red(N0*N1)
    mc=red(N0-1-(b-1)*ell);tc=red(mc+(B-2)*q*N0)
    jc=red(2*pp(1+g,4)*dc+B*source.geometric(B,8*t+1,p));sc=red(g+jc*N0)
    R=red(sc*(N*N-N)+(tc+1)*(N*N-1));cap=red(32*b*top)
    U=red(N*N*w);Y=red(N*N*s);M=red(R*Y);P=red(2*M*M*U)
    K=red(R+1+h*(P-1));A=red(M*(U+1));B1=red(2*R+1);W1=red(b*w)
    C=red(B1+W1+v['phi']);J=red(4*A-5);Q=red(3*W1*C-2*(W1*W1-1))
    D=red((A*A-1)*C*C+1);E=red(i*J*D*C*C);F=red((A*A-1)*E*E+1)
    G=red(A+F*(C*D+1-A));H=red(B1+j*C);I=red((G*G-1)*H*H+1)
    a0=red((P*P-1)*K*K+1);a1=red(64*D*F*I)
    margin=red(K*K*cap-4*(C-K*Y)**2*cap-8*g*K*K)
    u=red(J*F);vv=red(Q*F+J*(H-C));V0=red(P*K)
    nt=red(i*J*C);ap=red(nt*(8*D*D-4*D-1));GH=red(G*H);rc=red(ap*GH);V1=rc
    md=red(Q+H-C);om=red(u*(2*margin-1));e0=red(u*v['n']+vv-om*md);th=red(e0-om*V0*V1)
    inn=red(th*th-om*om*(a0+V0*V0*a1));answer=red(inn*inn-4*pp(om,4)*V0*V0*a0*a1)
    return answer,dict(b=b,base=B,ell=ell,top=top,qcode=q,Dcode=dc,N0=N0,N1=N1,N=N,Mcode=mc,Tcode=tc,Jcode=jc,Scode=sc,R=R,Gcap=cap,omega=w,U=U,Y=Y,M=M,P=P,K=K,A=A,B1=B1,W1=W1,C=C,J=J,Q=Q,D=D,E=E,F=F,G=G,H=H,I=I,a0=a0,a1=a1,margin=margin,u=u,v=vv,V0=V0,norm_t=nt,approx=ap,GH=GH,rootcap=rc,V1=V1,Mdiv=md,Omega=om,E0=e0,Theta=th,inner=inn,nine_b4=answer)


def norm_value(a0,a1,u,v,m,V0,V1,M,n):
    om=u*(2*m-1);th=u*n+v-om*(M+V0*V1)
    return (th*th-om*om*(a0+V0*V0*a1))**2-4*om**4*V0*V0*a0*a1


def exact_algebra_checks():
    # Expand in formal D and t: [t(8D²−4D−1)]²−64[t²D³(D−1)+D].
    mul=source.sparse_mul;add=source.sparse_add;scale=source.sparse_scale
    ap={(2,1):8,(1,1):-4,(0,1):-1}
    df={(4,2):1,(3,2):-1,(1,0):1}
    lhs=add(mul(ap,ap),scale(df,-64))
    assert lhs=={(1,2):8,(0,2):1,(1,0):-64}
    # Formal norm product in X,r0,r1, with weight folded into r1.
    poly={(0,0,0):1}
    for eps,delta in product((-1,1),repeat=2):
        poly=mul(poly,{(1,0,0):1,(0,1,0):eps,(0,0,1):delta})
    assert poly=={(4,0,0):1,(2,2,0):-2,(2,0,2):-2,(0,4,0):1,(0,2,2):-2,(0,0,4):1}
    return {'DF_approximation_exact_expansion':True,'four_factor_norm_exact_expansion':True}


def bounded_checks(rng):
    for rep in range(400):
        R,N,b,g,h,s,w,i,j=(rng.randrange(1,9) for _ in range(9));phi=rng.randrange(9)
        U=N*N*w;Y=N*N*s;M=R*Y;P=2*M*M*U;K=R+1+h*(P-1);A=M*(U+1)
        B1=2*R+1;W=b*w;C=B1+W+phi;J=4*A-5;Q=3*W*C-2*(W*W-1)
        D=(A*A-1)*C*C+1;E=i*J*D*C*C;F=(A*A-1)*E*E+1;G=A+F*(C*D+1-A)
        H=B1+j*C;I=(G*G-1)*H*H+1;t=i*J*C;ap=t*(8*D*D-4*D-1);V1=ap*G*H
        u=J*F;v=Q*F+J*(H-C);md=Q+H-C
        assert min(A,C,J,D,E,F,G,H,I,Q,H-C,u,v,md)>0
        assert ap*ap-64*D*F==t*t*(8*D+1)-64*D>0
        assert V1**2>64*D*F*I and v<=u*md
    # Both directions of the positive-divisor finalizer over a bounded model.
    count=0
    for rep in range(600):
        a0,a1=(rng.randrange(-4,26) for _ in range(2));u=rng.randrange(1,8);v=rng.randrange(1,30);m=rng.randrange(-3,5)
        V0=max(2,isqrt(abs(a0))+1);V1=max(2,isqrt(abs(a1))+1);md=v
        square=lambda a:a>=0 and isqrt(a)**2==a
        conditions=square(a0) and square(a1) and v%u==0 and m>0
        if conditions:
            for e,d in product((-1,1),repeat=2):
                n=(2*m-1)*(md+V0*V1+e*isqrt(a0)+d*V0*isqrt(a1))-v//u
                assert n>=1 and norm_value(a0,a1,u,v,m,V0,V1,md,n)==0
        for n in range(31):
            if norm_value(a0,a1,u,v,m,V0,V1,md,n)==0:assert conditions
            count+=1
    return {'positive_majorant_assignments':400,'finalizer_fixture_count':600,'finalizer_nonnegative_n_checks':count}


def run():
    rng=random.Random(202610231631)
    constants,coeff_report=source.source_coefficients();ports,port_report=source.fixed_ports(constants)
    assert KAPPA==INDEX_EXPONENT+22 and KAPPA%2==1
    assert 2*32**4 < 2**22 and 2048<2**22
    body,_=construct();pc,_=construct(True);certbody,_=construct(False,True);pcertbody,_=construct(True,True)
    weights=body['witness_weights'];positions=[0]+weights;seen=set()
    for ix in combinations_with_replacement(range(32),4):
        ss=sum(positions[i] for i in ix);assert ss not in seen;seen.add(ss)
    assert len(seen)==52360
    checks=0
    for prime in (101,1009,1000003):
        fixed=source.fixed_leaves(constants,ports,prime);fixed['base_scale']=pow(2,KAPPA,prime);fixed['base_scale_minus_one']=(fixed['base_scale']-1)%prime
        for rep in range(80):
            # Include negative values in polynomial-identity tests, not semantics.
            vv={name:rng.randrange(-30,31) for name in body['variables']}
            ans,named=evaluate(body,fixed,vv,prime);lit,lnamed=literal(vv,fixed,constants,weights,prime)
            assert ans==lit
            for name,val in lnamed.items():assert named[name]==val;checks+=1
            certans,cn=evaluate(certbody,fixed,vv,prime);assert ans==certans
            assert cn['deltaV']==(named['V1']**2-named['a1'])%prime
            plus={nn:vv[n]+1 for nn,n in zip(pc['variables'],body['variables'])}
            pa,pn=evaluate(pc,fixed,plus,prime);pca,pcn=evaluate(pcertbody,fixed,plus,prime)
            assert ans==pa==pca
    degrees=degree_certificate(certbody);pdegrees=degree_certificate(pcertbody)
    assert degrees['exact_degree']==pdegrees['exact_degree']==38176*body['t']+8744
    assert degrees['diagonal_leading_coefficient']==pdegrees['diagonal_leading_coefficient']=={'scalar':2**1046,'base_scale_power':9544*body['t']+2120}
    report={'status':'PASS','exact_degree':degrees['exact_degree'],'degree_formula':'38176*t+8744; t=610895',
      'diagonal_leading_coefficient':'2^1046 * base_scale^(9544*t+2120)','natural_operations':body['operation_counts'],'natural_total_operations':sum(body['operation_counts'].values()),
      'positive_operations':pc['operation_counts'],'positive_total_operations':sum(pc['operation_counts'].values()),
      'fixed_coefficient_reconstruction':coeff_report,'fixed_port_verification':port_report,
      'B4_distinct_four_multisets':len(seen),'base_scale_exponent':KAPPA,'base_scale_bound_verified':True,
      'literal_modular_assignments':240,'named_value_comparisons':checks,'positive_translation_and_telescoping':True,
      'exact_identities':exact_algebra_checks(),'bounded_regressions':bounded_checks(rng),
      'scope':'Finite certificate and circuit checks. Universal equivalence follows the ordinary proof and imported compiler/ratio theorems, not these tests.'}
    (ROOT/'generated/VALIDATION.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2));return report
if __name__=='__main__':run()
