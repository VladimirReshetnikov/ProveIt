"""Finite elementary audits for the triangular nonabsorbing theorem."""
import argparse
from itertools import product
import json
from math import gcd
from pathlib import Path
import pell_kernel_nonabsorbing_determinant as independent


def threshold(a,c,N):
    return c*max(a,c-a)//gcd(a,c)+3*c+abs(N)+3


def triangular_coin(a,c,target,upper):
    if target<0:return None
    for u in range(min(upper,target//a)+1):
        remaining=target-a*u
        if remaining%c==0 and u+remaining//c<=upper:
            return u,remaining//c
    return None


def classification(a,c,M,N,L):
    assert 0<a<c and L>=threshold(a,c,N)
    if M<0 or M>c:return False
    if M==0:return independent.coin_member(a,c,N)
    if M==c:return independent.coin_member(c-a,c,-3*c-N)
    return (M*L+N)%gcd(a,c)==0


def saturation_audit():
    cases=admitted=endpoints=0
    for a in range(1,9):
        for c in range(a+1,10):
            for M in range(-1,c+2):
                for N in range(-3*c-4,9):
                    for extra in (0,2):
                        L=threshold(a,c,N)+extra
                        exact=triangular_coin(a,c,M*L+N,L-3) is not None
                        assert exact==classification(a,c,M,N,L),(a,c,M,N,L)
                        cases+=1;admitted+=exact;endpoints+=M in (0,c)
    return dict(cases=cases,admitted=admitted,endpoint_cases=endpoints,
                maximum_large_coefficient=9)


def sorted_coefficients(a0,b0):
    weights=[0,a0,b0];assert len(set(weights))==3
    sigma=sorted(range(3),key=lambda j:weights[j])
    m0=weights[sigma[0]]
    a=weights[sigma[1]]-m0;c=weights[sigma[2]]-m0
    assert 0<a<c and gcd(a,c)==gcd(a0,b0)
    return sigma,m0,a,c


def sorted_vertex_audit():
    cases=0;orders=set()
    for a0,b0 in product(range(-5,6),repeat=2):
        if len({0,a0,b0})!=3:continue
        sigma,m0,a,c=sorted_coefficients(a0,b0);orders.add(tuple(sigma))
        for L in range(3,10):
            U=L-3;image=set()
            for A in range(1,L):
                for B in range(1,L-A):
                    x=[U-(A-1)-(B-1),A-1,B-1]
                    assert min(x)>=0 and sum(x)==U
                    u,v=x[sigma[1]],x[sigma[2]]
                    assert u>=0 and v>=0 and u+v<=U
                    assert a0*(A-1)+b0*(B-1)==m0*U+a*u+c*v
                    back=[0]*3
                    back[sigma[0]]=U-u-v;back[sigma[1]]=u;back[sigma[2]]=v
                    assert (1+back[1],1+back[2])==(A,B)
                    image.add((u,v));cases+=1
            assert image=={(u,v) for u in range(U+1) for v in range(U-u+1)}
    assert len(orders)==6
    return dict(bijection_cases=cases,all_six_vertex_orders=True)


def duration_audit():
    cases=replacements=0
    models=((1,0,0,2,-1,0,-3),(1,2,-1,1,1,-2,5),
            (-1,1,2,3,-2,1,-4),(0,2,-1,1,0,3,0),
            (2,-3,1,-2,1,0,7),(1,1,0,17,-1,0,-3))
    for radix in (2,3):
        for al,be,ga,de,ep,ze,eta in models:
            D=abs(al*de-be*ga);assert D
            S=1+sum(map(abs,(al,be,ga,de,ep,ze,eta)));K=S*S+8*S+3
            for m in range(1,5):
                W=radix**m;a0=al*W+be;b0=ga*W+de
                if len({0,a0,b0})!=3:continue
                sigma,m0,a,c=sorted_coefficients(a0,b0);d=gcd(a,c)
                assert D%d==0
                M=-ep*W-m0;N=-ze*W-eta-a0-b0+3*m0
                assert c<=S*(W+1) and abs(N)<=5*S*(W+1)
                B0=threshold(a,c,N);assert B0<=K*(W+1)**2
                n0=0
                while radix**n0<B0:n0+=1
                seq,mu,p=independent.orbit(radix,d)
                assert mu+p<=d<=D
                assert set(seq[mu:])<={pow(radix,j,d) for j in range(n0,n0+D)}
                for n in range(1,n0+D+8):
                    L=radix**n
                    accepted=(triangular_coin(a,c,M*L+N,L-3) is not None
                              if L<B0 else classification(a,c,M,N,L))
                    cases+=1
                    if not accepted:continue
                    if L<B0 or n<D:short=L
                    else:
                        ns=[j for j in range(n0,n0+D)
                            if classification(a,c,M,N,radix**j)]
                        assert ns
                        short=radix**ns[0]
                    assert short<=radix**(D+1)*K*(W+1)**2
                    replacements+=short!=L
    return dict(power_cases=cases,actual_duration_replacements=replacements,
                coefficient_models=len(models),radices=[2,3])


def slack_carry_audit():
    cases=zero_slacks=0
    for W in range(2,7):
        for k in range(4):
            for V in ((1,) if k==3 else range(1,W)):
                L=W**k*V
                if L<3:continue
                As=sorted({1,max(1,(L-1)//3),L-2})
                for A in As:
                    Bs=sorted({1,max(1,(L-1-A)//2),L-1-A})
                    for B in Bs:
                        Z=L-1-A-B
                        assert A>0 and B>0 and Z>=0
                        rows=[independent.base_digits(x,W,k+1)+[0]*(3-k) for x in (A,B,Z)]
                        assert all(row[k]<V for row in rows)
                        H=[sum(row[j] for row in rows)+(j==0)-(V if j==k else 0) for j in range(4)]+[0]
                        assert sum(h*W**j for j,h in enumerate(H))==0
                        assert all(abs(h)<=5*W for h in H)
                        carry=0
                        for h in H:
                            assert (h+carry)%W==0
                            carry=(h+carry)//W
                            assert abs(carry)<=10
                        assert carry==0
                        cases+=1;zero_slacks+=Z==0
    return dict(exact_bounded_slack_paths=cases,zero_slack_examples=zero_slacks)


def verify():
    return dict(status='PASS_NONABSORBING_JOINT_NONZERO_DETERMINANT_COMPONENTS',
                saturation=saturation_audit(),sorted_vertices=sorted_vertex_audit(),
                duration=duration_audit(),slack_carries=slack_carry_audit(),
                scope='Joint append bound with nonzero coefficient determinant; general Presburger elimination is not implemented',
                determinant_zero='GENERAL_CASE_UNRESOLVED',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(result,indent=2))
