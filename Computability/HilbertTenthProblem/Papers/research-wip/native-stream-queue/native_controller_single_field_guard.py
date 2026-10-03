"""Focused finite checks of the nonwrapping one-field period obstruction."""
import argparse
from itertools import product
import json
from pathlib import Path


def shift(word,n):
    return tuple(word[(i-n)%len(word)] for i in range(len(word)))


def polynomial(coefficients,word):
    return tuple(sum(c*word[(i-j)%len(word)] for j,c in enumerate(coefficients)) for i in range(len(word)))


def span(coefficients):
    indices=[i for i,c in enumerate(coefficients) if c]
    return max(indices)-min(indices)


def period(columns):
    N=len(columns[0])
    return next(p for p in range(1,N+1) if N%p==0 and all(shift(w,p)==w for w in columns))


def recurrence_checks():
    checked=admitted=0
    polynomials=((1,),(1,1),(1,-1),(1,0,1),(2,1))
    for N in range(1,10):
        for P in polynomials:
            D=span(P)
            for word in product((0,1),repeat=N):
                forcing=polynomial(P,word)
                p=period([forcing])
                ell=period([word,forcing])
                assert ell%p==0 and N%ell==0 and ell<=p*2**D
                checked+=1
                admitted+=ell>p
    return dict(binary_recurrences=checked,strict_period_extensions=admitted,maximum_N=9)


def layout_checks():
    R=16;L=4;B=R**L
    top=((1,),(1,1),(1,-1),(1,0,1),(1,2))
    lower=((0,),(1,),(1,-1))
    rows=[];total=admitted=0;examples=[]
    for P,K0 in product(top,lower):
        K=sum(c*B**j for j,c in enumerate(K0))+R*sum(c*B**j for j,c in enumerate(P))
        D=span(P);count=found=0;maximum_period=0
        for N in range(1,8):
            q=B**N;repunit=(q-1)//(B-1)
            words=list(product((0,1),repeat=N));zeros=(0,)*N
            for u0,u1 in product(words,repeat=2):
                columns=[u0,u1,zeros,zeros]
                U=sum((u0[i]+R*u1[i])*B**i for i in range(N))
                P0,P1=polynomial(P,u0),polynomial(P,u1)
                C0,C1=polynomial(K0,u0),polynomial(K0,u1)
                for h in range(N):
                    rotated0,rotated1=shift(u0,h),shift(u1,h)
                    values=[tuple(C0[i]+rotated0[i]-u0[i] for i in range(N)),
                            tuple(P0[i]+C1[i]+rotated1[i]-u1[i] for i in range(N)),P1,zeros]
                    lambdas=[v[0] for v in values]
                    residuals=[v-lambdas[e] for e,row in enumerate(values) for v in row]
                    assert max(abs(c) for c in residuals)<=R-2
                    lam=sum(c*R**e for e,c in enumerate(lambdas))
                    arithmetic=((K+B**h-1)*U-lam*repunit)%(q-1)==0
                    semantic=all(c==0 for c in residuals)
                    assert arithmetic==semantic
                    if arithmetic:
                        p=period(columns)
                        assert N%p==0 and p<=2**(2*D)
                        if D==0:assert p==1
                        maximum_period=max(maximum_period,p);found+=1
                        if p>1 and len(examples)<4:
                            examples.append(dict(P=list(P),K0=list(K0),N=N,h=h,u0=list(u0),u1=list(u1),
                                                 lambdas=lambdas,period=p,bound=2**(2*D)))
                    count+=1
        total+=count;admitted+=found
        rows.append(dict(P=list(P),K0=list(K0),span=D,candidates=count,admitted=found,maximum_period=maximum_period))
    return dict(radix=R,cell_length=L,allowed_inner_positions=[0,1],top_inner_shift=1,
                candidates=total,admitted=admitted,domains=rows,nonconstant_examples=examples)


def carry_boundary():
    R=4;n=5;q=R**n
    residuals=[R-1]*n
    assert sum(c*R**j for j,c in enumerate(residuals))==q-1
    assert all(c!=0 for c in residuals)
    return dict(radix=R,digits=n,residuals=residuals,
                conclusion='R-1 bounds do not justify coefficientwise recovery from a cyclic congruence')


def verify():
    return dict(status='PASS_SINGLE_FIELD_GUARD_PERIOD',recurrences=recurrence_checks(),layouts=layout_checks(),
                residual_boundary=carry_boundary(),
                scope='No within-cell wrap and actual no-carry coefficient equations only; general one-field compiler open',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps(dict(status=result['status'],recurrences=result['recurrences'],
                         candidates=result['layouts']['candidates'],admitted=result['layouts']['admitted']),indent=2))
