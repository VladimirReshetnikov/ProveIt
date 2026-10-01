"""Standard-library exact checks of the left flag and grouped zero-row identities."""
from itertools import permutations
from pathlib import Path
import json
from verify_degree_one_certificate import C,var,add,scale,mul

def det(M):
    total={}
    for perm in permutations(range(len(M))):
        sign=(-1)**sum(perm[i]>perm[j] for i in range(len(M)) for j in range(i+1,len(M)))
        term=C(sign)
        for i,j in enumerate(perm):term=mul(term,M[i][j])
        total=add(total,term)
    return total

def same(a,b,label):
    if a!=b:raise RuntimeError(label)

def run():
    n,p,q,d,e=[var(i) for i in range(5)]
    beta=add(p,scale(d,-1));mu=add(n,scale(e,-1))
    H=add(scale(mul(mul(p,beta),mu),4),scale(mul(n,mul(beta,beta)),-2),scale(mul(q,mul(mu,mu)),-3))
    M=[[scale(q,6),scale(p,2),scale(beta,2)],[scale(p,2),n,mu],[scale(beta,2),mu,C(0)]]
    same(det(M),scale(H,2),'left Hessian determinant')
    R=add(scale(mul(p,p),2),scale(mul(n,q),-3),scale(mul(d,d),-2),scale(mul(e,q),4))
    same(mul(mu,R),add(H,mul(e,add(scale(mul(beta,beta),2),mul(mu,q)))),'left flag identity')
    C0=add(q,scale(p,2),n);K=add(scale(q,2),scale(p,3),n)
    cases=[
        (add(mul(K,add(q,p)),scale(mul(C0,add(scale(q,2),p)),-1)),add(mul(p,p),scale(mul(n,q),-1))),
        (add(mul(K,add(scale(q,2),p)),scale(mul(C0,add(scale(q,3),p)),-1)),add(mul(q,q),mul(p,q),mul(p,p),scale(mul(n,q),-1))),
        (add(mul(K,K),scale(mul(C0,add(scale(q,3),p)),-1)),add(mul(q,q),scale(mul(p,q),5),scale(mul(p,p),7),mul(n,q),scale(mul(n,p),5),mul(n,n)))
    ]
    for i,(lhs,rhs) in enumerate(cases):same(lhs,rhs,('zero-row identity',i))
    return {'left_Hessian_identity':True,'left_mixed_flag_identity':True,'grouped_zero_row_identities':3,'all_passed':True}

if __name__=='__main__':
    result=run();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
