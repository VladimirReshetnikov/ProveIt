"""Exact flag identities, using only rational sparse-polynomial arithmetic."""
from itertools import permutations
from fractions import Fraction as Q
from pathlib import Path
import json
from verify_degree_one_certificate import C,var,add,mul,scale

def determinant(matrix):
    out={}
    for perm in permutations(range(len(matrix))):
        inversions=sum(perm[i]>perm[j] for i in range(len(perm)) for j in range(i+1,len(perm)))
        term=C((-1)**inversions)
        for i,j in enumerate(perm):term=mul(term,matrix[i][j])
        out=add(out,term)
    return out

def run():
    n,p,q,d,e=[var(i) for i in range(5)]
    h=add(p,scale(d,-1));mu=add(n,scale(e,-1))
    H=[[scale(q,6),scale(p,2),scale(h,2)],[scale(p,2),n,n],[scale(h,2),n,mu]]
    G=add(scale(mul(e,mul(p,p)),2),scale(mul(e,mul(n,q)),-3),scale(mul(n,mul(d,d)),-2))
    if determinant(H)!=scale(G,2):raise RuntimeError('left Hessian determinant')
    # The right Schur form, coefficient by coefficient in U,V,W,u,omega.
    obtained=[scale(mul(q,q),2),scale(mul(q,h),2),add(mul(h,h),scale(mul(d,h),2)),scale(mul(q,d),2),scale(mul(d,h),-2)]
    expected=[scale(mul(q,q),2),scale(mul(q,add(p,scale(d,-1))),2),add(mul(p,p),scale(mul(d,d),-1)),scale(mul(q,d),2),scale(mul(d,h),-2)]
    if obtained!=expected:raise RuntimeError('right Schur quadratic')
    if add(mul(p,p),scale(mul(d,d),-1),scale(mul(d,h),-2),scale(mul(e,q),2))!=add(mul(h,h),scale(mul(e,q),2)):
        raise RuntimeError('mixture identity')
    return {'left_Hessian_identity':True,'right_Schur_identity':True,'axis_mixture_identity':True,'all_passed':True}

if __name__=='__main__':
    result=run();Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
