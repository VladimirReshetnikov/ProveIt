#!/usr/bin/env python3
"""Independent stdlib certificate for the four thirteen-group plans.

Supports come from explicit edge products of disjoint vertex classes.
The exhaustive loop uses an exact Gram expansion of each squared norm;
its aggregate is independently checked by summing the Gram matrices.
"""
import argparse
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path

PLANS = [
 [[0,1,2,3,4],[5,6,7,8],[9,10,11,12]],
 [[12,10,1,6,4],[9,0,3,8],[5,2,7,11]],
 [[0,8,11,12,1],[7,10,4,3],[5,2,6,9]],
 [[1,7,0,6,9],[5,10,11,3],[12,8,4,2]],
]


def require(condition,message):
    if not condition:raise RuntimeError(message)


def profiles(plan):
    vertices=set(range(13));edges=list(combinations(range(13),2))
    require(sorted(x for b in plan for x in b)==list(range(13)),'Invalid partition')
    ops=[]
    # Iterative interval traversal; operation order is irrelevant to the norm certificate.
    for block in plan:
        stack=[block]
        while stack:
            piece=stack.pop()
            if len(piece)==1:continue
            half=len(piece)//2
            a,b=piece[:half],piece[half:]
            ops.append((set(a),set(b),vertices-set(piece)))
            stack.extend([a,b])
    ops.append(tuple(map(set,plan)))
    require(len(ops)==11,'Operation count failed')
    result=[]
    for a,b,c in ops:
        domains=[{tuple(sorted((x,y))) for x in u for y in v}
                 for u,v in [(a,b),(a,c),(b,c)]]
        require(sum(map(len,domains))==len(set.union(*domains)),'Domains overlap')
        for disc in range(3):
            coeff={e:0 for e in edges}
            for j,d in enumerate(domains):
                for e in d:coeff[e]=2 if j==disc else 5
            result.append(tuple(coeff[e]for e in edges))
    require(len(result)==33,'Profile count failed')
    return result


def certify():
    menus=list(map(profiles,PLANS));n=33
    norms=[[sum(x*x for x in v)for v in rows]for rows in menus]
    gram={(i,j):[[sum(x*y for x,y in zip(v,w))for w in menus[j]]for v in menus[i]]
          for i,j in combinations(range(4),2)}
    ab,ac,ad,bc,bd,cd=(gram[i,j]for i,j in [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)])
    maximum=-1;total=0;count=0;witness=None;maxcount=0
    for i in range(n):
        for j in range(n):
            ij=norms[0][i]+norms[1][j]+2*ab[i][j]
            for k in range(n):
                ijk=ij+norms[2][k]+2*(ac[i][k]+bc[j][k])
                for l in range(n):
                    val=ijk+norms[3][l]+2*(ad[i][l]+bd[j][l]+cd[k][l])
                    if val>maximum:
                        maximum=val;witness=[i,j,k,l];maxcount=1
                    elif val==maximum:maxcount+=1
                    total+=val;count+=1
    independent_total=n**3*sum(map(sum,norms))+2*n**2*sum(sum(map(sum,g))for g in gram.values())
    require(total==independent_total,'Gram aggregate identity failed')
    require(maximum==12020,'Sharp norm bound failed')
    require(count==33**4,'Exhaustive count failed')
    actual=[sum(menus[j][witness[j]][e]for j in range(4))for e in range(78)]
    require(sum(x*x for x in actual)==maximum,'Direct witness check failed')
    b=Fraction(2*maximum,25*16*169)
    require(b==Fraction(601,1690),'Normalization failed')
    return {'status':'PASS','plans':PLANS,'profile_counts':[33]*4,
            'maximum_squared_norm':maximum,'tuples_checked':count,
            'sum_of_squared_norms':total,'independent_gram_sum':independent_total,
            'first_witness_in_independent_order':witness,'maximizing_tuples':maxcount,
            'local_coefficient_squared':str(b),'sum_vector_of_first_witness':actual}


def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path);a=p.parse_args()
    result=certify();text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
