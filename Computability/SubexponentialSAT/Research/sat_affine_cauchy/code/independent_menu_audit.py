#!/usr/bin/env python3
"""Independent bit-set reconstruction of finite menu support certificates."""
from itertools import combinations
from fractions import Fraction
from math import sqrt, log, pi
from pathlib import Path
import json


def require(ok, msg):
    if not ok: raise ArithmeticError(msg)


def generate(r, blocks):
    edge_index={e:j for j,e in enumerate(combinations(range(r),2))}
    all_vertices=frozenset(range(r)); operations=[]; queue=[tuple(b) for b in blocks]
    require(sorted(v for b in blocks for v in b)==list(range(r)), 'partition')
    while queue:
        block=queue.pop(0)
        if len(block)<2: continue
        split=len(block)//2; left=block[:split];right=block[split:]
        queue += [left,right]
        operations.append((frozenset(left),frozenset(right),all_vertices-frozenset(block)))
    operations.append(tuple(frozenset(b) for b in blocks))
    def between(a,b):
        ans=0
        for x in a:
            for y in b: ans |= 1<<edge_index[tuple(sorted((x,y)))]
        return ans
    masks=[]
    for a,b,c in operations:
        three=[between(a,b),between(a,c),between(b,c)]
        cross=three[0]|three[1]|three[2]
        require((three[0]&three[1])|(three[0]&three[2])|(three[1]&three[2])==0,'edge class overlap')
        masks.extend((cross,d) for d in three)
    return masks


def ip(u,v):
    c,d=u;C,D=v
    return 25*(c&C).bit_count()-15*((d&C).bit_count()+(c&D).bit_count())+9*(d&D).bit_count()


def certify(r,plans):
    menus=[generate(r,p) for p in plans]
    matrix=[[max(ip(x,y) for x in a for y in b) for b in menus] for a in menus]
    q=len(plans); total=sum(map(sum,matrix))
    return {'r':r,'plans':q,'mask_counts':[len(x) for x in menus],'maximum_dot_matrix':matrix,'S':total,'b_squared':str(Fraction(2*total,25*q*q*r*r))}


def main():
    affine=[]
    for linear in (lambda x,y:x,lambda x,y:y,lambda x,y:x+y,lambda x,y:x+2*y):
        affine.append([[j for j in range(9) if linear(j%3,j//3)%3==a] for a in range(3)])
    seed=((11,2,8,9,7),(10,1,0,5),(6,4,3,12))
    cyclic=[[[ (x+shift)%13 for x in block] for block in seed] for shift in range(13)]
    a=certify(9,affine);c=certify(13,cyclic);tail=certify(7,[[(0,1,2),(3,4),(5,6)]])
    require(a['maximum_dot_matrix']==[[486 if i==j else 288 for j in range(4)] for i in range(4)],'affine matrix')
    pattern=[1064,647,651,713,647,709,651,651,709,647,713,651,647]
    require(c['maximum_dot_matrix']==[[pattern[(j-i)%13] for j in range(13)] for i in range(13)],'cyclic matrix')
    require(a['b_squared']=='1/3' and c['b_squared']=='56/169' and tail['b_squared']=='632/1225','norm constants')
    kap=pi*sqrt(2)/log(2)
    K0=kap/sqrt(63/4000); K1=kap*(2/9)/sqrt(9/800); K2=kap*(4/117)/sqrt(77/16200)
    C0=K0/sqrt(3); C1=4*K0/9+sqrt(56)*K1/13
    Cinf=4*K0/9+sqrt(24)*K1/13+sqrt(3)*K2/2
    # Unroll all explicit paid aggregation branches, independent of closed-form max.
    alphas=[4/9,sqrt(24)/13]+[sqrt(12)/7]*80
    bs=[1/sqrt(3),sqrt(56)/13]+[sqrt(632)/35]*80
    Ks=[K0,K1]+[K2*(3/7)**j for j in range(80)]
    prefix=0; paid=[]
    for alpha,b,K in zip(alphas,bs,Ks):
        paid.append(prefix+b*K);prefix+=alpha*K
    require(max(paid)<=Cinf+1e-12 and abs(prefix-Cinf)<1e-12,'paid recurrence')
    require(Cinf<30.513 and C0<29.488,'coefficient thresholds')
    require(abs(max(b*K for b,K in zip(bs,Ks))-C0)<1e-12,'storage maximum')
    return {'status':'PASS','method':'Independent bit-set incidence formula, no import of original checker','finite_certificates':[a,c,tail],'numeric_cross_check_only':{'root':C0,'depth1':C1,'path':Cinf,'82_level_paid_max':max(paid),'82_level_single_path_storage':max(b*K for b,K in zip(bs,Ks))},'proof_scope':'Relative to inherited weighted entropy, exact group identities, strict schedule, and rational-matrix-to-ring bridge; no independent full SAT verification'}

if __name__=='__main__':
    result=main();print(json.dumps(result,indent=2))
