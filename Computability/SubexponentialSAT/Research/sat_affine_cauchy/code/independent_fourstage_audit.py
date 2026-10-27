#!/usr/bin/env python3
"""Independent support and schedule audit for the final 9->13->9->6 result.

This does not import the primary certificate implementation. Bit-set incidence
counts independently rebuild all supports. Schedule checks use exact rational
arithmetic. Constants also receive a floating-point recurrence cross-check;
the primary certificate supplies their rigorous rational intervals.
"""
from itertools import combinations
from fractions import Fraction as F
from math import sqrt,log,pi
import json


def require(ok,msg):
    if not ok: raise ArithmeticError(msg)


def generate(r,blocks):
    edges={e:j for j,e in enumerate(combinations(range(r),2))}
    universe=frozenset(range(r));ops=[];queue=[tuple(b) for b in blocks]
    require(sorted(v for b in blocks for v in b)==list(range(r)),'invalid partition')
    while queue:
        block=queue.pop(0)
        if len(block)<2: continue
        k=len(block)//2;a=block[:k];b=block[k:];queue += [a,b]
        ops.append((frozenset(a),frozenset(b),universe-frozenset(block)))
    ops.append(tuple(frozenset(b) for b in blocks))
    def between(a,b):
        ans=0
        for x in a:
            for y in b: ans|=1<<edges[tuple(sorted((x,y)))]
        return ans
    masks=[]
    for a,b,c in ops:
        classes=[between(a,b),between(a,c),between(b,c)]
        require(all(classes),'empty operation class')
        require((classes[0]&classes[1])|(classes[0]&classes[2])|(classes[1]&classes[2])==0,'overlap')
        allcross=classes[0]|classes[1]|classes[2]
        masks.extend((allcross,discount) for discount in classes)
    require(len(masks)==3*(r-2),'operation count')
    return masks


def ip(u,v):
    c,d=u;C,D=v
    return 25*(c&C).bit_count()-15*((d&C).bit_count()+(c&D).bit_count())+9*(d&D).bit_count()


def certify(r,plans):
    menus=[generate(r,p) for p in plans]
    matrix=[[max(ip(u,v) for u in a for v in b) for b in menus] for a in menus]
    q=len(plans);S=sum(map(sum,matrix))
    return {'groups':r,'plans':q,'mask_counts':[len(m) for m in menus],'maximum_dot_matrix':matrix,'S':S,'b_squared':str(F(2*S,25*q*q*r*r))}


def menus():
    affine=[]
    for a,b in ((1,0),(0,1),(1,1),(1,2)):
        affine.append([[j for j in range(9) if (a*(j%3)+b*(j//3))%3==c] for c in range(3)])
    seed=((11,2,8,9,7),(10,1,0,5),(6,4,3,12))
    cyclic=[[[ (x+shift)%13 for x in block] for block in seed] for shift in range(13)]
    c9=certify(9,affine);c13=certify(13,cyclic);c6=certify(6,[[[0,1],[2,3],[4,5]]])
    require(c9['maximum_dot_matrix']==[[486 if i==j else 288 for j in range(4)] for i in range(4)],'affine correlations')
    pattern=[1064,647,651,713,647,709,651,651,709,647,713,651,647]
    require(c13['maximum_dot_matrix']==[[pattern[(j-i)%13] for j in range(13)] for i in range(13)],'cyclic correlations')
    require(c9['b_squared']=='1/3' and c13['b_squared']=='56/169' and c6['b_squared']=='12/25','local coefficients')
    six=generate(6,[[0,1],[2,3],[4,5]])
    # BFS construction puts nine two-leaf merge masks before the final triangle.
    require(max(ip(v,v) for v in six[:9])==204,'six-group internal merge')
    require(max(ip(v,v) for v in six[9:])==216,'six-group triangle')
    return [c9,c13,c6]


def schedule():
    eta=[F(15773,10**6),F(9,800),F(4477,10**6),F(923,250000)]
    q=F(12,25)
    cumul=[eta[0],sum(eta[:2]),sum(eta[:3]),sum(eta[:3])+eta[3]/(1-q)]
    require(cumul==[F(15773,10**6),F(27023,10**6),F(63,2000),F(193,5000)],'cumulative schedule')
    roots=[(9,20000,63399),(13,2000,7401),(9,100,317),(6,200,517)]
    for base,power,exponent in roots: require(base**power<2**exponent,'log upper bound')
    logs=[F(c,b) for _,b,c in roots]
    gap=[F(1,10)-(2 if j==0 else 1)*cumul[j]*logs[j] for j in range(4)]
    expected=[F(7573,10**10),F(2777,2*10**9),F(29,200000),F(219,10**6)]
    require(gap==expected and min(gap)>0,'packing gap')
    fresh=cumul[-1]*(2*max(logs)+1)
    require(fresh==F(1621393,5000000) and fresh<1,'fresh-side/rounding gate')
    require(cumul[-1]<F(9,10),'new degree bound')
    require((1/q)**3<16,'depth bootstrap taper exponent')
    require(F(1,3)<F(1,2),'tail contraction ratio margin')
    # Guard B=ceil(6 log2 lambda), inherited precision exponent 15/4.
    require(F(15,4)-6<0,'precision guard decay')
    return {'etas':[str(e) for e in eta],'tail_ratio':str(q),'cumulative_caps':[str(x) for x in cumul],'exact_packing_gaps':[str(x) for x in gap],'fresh_side_exponent':str(fresh),'bootstrap_epsilon_numeric':1-.75*log(25/12,2),'precision_guard_power':str(F(15,4)-6)}


def constants():
    kap=pi*sqrt(2)/log(2)
    K=[kap/sqrt(15773/10**6),kap*(2/9)/sqrt(9/800),kap*(4/117)/sqrt(4477/10**6),kap*(8/1053)/sqrt(923/250000)]
    alpha=[4/9,sqrt(24)/13,4/9,sqrt(10)/6]
    b=[1/sqrt(3),sqrt(56)/13,1/sqrt(3),sqrt(12)/5]
    gamma=(1/3)/sqrt(12/25)
    require(alpha[-1]/(1-gamma)>b[-1],'tail path dominance')
    branch=[b[0]*K[0],alpha[0]*K[0]+b[1]*K[1],alpha[0]*K[0]+alpha[1]*K[1]+b[2]*K[2],sum(alpha[j]*K[j] for j in range(3))+alpha[-1]*K[-1]/(1-gamma)]
    closed_time=pi/log(2)*(4/9*sqrt(2000000/15773)+160*sqrt(14)/351)
    closed_space=pi/log(2)*sqrt(2000000/47319)
    require(abs(branch[1]-closed_time)<1e-12 and abs(branch[0]-closed_space)<1e-12,'closed form')
    require(branch[1]==max(branch) and branch[1]<30.414 and branch[0]<29.467,'dominant branch')
    # Direct recurrence unrolling, independently of finite-max reduction.
    Ks=K[:3]+[K[3]*gamma**d for d in range(90)]
    aa=alpha[:3]+[alpha[3]]*90;bb=b[:3]+[b[3]]*90
    paid=[];prefix=0
    for ak,bk,k in zip(aa,bb,Ks):
        paid.append(prefix+bk*k);prefix+=ak*k
    storage=[bk*k for bk,k in zip(bb,Ks)]
    require(abs(max(paid)-closed_time)<1e-12,'full paid recurrence')
    require(abs(max(storage)-closed_space)<1e-12,'recursive storage maximum')
    require(abs(prefix-branch[3])<1e-12,'terminal leaf multiplier')
    return {'branches_C0_C1_C2_Cinf':branch,'closed_form_time':closed_time,'closed_form_space':closed_space,'local_storage':[b[j]*K[j] for j in range(4)],'tail_K_ratio':gamma,'93_depth_paid_max':max(paid),'93_depth_terminal_child_path':prefix,'note':'Floating-point cross-check only; rigorous intervals supplied by primary rational checker'}


def main():
    return {'status':'PASS','method':'Independent bit-set reconstruction, exact rational schedule gates, and independently unrolled paid recurrence','finite_certificates':menus(),'schedule':schedule(),'constant_cross_check':constants(),'scope':'New menus and schedule validated relative to imported exact contraction identities, weighted entropy, and rational-matrix/CRT bridge; no full SAT formal verification'}

if __name__=='__main__': print(json.dumps(main(),indent=2))
