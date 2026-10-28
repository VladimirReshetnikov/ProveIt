#!/usr/bin/env python3
"""Exact comparison certificates for the three-stage cached schedule."""
from fractions import Fraction as F
import json
from verify_schedule import require,sqrt_interval,pi_interval,ln2_interval
from schedules import schedule_from_lambda

def add(*xs): return sum((x[0] for x in xs),F(0)),sum((x[1] for x in xs),F(0))
def mul(x,y): return x[0]*y[0],x[1]*y[1]
def scale(x,q): return x[0]*q,x[1]*q
def div(x,y):
    require(0<y[0]<=y[1],'positive interval denominator')
    return x[0]/y[1],x[1]/y[0]

def main():
    strict={'root7':7**89<2**250,'middle9':9**63<2**200,
            'tail6':6**193<2**500,'strassen_log_bound':7**16<2**45,
            'uniform_taper_growth':F(25,12)<F(5,2),
            'root_table_dominates_matrix':24+8*F(13,16)**2<30,
            'tail_matrix_below_077':F(2,9)*(2+F(13,16)**2)<F(77,100)**2}
    for label,value in strict.items(): require(value,label)
    # Cancel common k=pi*sqrt(2)/ln2 from the three candidates.
    K0=sqrt_interval(1/F(89,5000)); K1=scale(sqrt_interval(1/F(137,10000)),F(2,7)); K2=scale(sqrt_interval(1/F(923,250000)),F(4,63))
    a0=scale(sqrt_interval(F(12)),F(1,7)); a1=(F(4,9),)*2
    at=scale(sqrt_interval(F(10)),F(1,6)); b0=scale(sqrt_interval(F(30)),F(1,7))
    gamma=div((F(5,6),)*2,sqrt_interval(F(3)))
    tailfactor=div(at,(1-gamma[1],1-gamma[0]))
    require(tailfactor[0]>F(77,100),'tail cache dominates matrix')
    root=mul(b0,K0)
    middle=add(mul(a0,K0),scale(K1,F(77,100)))
    tail=add(mul(a0,K0),mul(a1,K1),mul(tailfactor,K2))
    require(root[0]>middle[1],'root dominates middle')
    require(root[0]>tail[1],'root dominates infinite tail')
    # Space comparisons similarly cancel k.
    memroot=mul(scale(sqrt_interval(F(24)),F(1,7)),K0)
    require(memroot[0]>F(2,3)*K1[1] and memroot[0]>F(2,3)*K2[1],'root space dominates')
    pi=pi_interval(); ln2=ln2_interval()
    C=div(mul(pi,sqrt_interval(F(300000,4361))),ln2)
    S=div(mul(pi,sqrt_interval(F(240000,4361))),ln2)
    require(F(37591702555541,10**12)<C[0]<=C[1]<F(37591702555542,10**12),'time enclosure')
    require(F(33623040921657,10**12)<S[0]<=S[1]<F(33623040921658,10**12),'space enclosure')
    require(C[1]<F(188,5) and S[1]<34,'safe rounded constants')
    require(F(89,5000)+F(137,10000)==F(63,2000),'first cumulative budget')
    require(F(923,250000)/(1-F(12,25))+F(63,2000)==F(193,5000),'full budget')
    # Finite generator checks exercise floor/cumulative behavior, not all-size feasibility.
    instances=0
    for family in ('polynomial','cached'):
        for lam in (1,2,10,1000,10**6,10**12):
            prev_a=0
            for d in range(18):
                z=schedule_from_lambda(lam,d,family)
                require(z['a']==prev_a+z['u']+z['g'],'exact cumulative recurrence')
                require(z['u']>=0 and z['a']>=z['u'],'nonnegative integer parameters')
                prev_a=z['a']; instances+=1
    out={'status':'pass','scope':'exact component certificates; all-size proof separate',
      'strict_margins':strict,'time_coefficient_interval':['37.591702555541','37.591702555542'],
      'space_coefficient_interval':['33.623040921657','33.623040921658'],
      'safe_eventual_time':'37.6','safe_eventual_space':34,
      'root_dominates_middle_and_infinite_tail':True,'generator_instances':instances,
      'optimizations_enabled':not __debug__}
    print(json.dumps(out,indent=2))
if __name__=='__main__': main()
