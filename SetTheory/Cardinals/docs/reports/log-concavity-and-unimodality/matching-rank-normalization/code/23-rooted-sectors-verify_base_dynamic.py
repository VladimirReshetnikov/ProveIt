"""Independent endpoint-set enumeration of a scalar ULC3 counterexample.

No profile formulas are used in endpoint_coefficients. All computations are integers.
"""
from itertools import combinations
from pathlib import Path
import json

def support_count(core,left,right):
    rows=core+left
    fixed_columns=[sum(1<<i for i,row in enumerate(rows) if row>>j&1) for j in range(3)]
    states={0}
    for col in fixed_columns+right:
        next_states=set()
        for state in states:
            avail=col&~state
            while avail:
                bit=avail&-avail;avail-=bit
                next_states.add(state|bit)
        states=next_states
    return len(states)

def endpoint_coefficients(core,left,right,activities):
    out=[]
    for k in range(4):
        value=0
        for I in combinations(range(len(right)),k):
            term=support_count(core,left,[right[i] for i in I])
            for i in I:term*=activities[i]
            value+=term
        out.append(value)
    return out

core=[2,1,0];left=[7]*8;right=[1,2]+[3]*7+[4];activities=[15,15]+[1]*7+[15]
c=endpoint_coefficients(core,left,right,activities)
gaps=[c[1]**2-3*c[0]*c[2],c[2]**2-3*c[1]*c[3]]
# Independently derived factorization: D(t)=120+3500t+25536t²; C(t)=(1+15t)D(t).
a,b,d,y=120,3500,25536,15
if c!=[a,b+a*y,d+b*y,d*y]:raise RuntimeError('factorization')
if not all(v>0 for v in c):raise RuntimeError('positive coefficients')
if not all(v<0 for v in gaps):raise RuntimeError('ULC3 signs')
if not support_count(core,left,[1,2,4]):raise RuntimeError('rank-six witness')
out={'core_rows':core,'exterior_left_masks':left,'exterior_right_masks':right,'exterior_right_activities':activities,'all_left_activities':1,'forced_B_activities':1,'vertices':6+len(left)+len(right),'edges':sum(x.bit_count() for x in core+left+right),'matching_rank':6,'conditional_cubic':c,'ulc3_gaps':gaps,'quadratic_factor':[a,b,d],'linear_factor_activity':y,'quadratic_discriminant':b*b-4*a*d}
print(json.dumps(out,indent=2));Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
