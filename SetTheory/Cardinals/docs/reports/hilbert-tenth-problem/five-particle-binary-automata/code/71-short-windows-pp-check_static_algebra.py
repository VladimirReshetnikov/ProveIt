"""Fresh symbolic affine arithmetic only; no CA rule, interpreter, or trajectory.

A=(a,b,c) denotes a*D+b*J+c for all D>=2 and J>=0.
Endpoint support checks use the corners of each affine t,d parameter box.
"""
from pathlib import Path
import json

OUT = Path(__file__).resolve().parent / 'static-algebra-certificate.json'
D, J, one = (1,0,0), (0,1,0), (0,0,1)
zero=(0,0,0)
def add(*xs): return tuple(sum(x[i] for x in xs) for i in range(3))
def neg(x): return tuple(-v for v in x)
def sub(x,y): return add(x,neg(y))
def mul(n,x): return tuple(n*v for v in x)
def evaluate(x,d,j): return x[0]*d+x[1]*j+x[2]
checks=[]
def eq(label,x,y):
    if x!=y: raise RuntimeError((label,x,y))
    checks.append({'label':label,'kind':'affine_identity','value':list(x)})
def nonneg(label,x):
    if not (x[0]>=0 and x[1]>=0 and 2*x[0]+x[2]>=0):
        raise RuntimeError((label,x))
    checks.append({'label':label,'kind':'nonnegative_D_ge_2_J_ge_0','margin':list(x)})

S=add(mul(2,D),mul(2,one)); B2=add(D,one)
L=add(mul(3,D),mul(4,one)); b=add(mul(4,D),mul(5,one))
Z=add(mul(10,b),mul(10,one),mul(2,J)); r=add(Z,J)
H=add(b,r); edge=add(mul(3,b),r); phase=mul(6,b)
total=add(edge,phase); refined=sub(total,one)
eq('b=L+D+1',b,add(L,D,one))
nonneg('L>=B2',sub(L,B2)); nonneg('b>=L',sub(b,L))
nonneg('r>=3b',sub(r,mul(3,b)))
nonneg('H>=4b',sub(H,mul(4,b)))
nonneg('Z-1>3b+1',sub(sub(Z,one),add(mul(3,b),mul(2,one))))
nonneg('Z>2(L+1)',sub(Z,add(mul(2,L),mul(3,one))))
nonneg('head-marker distance S-D>D',sub(S,add(mul(2,D),one)))
nonneg('class reads are outside b',sub(Z,add(b,one)))
eq('edge radius',edge,add(mul(13,b),mul(10,one),mul(3,J)))
eq('main total in D,J',total,add(mul(76,D),mul(3,J),mul(105,one)))
eq('one-site refinement in D,J',refined,add(mul(76,D),mul(3,J),mul(104,one)))

support_count=0
def support(label,coordinates,bound):
    global support_count
    for i,x in enumerate(coordinates):
        nonneg(label+': upper '+str(i),sub(bound,x))
        nonneg(label+': lower '+str(i),add(bound,x))
    support_count+=1
for d in (one,D):
    for w in (-1,1):
        support('free-edge '+str((d,w)),[zero,d,mul(w,one),add(mul(w,one),d)],B2)
        for t in (S,L):
            support('behind '+str((d,w,t)),[zero,mul(w,t),add(mul(w,t),d),mul(w,add(t,one)),add(mul(w,add(t,one)),d)],b)
        for t in (add(S,one),L):
            support('ahead '+str((d,w,t)),[zero,mul(-w,t),add(mul(-w,t),d),mul(-w,sub(t,one)),add(mul(-w,sub(t,one)),d)],b)
        for delta in (-1,1):
            marker=mul(w*delta,one)
            head=add(marker,mul(-w,S))
            support('endpoint '+str((d,w,delta)),[zero,mul(-w,S),add(mul(-w,S),d),marker,head,add(head,d)],b)
        support('dispatch-commit '+str((d,w)),[zero,S,add(S,d),mul(w,S),add(mul(w,S),d)],b)
        for t in (S,L):
            support('phase-near '+str((d,w,t)),[zero,mul(w,t),add(mul(w,t),d)],sub(b,one))
    support('phase-free '+str(d),[zero,d],B2)
    support('phase-home-direct '+str(d),[zero,S,add(S,d)],sub(b,one))

examples={}
for name,d,j in [('small_source',8,0),('clean_target',18,1),('inherited_universal',509508,0)]:
    row={k:evaluate(v,d,j) for k,v in [('D',D),('J',J),('S',S),('B2',B2),('L',L),('b',b),('Z',Z),('r',r),('H_edge',H),('edge_radius',edge),('phase_radius',phase),('main_total',total),('refined_total',refined)]}
    row.update(accepted_two_scale=108*d+149+3*j,report26=180*d+258+9*j)
    row['reduction_from_accepted_two_scale']=row['accepted_two_scale']-row['main_total']
    examples[name]=row
if 2*122622+4*66066 != 509508: raise RuntimeError('Inherited ledger arithmetic')
result={
    'status':'passed',
    'kind':'fresh static affine algebra; not a source compiler, CA evaluator, or trajectory simulator',
    'domain':'D>=2,J>=0; corners suffice for affine endpoint support boxes',
    'affine_coordinate_order':['D','J','constant'],
    'checks':checks,
    'support_corner_cases':support_count,
    'examples':examples,
    'universal_source_inherited_not_executed':True,
    'scope':'Arithmetic and support bounds only; the full-shift and admissible-set proofs are symbolic in PROOF.md',
}
OUT.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'passed','affine_checks':len(checks),'support_corner_cases':support_count,'examples':examples},indent=2))
