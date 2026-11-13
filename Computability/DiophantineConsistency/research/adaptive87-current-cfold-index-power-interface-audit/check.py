#!/usr/bin/env python3
"""Pin and check Pell/source bindings and exact ring identities; no Lean."""
from pathlib import Path
from collections import Counter
import hashlib,itertools,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
PINS={
'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean':'374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5',
'Lean/DiophantineConsistency/ArithmeticPellClassification.lean':'77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78',
'Lean/DiophantineConsistency/ArithmeticPellCongruences.lean':'75e5e2c18b70a6cf9b4cdd0d1f8fe52bc3104c2ae34de5ff4169f5786885c6b1',
'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390',
'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794',
'research/adaptive87-current-cfold-orientation-q4/result.json':'5b79374b1237aac65cb473d55b9273942af66da115df7ba42cb5b8f705f77898',
'research/adaptive87-current-cfold-orientation-q4/README.md':'4c2c5ba63d8b457c9360a9c745a761a2a259800fd607cd4f5400f81e43b21fee',
'research/adaptive87-current-cfold88-degree28/graph.json':'26b5bc4c14320b0fe2891f3aeca0e216f26e555ee1206cefd71d7fcc7b674b36',
'research/adaptive87-current-cfold88-degree28/result.json':'957ab2a659c06f544862f2a027e8dc7ec9d66c50d3677137b2eb55c6ed95b2f7'}
for n,h in PINS.items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h,n
for n,token in [
 ('Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean','theorem positive_parameter_solution (Q x k : V)'),
 ('Lean/DiophantineConsistency/ArithmeticPellClassification.lean','theorem solution_index (b x y : V)'),
 ('Lean/DiophantineConsistency/ArithmeticPellCongruences.lean','theorem residue_quotients (time b m : V)'),
 ('Lean/DiophantineConsistency/Compact44/P72Exact.lean',"theorem indices_ordinary (q X Y k R g c a y0 i' f T u n s μ m η : V)"),
 ('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean','theorem power_bound (X Y r k c eta zeta : V)'),
 ('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean','theorem projection_quotient (a t : V)'),
 ('Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean','theorem scalar_rank_window (q beta MC MF J F alpha : V)')]:assert token in (ROOT/n).read_text(),n
g=json.loads((ROOT/'research/adaptive87-current-cfold88-degree28/graph.json').read_bytes());rows={r[0]:r for r in g['source']}
for row in [['ell','*','E','kY'],['c','+','eta','kY'],['a','+','E','Y'],['root_skew','*','k','C'],
 ['R','+','g47','g50'],['I','*','c2','i'],['g72','-','g71','Q'],['V','-','g76','c'],
 ['g78','+','V','u'],['g81','-','y2','g80'],['Fa','-','y2','g82']]:assert rows[row[0]]==row,row
# Exact identities in a sparse free commutative ring. Y=q^3*s is substituted
# in both the scale identity and the oriented-balance transformation.
N=11
def var(i):return {tuple(int(j==i) for j in range(N)):1}
one={(0,)*N:1}
def add(a,b,sign=1):
 c=a.copy()
 for k,v in b.items():c[k]=c.get(k,0)+sign*v
 return {k:v for k,v in c.items() if v}
def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(x+y for x,y in zip(m,n));c[k]=c.get(k,0)+v*w
 return {k:v for k,v in c.items() if v}
def times(a,n):return {k:v*n for k,v in a.items() if v*n}
X,q,s,w,d,H,a,c,gamma,R,u=map(var,range(N))
q2=mul(q,q);q3=mul(q2,q);Y=mul(q3,s);U=mul(Y,q2);E=mul(X,Y);W=times(mul(mul(mul(X,q),s),w),4);m=mul(mul(X,Y),Y)
assert mul(U,W)==times(mul(m,w),4)
base=add(add(d,X,-1),mul(a,c),-1);base=add(base,mul(H,gamma),-1)
left=add(mul(U,base),mul(H,add(mul(E,q),times(mul(m,w),4),-1)),-1)
qY=mul(q,Y);rightinner=add(add(mul(q,add(base,mul(H,W))),mul(H,X),-1),{},1)
assert left==mul(qY,rightinner)
# The signed auxiliary factor's difference from one is precisely the
# difference of the two natural-square sides expected by P72Exact.
Q,V,y=map(var,[0,1,2])
fa_minus=add(add(mul(y,y),mul(Q,add(mul(y,y),mul(V,V),-1)),-1),one,-1)
p72_diff=add(add(mul(Q,mul(V,V)),mul(y,y)),add(one,mul(Q,mul(y,y))),-1)
assert fa_minus==p72_diff
# P72 absdiff arguments when f,T,c,R,u are natural, including negative V.
cases=0;negative_V=0;negative_y=0
for f,T,c0,R0,u0 in itertools.product(range(1,5),range(1,5),range(1,5),range(0,10),range(1,5)):
 p=f*f*T*c0;n=f*f*R0+c0;V0=p-n;y0=V0+u0
 assert abs(p-n)**2==V0**2 and abs(p+u0-n)**2==y0**2
 cases+=1;negative_V+=V0<0;negative_y+=y0<0
assert negative_V>0 and negative_y>0
print(json.dumps({'status':'PASS','source_pins':PINS,'exact_scale_and_oriented_balance_identity':True,'exact_auxiliary_factor_identity':True,
 'absdiff_controls':{'total':cases,'V_negative':negative_V,'ordinate_negative':negative_y},
 'limits':['Source statement and algebra audit; no Lean execution, provider authentication or new derivation.',
 'The P72 exact-index and power-bound theorems are invoked only as historical fact-level interfaces.',
 'No claim that the new graph is already formally bound to these theorems or that the iPRA bridge is checked.']},indent=2,sort_keys=True))
