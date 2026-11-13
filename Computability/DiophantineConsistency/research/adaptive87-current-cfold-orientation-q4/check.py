#!/usr/bin/env python3
"""Graph-bound standard-integer orientation and q^4 congruence controls."""
from pathlib import Path
from math import gcd
import hashlib,json,itertools
D=Path(__file__).resolve().parent;ROOT=D.parents[1]
PINS={
'research/adaptive87-current-cfold88-degree28/graph.json':'26b5bc4c14320b0fe2891f3aeca0e216f26e555ee1206cefd71d7fcc7b674b36',
'research/adaptive87-current-cfold88-degree28/result.json':'957ab2a659c06f544862f2a027e8dc7ec9d66c50d3677137b2eb55c6ed95b2f7',
'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean':'40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884'}
for n,h in PINS.items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h,n
g=json.loads((ROOT/'research/adaptive87-current-cfold88-degree28/graph.json').read_bytes());r={row[0]:row for row in g['source']}
expected=[['qm','*','J','beta'],['q','+',1,'qm'],['q2','*','q','q'],['q3','*','q','q2'],['U','*','Y','q2'],
 ['qF','-','q','F'],['C','-','qF','alpha'],['E','*','X','Y'],['k','+','eta','zeta'],['kY','*','Y','k'],['c','+','eta','kY'],
 ['a','+','E','Y'],['g15','*',4,'a'],['H','+',3,'g15'],['g17','*','a','a'],['Delta','+','H','g17'],['g19','*','a','c'],['b0','+','X','g19'],
 ['g44','*','qF','qm'],['G','+','alpha','g44'],['g46','-','q2',1],['g47','*','G','g46'],['g48','*','MF','q'],['g49','+','MC','g48'],['g50','*','J','g49'],['R','+','g47','g50'],
 ['g52','-','k','R'],['r0','-','g52',1],['g54','*','U','gamma'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59'],
 ['g61','*','Dstar','Dstar'],['g62','*','U','U'],['g63','*','Delta','c2'],['g64','+',1,'g63'],['g65','*','g62','g64'],['A1','-','g61','g65']]
for row in expected:assert r.get(row[0])==row,row
# Sparse free-ring check of Dstar shape and rearranged oriented balance.
N=10
def atom(i):return {tuple(int(j==i) for j in range(N)):1}
one={(0,)*N:1}
def add(a,b,s=1):
 z=a.copy()
 for m,v in b.items():z[m]=z.get(m,0)+s*v
 return {m:v for m,v in z.items() if v}
def mul(a,b):
 z={}
 for m,v in a.items():
  for n,w in b.items():
   p=tuple(x+y for x,y in zip(m,n));z[p]=z.get(p,0)+v*w
 return {m:v for m,v in z.items() if v}
# Use ten independent indeterminates, including k.
U,X,a,c,H,gamma,E,q,R,k=map(atom,range(N))
b0=add(X,mul(a,c));r0=add(add(k,R,-1),one,-1);shift=add(add(mul(U,gamma),mul(E,q)),r0,-1)
actual=add(mul(U,b0),mul(H,shift))
target=add(mul(U,add(X,mul(a,c))),mul(H,add(add(add(mul(U,gamma),mul(E,q)),R),add(one,k,-1))))
assert actual==target
# Exhaustive controls for inequalities and the gcd identity; mathematical proof is in README.
counts={'positivity':0,'gcd':0,'q4_congruence':0}
for q0,Y0,a0 in itertools.product(range(3,20),range(1,12),range(2,20)):
 assert q0*q0*Y0*Y0*a0>4*a0+3;counts['positivity']+=1
for q0,s0,X0 in itertools.product(range(3,60),range(1,6),range(1,6)):
 Y0=q0**3*s0;H0=3+4*Y0*(X0+1)
 gg=gcd(H0,q0**5);assert gg==gcd(3,q0) and q0%gg==0
 Eq=X0*Y0*q0
 for w in range(-2,3):
  # A true balance implies q^5 | H*(Eq+R+1-k).
  test=(q0**5//gg)*w-Eq
  assert (H0*(Eq+test))%(q0**5)==0 and test%q0**4==0
  assert (H0*(Eq+test+1))%(q0**5)!=0
  counts['q4_congruence']+=1
 counts['gcd']+=1
print(json.dumps({'status':'PASS','pins':PINS,'checked_graph_rows':len(expected),'exact_free_ring_Dstar_identity':True,'bounded_controls':counts,
 'limits':['Standard-integer arithmetic only; no Lean execution or all-model claim.',
 'The main Pell equality, positive inputs, q>=3, R>=0 and Y=q^3*s are explicit hypotheses.',
 'Controls and source hashes do not prove index alignment, X>=q^2, Cal, or zero equivalence.']},sort_keys=True,indent=2))
