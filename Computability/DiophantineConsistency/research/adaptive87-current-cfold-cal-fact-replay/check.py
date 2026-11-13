#!/usr/bin/env python3
"""Exact graph/source pins and symbolic balancing identities; no Lean."""
import hashlib,itertools,json,resource,sys
from pathlib import Path
if not (sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode):raise SystemExit('use python3 -I -S -B')
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
r=Path(__file__).resolve().parents[2];d=Path(__file__).resolve().parent;sha=lambda x:hashlib.sha256(x).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
pins=json.loads((d/'pins.json').read_bytes())
for f,h in pins.items():need(sha((r/f).read_bytes())==h,'pin '+f)
def read(p):return (r/p).read_text()
g=json.loads(read('research/adaptive87-current-cfold88-degree28/graph.json'));rows={x[0]:x for x in g['source']}
expected=[['qm','*','J','beta'],['q','+',1,'qm'],['q2','*','q','q'],['q3','*','q','q2'],['U','*','Y','q2'],['qF','-','q','F'],['C','-','qF','alpha'],['E','*','X','Y'],['k','+','eta','zeta'],['kY','*','Y','k'],['c','+','eta','kY'],['a','+','E','Y'],['g15','*',4,'a'],['H','+',3,'g15'],['g17','*','a','a'],['Delta','+','H','g17'],['root_skew','*','k','C'],['g44','*','qF','qm'],['G','+','alpha','g44'],['g46','-','q2',1],['g47','*','G','g46'],['g48','*','MF','q'],['g49','+','MC','g48'],['g50','*','J','g49'],['R','+','g47','g50'],['g52','-','k','R'],['r0','-','g52',1],['g54','*','U','gamma'],['g55','*','E','q'],['g56','+','g54','g55'],['shift','-','g56','r0'],['g58','*','U','b0'],['g59','*','H','shift'],['Dstar','+','g58','g59'],['f2','*','f','f'],['rho','-','f2',1],['Q','*','Delta','rho'],['I','*','c2','i'],['g71','*','I','I'],['g72','-','g71','Q'],['g74','*','T','c'],['g75','-','g74','R'],['g76','*','f2','g75'],['V','-','g76','c'],['g78','+','V','u'],['y2','*','g78','g78'],['g80','*','V','V'],['g81','-','y2','g80'],['g82','*','Q','g81'],['Fa','-','y2','g82']]
for x in expected:need(rows.get(x[0])==x,'row '+x[0])
checks={'Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean':['theorem positive_parameter_solution (Q x k : V)','2*ycoord time (2*(Q-1)+1)=k'], 'Lean/DiophantineConsistency/ArithmeticPellClassification.lean':['theorem solution_index (b x y : V)','xcoord time b=x ∧ ycoord time b=y'], 'Lean/DiophantineConsistency/ArithmeticPellCongruences.lean':['theorem residue_quotients (time b m : V) (hm : m∣b+1)','ycoord time b=time+m*s'], 'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':['theorem scalar_rank_window','(hgap : F+alpha<q)','+q^3+q+1≤q^4'], 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':['theorem indices_ordinary','(hR26 : 26 ≤ R)','(hnmod : (2 * n) % μ = R + 1)','13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1'], 'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean':['theorem power_bound (X Y r k c eta zeta : V)','(hX : 16≤X)','theorem projection_quotient (a t : V)']}
for f,tokens in checks.items():
 s=read(f)
 for t in tokens:need(t in s,'interface '+f+' '+t)
# Free polynomial ring on q,s,X,H,g,d,a,c,n,w. Verify the exact same-index carrier.
N=10
def var(i):return {tuple(int(i==j) for j in range(N)):1}
def scalar(n):return {(0,)*N:n} if n else {}
def add(a,b,k=1):
 z=a.copy()
 for m,v in b.items():z[m]=z.get(m,0)+k*v
 return {m:v for m,v in z.items() if v}
def mul(a,b):
 z={}
 for m,x in a.items():
  for n,y in b.items():
   e=tuple(i+j for i,j in zip(m,n));z[e]=z.get(e,0)+x*y
 return {m:v for m,v in z.items() if v}
def prod(*x):
 z=scalar(1)
 for y in x:z=mul(z,y)
 return z
q,s,X,H,gamma,d0,a,c,n,w=[var(i) for i in range(N)];Y=prod(q,q,q,s);U=prod(Y,q,q);m=prod(X,Y,Y);R=add(prod(scalar(2),n),scalar(1),-1);k=add(prod(scalar(2),n),prod(scalar(4),m,w));W=prod(scalar(4),X,q,s,w)
main=add(add(prod(U,d0),prod(U,add(X,prod(a,c))),-1),prod(H,add(add(prod(U,gamma),prod(X,Y,q)),add(R,scalar(1)))), -1)
# main currently excludes the -k term; add it with the correct sign.
main=add(main,prod(H,k))
balance=add(add(prod(q,add(d0,prod(H,W))),prod(q,add(add(X,prod(a,c)),prod(H,gamma))),-1),prod(H,X),-1)
need(main==prod(Y,q,balance),'carrier balance exact')
need(prod(scalar(4),m)==prod(q,q,q,q,scalar(4),X,q,q,s,s),'q4 divides 4m polynomial')
need(add(prod(add(prod(scalar(2),q),scalar(-1)),add(prod(q,q),scalar(-1))),prod(q,q,q),-1)==add(prod(add(q,scalar(-2)),add(prod(q,q),q)),scalar(1)),'rank algebra')
print(json.dumps({'scope':'graph/source text pins and exact symbolic balances; universal Pell replay is mathematical and unelaborated','pins_sha256':sha((d/'pins.json').read_bytes()),'graph_rows_checked':len(expected),'source_theorem_interfaces_checked':len(checks),'same_index_oriented_balance':True,'q4_divides_four_m_identity':True,'carrier_balance_monomials':len(main)},sort_keys=True,indent=2))
