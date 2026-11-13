#!/usr/bin/env python3
"""Independent graph/source-bound and algebra checks; no Lean."""
import hashlib,json,itertools,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parents[2];D=Path(__file__).resolve().parent
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
for n,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256((R/n).read_bytes()).hexdigest()==h,n
src=json.loads((R/'research/adaptive87-current-cfold88-degree28/graph.json').read_bytes())['source']; r={v[0]:v[1:] for v in src}
expected={'qm':['*','J','beta'],'q':['+',1,'qm'],'q2':['*','q','q'],'q3':['*','q','q2'],'U':['*','Y','q2'],'qF':['-','q','F'],'C':['-','qF','alpha'],'E':['*','X','Y'],'k':['+','eta','zeta'],'kY':['*','Y','k'],'c':['+','eta','kY'],'c2':['*','c','c'],'ell':['*','E','kY'],'a':['+','E','Y'],'g15':['*',4,'a'],'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17'],'g19':['*','a','c'],'b0':['+','X','g19'],'g44':['*','qF','qm'],'G':['+','alpha','g44'],'g46':['-','q2',1],'g47':['*','G','g46'],'g48':['*','MF','q'],'g49':['+','MC','g48'],'g50':['*','J','g49'],'R':['+','g47','g50'],'g52':['-','k','R'],'r0':['-','g52',1],'g54':['*','U','gamma'],'g55':['*','E','q'],'g56':['+','g54','g55'],'shift':['-','g56','r0'],'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65'],'f2':['*','f','f'],'rho':['-','f2',1],'Q':['*','Delta','rho'],'I':['*','c2','i'],'g71':['*','I','I'],'g72':['-','g71','Q'],'g74':['*','T','c'],'g75':['-','g74','R'],'g76':['*','f2','g75'],'V':['-','g76','c'],'g78':['+','V','u'],'y2':['*','g78','g78'],'g80':['*','V','V'],'g81':['-','y2','g80'],'g82':['*','Q','g81'],'Fa':['-','y2','g82']}
assert all(r[n]==v for n,v in expected.items())
# Pin exact individual signatures including both absdiffs and both Pell indices.
def src_contains(path, terms):
 s=(R/path).read_text()
 for term in terms:assert term in s,(path,term)
src_contains('Lean/DiophantineConsistency/ArithmeticPellFirstNorm.lean',['theorem positive_parameter_solution (Q x k : V) (hQ : 0<Q)','2*ycoord time (2*(Q-1)+1)=k'])
src_contains('Lean/DiophantineConsistency/ArithmeticPellCongruences.lean',['theorem residue_quotients (time b m : V) (hm : m∣b+1)','ycoord time b=time+m*s'])
src_contains('Lean/DiophantineConsistency/ArithmeticPellClassification.lean',['theorem solution_index (b x y : V)','xcoord time b=x ∧ ycoord time b=y'])
src_contains('Lean/DiophantineConsistency/Compact44/P72Exact.lean',["(hny : 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k)","(hks : k = 2 * n + 4 * ((X * Y) * Y) * s)","(hmy : ycoord m a = c)","(hg : g * g = 1 + delta a * c * c)","(hs' : (i' * c * c) * (i' * c * c) + delta a = delta a * (f * f))",'absdiff (f * f * (T * c) + u) (f * f * R + c)','13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1'])
src_contains('Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean',['theorem scalar_rank_window','(hgap : F+alpha<q)','+q^3+q+1≤q^4'])
src_contains('Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean',['theorem power_bound (X Y r k c eta zeta : V) (hX : 16≤X)','(hc : c=ycoord (2*r+1) (Y*(X+1)))','(hk : k=2*ycoord (r+1) (2*(X*Y*Y-1)+1))','theorem projection_quotient (a t : V)'])
# Free commutative-ring certificates for both positive-q cancellation and the
# final projection. Monomials are exponent tuples, coefficients are integers.
N=10
def var(i):return {tuple(int(i==j) for j in range(N)):1}
def const(k):return {(0,)*N:k} if k else {}
def add(a,b,sgn=1):
 z=a.copy()
 for m,v in b.items():z[m]=z.get(m,0)+sgn*v
 return {m:v for m,v in z.items() if v}
def mul(a,b):
 z={}
 for m,x in a.items():
  for n,y in b.items():
   key=tuple(i+j for i,j in zip(m,n));z[key]=z.get(key,0)+x*y
 return {m:v for m,v in z.items() if v}
def prod(*xs):
 z=const(1)
 for x in xs:z=mul(z,x)
 return z
q,s,X,H,gamma,d,a,c,w=map(var,range(9));Y=prod(q,q,q,s);U=prod(Y,q,q);m=prod(X,Y,Y);W=prod(const(4),X,q,s,w)
assert prod(const(4),m,w)==prod(U,W)
A=add(add(d,X,-1),prod(a,c),-1)
B=add(add(prod(q,add(A,prod(H,add(W,gamma,-1)))),prod(H,X),-1),const(0))
L=var(9) # independent of q, s, X, H, and the remaining atoms
# qL=H-3 is an explicit algebraic substitution, no division is performed.
Hrep=add(prod(q,L),const(3))
Br=add(prod(q,add(A,prod(Hrep,add(W,gamma,-1)))),prod(Hrep,X),-1)
# 3A = H*(A+qL*(W-gamma)-L*X)-L*B when H=qL+3.
rhs=add(prod(Hrep,add(add(A,prod(q,L,add(W,gamma,-1))),prod(L,X),-1)),prod(L,Br),-1)
assert prod(const(3),A)==rhs
# Exhaust signed difference mapping for distinct source values, including V<0.
count=0
for f,T,c0,R0,u in itertools.product(range(1,5),range(1,5),range(1,5),range(0,6),range(1,5)):
 P=f*f*T*c0;N0=f*f*R0+c0;V=P-N0
 assert abs(P-N0)**2==V**2 and abs(P+u-N0)**2==(V+u)**2
 count+=1
out=subprocess.check_output([sys.executable,'-I','-S','-B',str(R/'research/adaptive87-current-cfold-cal-fact-replay/check.py')],cwd=R)
assert out==(R/'research/adaptive87-current-cfold-cal-fact-replay/receipt.json').read_bytes()
print(json.dumps({'graph_rows_checked':len(expected),'exact_scale_identity':True,'exact_projection_identity':True,'signed_absdiff_controls':count,'source_interfaces':6,'author_receipt_reproduced':True,'lean_executed':False},sort_keys=True,indent=2))
