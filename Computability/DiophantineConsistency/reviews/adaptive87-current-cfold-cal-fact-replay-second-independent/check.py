#!/usr/bin/env python3
"""Independent bounded source-interface, same-index and projection review."""
from pathlib import Path
import hashlib,json,subprocess,sys,itertools
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
PINS={
'research/adaptive87-current-cfold-cal-fact-replay/check.py':'e3969205ce72cc08c62544ea7acd072b95853c20499e1762bfe427019b4469ab',
'research/adaptive87-current-cfold-cal-fact-replay/receipt.json':'7db80dfe284e63d000ce93067e238c5d11e76373f2c1add1d680e018a1aac776',
'research/adaptive87-current-cfold-cal-fact-replay/README.md':'18e6060aec0840e6460504f05f6b8590619119d8a5bfe2249a5059fb57a0fde2',
'research/adaptive87-current-cfold-cal-fact-replay/pins.json':'d0d4fd6cd081205f2670381e905a48e8bbc1a2675119413829932104d0d0f9e9',
'research/adaptive87-current-cfold-index-power-interface-audit/check.py':'0a7dc0a0bf4251a936401bd0a00b74fc3075304f8193dd511d503f214b4231ff',
'research/adaptive87-current-cfold-index-power-interface-audit/result.json':'bea279767d3e43c5358664238312e108b895cf214ca62239e083382fe144bef5',
'research/adaptive87-current-cfold-index-power-interface-audit/README.md':'2bc983558a0a28d0f6408c64976b1280f4bf966f115aef3f861e9215ec6334b3'}
for n,h in PINS.items():assert hashlib.sha256((ROOT/n).read_bytes()).hexdigest()==h,n
for name in ('research/adaptive87-current-cfold-cal-fact-replay','research/adaptive87-current-cfold-index-power-interface-audit'):
 out=subprocess.run([sys.executable,'-I','-S','-B',str(ROOT/name/'check.py')],capture_output=True,check=True,timeout=30).stdout
 receipt='receipt.json' if name.endswith('fact-replay') else 'result.json'
 assert out==(ROOT/name/receipt).read_bytes(),name
p72=(ROOT/'Lean/DiophantineConsistency/Compact44/P72Exact.lean').read_text().split('theorem indices_ordinary ',1)[1].split(':= by',1)[0]
checks=['(hq3 : 3 ≤ q)','(hX : 0 < X)','(hy0 : 0 < y0)','(hYq : Y = q * (q * q) * y0)',
 '(hη : 0 < η)','(hc : c = η + Y * k)',"(hi' : 0 < i')",'(hf : 0 < f)',
 '(ha : a = X * Y + Y)','(hR26 : 26 ≤ R)',
 '(hny : 2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k)',
 '(hks : k = 2 * n + 4 * ((X * Y) * Y) * s)','(hRμ : R + 1 < μ)',
 '(hnmod : (2 * n) % μ = R + 1)','(hmy : ycoord m a = c)',
 '(hg : g * g = 1 + delta a * c * c)',
 "(hs' : (i' * c * c) * (i' * c * c) + delta a = delta a * (f * f))",
 'absdiff (f * f * (T * c)) (f * f * R + c)',
 'absdiff (f * f * (T * c) + u) (f * f * R + c)',
 '13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1']
for token in checks:assert token in p72,token
power=(ROOT/'Lean/DiophantineConsistency/ArithmeticPellPowerRecovery.lean').read_text().split('theorem power_bound ',1)[1].split(':= by',1)[0]
for token in ['(hX : 16≤X)','(hY : 1≤Y)','(hr : 2≤r)','(hck : c=k*Y+eta)',
 '(hkez : k=eta+zeta)','(hz : 0<zeta)','(hc : c=ycoord (2*r+1) (Y*(X+1)))',
 '(hk : k=2*ycoord (r+1) (2*(X*Y*Y-1)+1))','Exp.exp (2*r+1)<Y']:assert token in power,token
# Independently verify modular projection algebra in a free integer ring.
N=8
def var(i):return {tuple(int(j==i) for j in range(N)):1}
one={(0,)*N:1}
def add(a,b,sgn=1):
 c=a.copy()
 for m,v in b.items():c[m]=c.get(m,0)+sgn*v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():
   k=tuple(x+y for x,y in zip(m,n));c[k]=c.get(k,0)+v*w
 return {k:v for k,v in c.items() if v}
def times(a,n):return {k:v*n for k,v in a.items() if v*n}
q,L,d,W,X,a,c,gamma=map(var,range(N));H=add(times(one,3),mul(q,L));ac=mul(a,c)
D=add(add(add(add(d,mul(H,W)),X,-1),ac,-1),mul(H,gamma),-1)
qbalance=add(mul(q,D),mul(H,X),-1)
base=add(add(d,X,-1),ac,-1)
left=add(add(mul(H,add(D,mul(L,X),-1)),times(base,3),-1),mul(L,qbalance),-1)
assert left==times(mul(H,add(W,gamma,-1)),3)
# Signed absdiff mapping independently exercised in both sign orientations.
count=0;signs=set()
for f,T,c0,R,u in itertools.product(range(1,5),range(1,5),range(1,5),range(0,9),range(1,5)):
 A=f*f*T*c0;B=f*f*R+c0;V=A-B;y=V+u
 assert abs(A-B)**2==V**2 and abs(A+u-B)**2==y**2
 signs.add((V<0,y<0));count+=1
assert (True,True) in signs and (True,False) in signs and (False,False) in signs
print(json.dumps({'status':'PASS','pinned':PINS,'author_and_interface_receipts_reproduce':True,'P72_header_markers':len(checks),
 'projection_ring_identity':True,'signed_absdiff_cases':count,'sign_cases':sorted([list(x) for x in signs]),
 'limits':['Ordinary-integer mathematical/source review conditional on cited Pell theorem correctness; no Lean build.',
 'The theorem signatures were inspected, not newly kernel checked or graph-bound in an IΣ₁ model.',
 'The parent 88/30 equivalence, prior source/provider ancestry and formal iPRA bridge remain separate boundaries.']},indent=2,sort_keys=True))
