from pathlib import Path
import re,hashlib
D=Path(__file__).resolve().parents[2];draft=D/'research/trace74-boundary-natural-seed-draft/Trace74BoundaryNaturalSeed.lean';python=D/'research/trace74-boundary-31-seed/check.py';bridge=D/'research/trace74-boundary-recurrence-cast-draft/Trace74BoundaryRecurrenceCast.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(draft)=='d94229597d11921a7fb0a174334b6ff497836301e1a0a39ecbb8020f5a5d33f0' and sha(bridge)=='94d1c036f3cc94030b8f95395bc0f6274a823692d93c45a0c87e886571a58ea6' and sha(python)=='d46fcda0011422f6bd534bb45260f8d461f537a231ce9dcc8d1052107bbf21f1'
a=re.search(r'def S : ℕ := (0x[0-9a-f]+)',draft.read_text())[1];b=re.search(r"s=int\('([0-9a-f]+)',16\)",python.read_text())[1];S=int(a,16);assert S==int(b,16);X=2**31;Y=8*S;P=X*Y*Y

def offset(n,b):
 x,y=1,0
 for _ in range(n):x,y=(b+2)*x+(b+1)*(b+3)*y,x+(b+2)*y
 return x,y
def usual(a,n):
 x,y=1,0
 for _ in range(n):x,y=a*x+(a*a-1)*y,x+a*y
 return x,y
assert P>=1;first=2*(P-1)+1;assert first+2==2*P+1;assert offset(16,first)==usual(2*P+1,16);assert offset(31,Y*(X+1))==usual(Y*(X+1)+2,31);K=2*offset(16,first)[1];C=offset(31,Y*(X+1))[1];assert K*Y<C<K*Y+K;print('PASS same S, natural offsets and indices, finite interval independently in Python; no Lean')
