from pathlib import Path
from hashlib import sha256
import sys,json,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-shared-index-norm-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-independent-k-shared-index-norm-audit')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
src=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
for x in ['run 0 b=⟪1,0⟫','xcoord 0 b=1','ycoord 0 b=0','xcoord (time+1) b=','ycoord (time+1) b=']:
 assert x in src,x
exact=Path('research/ordinary13-eta-zero-p72-index-draft/P72ExactEtaNatural.lean.src').read_text()
for x in ['2 * ycoord n (2 * ((X * Y) * Y - 1) + 1) = k','ycoord m a = c','13 ≤ n ∧ n < m ∧ m = R ∧ 2 * n = R + 1']:
 assert x in exact,x
# Different implementation: power of the 2x2 Pell-step matrix.
def mul(A,B):
 return (A[0]*B[0]+A[1]*B[2],A[0]*B[1]+A[1]*B[3],A[2]*B[0]+A[3]*B[2],A[2]*B[1]+A[3]*B[3])
def pell(A,n):
 v=(1,0,0,1);m=(A,A*A-1,1,A)
 while n:
  if n&1:v=mul(v,m)
  m=mul(m,m);n//=2
 return v[0],v[2]
count=0
for n in (14,16,31,50,100):
 for q in (2*n+2,2*n+7):
  X=q;Y=q**3;M=X*Y*Y;a=X*Y+Y;R=2*n-1;mu=q**4
  tau,y=pell(2*M+1,n);k=2*y;g,c=pell(a+2,R);eta=c-Y*k
  assert tau*tau==1+M*(M+1)*k*k
  assert g*g==1+(3+4*a+a*a)*c*c
  assert y>=n and (y-n)%(2*M)==0
  assert 2*n+4*M*((y-n)//(2*M))==k
  assert n<R and R>=26 and (2*n)%mu==R+1 and R+q**3+q+1<=mu
  assert c>(Y+1)*k and eta>k
  assert q**(n-4)>4*6**(n-1)
  count+=1
assert 4**5>4*6**3
assert 'def betaNat : ℕ := 2^(67*8807)-1' in Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
print(json.dumps({'author_receipt_reproduced':True,'source_zero_index_and_exact_index_binders_checked':True,'independent_matrix_exponent_controls':count,'fixed_compact_q_expanded':False,'graph_rank_or_factor_zero_proved':False,'lean_executed':False},indent=2,sort_keys=True))
