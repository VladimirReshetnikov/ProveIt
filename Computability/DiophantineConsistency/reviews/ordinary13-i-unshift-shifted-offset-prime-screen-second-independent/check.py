from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-i-unshift-shifted-offset-prime-screen-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for folder in ('research/ordinary13-i-unshift-shifted-offset-prime-screen','reviews/ordinary13-i-unshift-shifted-power-modular-second-independent'):
 p=Path(folder);assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
# Exact independent integer polynomial identity: the discrepancy is 8 times
# the power-match equation, with R=2n−1.
N=3;zero=(0,0,0)
def C(v):return {zero:v} if v else {}
def V(i):
 e=[0,0,0];e[i]=1;return {tuple(e):1}
def add(a,b,sgn=1):
 out=a.copy()
 for k,v in b.items():out[k]=out.get(k,0)+sgn*v
 return {k:v for k,v in out.items() if v}
def sub(a,b):return add(a,b,-1)
def mul(a,b):
 out={}
 for e,v in a.items():
  for f,w in b.items():
   k=tuple(x+y for x,y in zip(e,f));out[k]=out.get(k,0)+v*w
 return {k:v for k,v in out.items() if v}
L,h,n=[V(i) for i in range(3)];one=C(1);two=C(2);three=C(3);four=C(4);five=C(5);eight=C(8)
R=sub(mul(two,n),one);S=sub(add(mul(four,L),one),mul(three,h));rhs=mul(add(h,one),add(add(h,five),mul(four,R)))
match=sub(mul(sub(L,h),add(sub(mul(two,L),h),one)),mul(add(h,one),n))
assert sub(mul(S,S),rhs)==mul(eight,match)
# Independent enumeration of possible residues modulo 9 under n=2 (mod 3).
possible={}
for h0 in range(9):
 possible[h0]=[(L0,n0) for L0 in range(9) for n0 in range(9)
  if n0%3==2 and ((h0+1)*n0-(L0-h0)*(2*L0-h0+1))%9==0]
assert [h for h,v in possible.items() if not v]==[0,2,3,5,6]
# Binary Jacobi algorithm independently compares the prime classes; previous
# receipt provides independently trial-divided prime and fixed-port residue.
def jacobi(a,n):
 assert n>0 and n%2==1
 a%=n;ans=1
 while a:
  while a%2==0:
   a//=2
   if n%8 in (3,5):ans=-ans
  a,n=n,a
  if a%4==n%4==3:ans=-ans
  a%=n
 return ans if n==1 else 0
p=193707721;R0=55801659;eligible=[h0 for h0 in range(1,31) if possible[h0%9]]
bad=[];passed=[];values=[]
for h0 in eligible:
 x=((h0+1)*(h0+5+4*R0))%p;j=jacobi(x,p)
 assert (j==0 and x==0) or (j!=0 and pow(x,(p-1)//2,p)==(1 if j==1 else p-1))
 (bad if j==-1 else passed).append(h0);values.append([h0,x,j])
assert bad==[1,7,10,16,19,26,28] and passed==[4,8,13,17,22,25]
assert values[0][1]==(8*R0+12)%p
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_and_independent_prime_receipts_reproduced':True,'completed_square_exact_polynomial':True,
 'mod3_excluded_h_mod9':[0,2,3,5,6],'eligible_h':eligible,
 'independent_binary_jacobi_rows':values,'nonsquare':bad,'passes_necessary_test':passed,
 'scope':'fixed compact ports J=1, exact matching and rank; no zero decision or all-model proof.',
 'lean_executed':False},sort_keys=True,indent=2))
