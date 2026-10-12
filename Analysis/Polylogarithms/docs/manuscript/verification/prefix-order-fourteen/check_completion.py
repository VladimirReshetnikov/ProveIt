"""Complete exact order-fourteen prefix certificate; fresh scratch outputs only.

The eventual-threshold construction is preserved from the quartic reconstruction
report. Its written theorem supplies the infinite proof; this script regenerates
its fixed-order constants and certifies every remaining rational determinant.
Requires SymPy, python-flint, NumPy and g++; run with assertions enabled.
"""
from pathlib import Path
from math import factorial,comb,isqrt
import array,hashlib,json,subprocess,struct,sys,time,tempfile
import numpy as np
import sympy as s
from sympy.functions.combinatorial.numbers import stirling
import flint
from flint import nmod_poly
V=Path(__file__).resolve().parent;S=Path(tempfile.mkdtemp(prefix='polylog-rank14-replay-'));P=7340033;A=7;B=80640;N=2*B;started=time.monotonic()
if sys.flags.optimize:raise RuntimeError('Assertions must be enabled.')
subprocess.run([sys.executable,str(V/'eventual_threshold.py'),'7','--output',str(S/'eventual_threshold_checks.json')],check=True)
assert all(P%d for d in range(2,isqrt(P)+1)) and P>4*B+4*A
threshold=json.loads((S/'eventual_threshold_checks.json').read_text());assert threshold['cases'][0]['a']==A and threshold['cases'][0]['sufficient_B']==B and threshold['cases'][0]['all_exact_checks_passed']
maximum=4*B+4*A;fac=[1]*(maximum+1);fi=[1]*(maximum+1)
for j in range(1,maximum+1):fac[j]=fac[j-1]*j%P
fi[-1]=pow(fac[-1],P-2,P)
for j in range(maximum,0,-1):fi[j-1]=fi[j]*j%P
e=fi[1:N+2];poly=nmod_poly(e,P);h=poly.inverse_series_trunc(N+1);assert (poly*h).truncate(N+1)==nmod_poly([1],P)
hcoeff=[int(h[j]) for j in range(N+1)];bern=[hcoeff[j]*fac[j]%P for j in range(N+1)];assert bern[0]==1 and bern[1]==P-pow(2,P-2,P) and all(bern[j]==0 for j in range(3,N+1,2))
print('FLINT complete Bernoulli inverse and product identity PASS',flush=True)
def multiply(left,right,stop):
 assert min(len(left),len(right))*(P-1)**2<2**64
 x=int.from_bytes(b''.join(v.to_bytes(8,'little') for v in left),'little');y=int.from_bytes(b''.join(v.to_bytes(8,'little') for v in right),'little')
 count=len(left)+len(right)-1;data=memoryview((x*y).to_bytes(8*count,'little'))
 return [int.from_bytes(data[8*j:8*j+8],'little')%P for j in range(min(stop,count))]
g=[1]
while len(g)<len(e):
 length=min(2*len(g),len(e));q=multiply(e[:length],g,length);q=[(-v)%P for v in q];q[0]=(q[0]+2)%P;g=multiply(g,q,length)
 print('Independent integer series length',length,flush=True)
assert multiply(e,g,len(e))==[1]+[0]*N and g==hcoeff
input_path=S/'rank14-bernoulli.bin';assert sys.byteorder=='little';data=array.array('I',bern)
with input_path.open('wb') as f:f.write(struct.pack('<4sIIII',b'R14B',P,A,B,N));data.tofile(f)
subprocess.run(['g++','-std=c++20','-O3','-march=native',str(V/'rank14_scan.cpp'),'-o',str(S/'rank14_scan.exe')],check=True)
subprocess.run([str(S/'rank14_scan.exe'),str(input_path),str(S/'rank14-residues-native.bin')],check=True)
f=np.asarray(fac,dtype=np.int64);invf=np.asarray(fi,dtype=np.int64);bv=np.asarray(bern,dtype=np.int64)
b_symbol,y=s.symbols('b y');coefficient_lists={}
for i in range(A):
 n=b_symbol-A+i;ordinary=s.Poly((2*n+2-y)*s.prod(4*n+2-y-r for r in range(2*i)),y)
 for k in range(i+1):
  hh=2*k+1;q=s.Poly(sum(ordinary.nth(j)*stirling(j,hh,kind=2) for j in range(hh,2*i+2)),b_symbol)
  coefficient_lists[i,k]=[int(c)%P for c in q.all_coeffs()]
def evaluate(coefficients,x):
 value=np.zeros_like(x)
 for c in coefficients:value=(value*x+c)%P
 return value
def laplace(m):
 count,dim,_=m.shape;dp=[np.ones(count,dtype=np.int64)]+[None]*((1<<dim)-1)
 for mask in range(1,1<<dim):
  columns=[j for j in range(dim) if mask>>j&1];row=len(columns)-1;value=np.zeros(count,dtype=np.int64)
  for position,j in enumerate(columns):value+=((-1)**(row+position))*m[:,row,j]*dp[mask^(1<<j)]
  assert len(columns)*(P-1)**2<2**63
  dp[mask]=value%P
 return dp[-1]
expected=[]
for b in range(A+1,2*A):
 m=np.zeros((1,b,b),dtype=np.int64)
 for t in range(b):
  for k in range(b):
   j=t+k-A+1
   if j<0:continue
   bracket=fac[2*b+2*t-2*A+1]*fi[2*b-2*k]%P
   if k<A:bracket=(bracket+fac[2*t+1]*fi[2*A-2*k])%P
   m[0,t,k]=bern[2*j]*fi[2*j]%P*bracket%P
 expected.extend(map(int,laplace(m)))
for start in range(2*A,B,2048):
 bb=np.arange(start,min(start+2048,B),dtype=np.int64);m=np.zeros((len(bb),A,A),dtype=np.int64)
 for i in range(A):
  n=bb-A+i;dc=[evaluate(coefficient_lists[i,k],bb) for k in range(i+1)]
  for ell in range(A):
   nn=2*(n-ell)+1;rr=2*bb-2*A+2+2*ell
   first=f[2*n]*invf[2*n-2*ell]%P;first=first*f[2*n+2*ell+2]%P;first=first*invf[2*n+2]%P;first=first*fi[2*ell+1]%P
   correction=np.zeros(len(bb),dtype=np.int64)
   for k in range(i+1):
    fall=f[nn]*invf[nn-2*k-1]%P;term=dc[k]*fall%P;term=term*(2*bv[2*bb-2*(A-i+ell+k)]%P)%P;correction=(correction+term)%P
   scale=f[rr]*invf[nn]%P;scale=scale*invf[2*n+1]%P*f[2*n]%P;scale=scale*invf[2*n+2]%P*f[2*n+1]%P;scale=scale*fi[2*ell+2]%P
   m[:,i,ell]=(2*first+scale*correction)%P
 expected.extend(map(int,laplace(m)))
 if start%8192<2048:print('Independent full subset determinants through',int(bb[-1]),flush=True)
native=(S/'rank14-residues-native.bin').read_bytes();magic,p,a,first,last,count=struct.unpack('<4sIIIII',native[:24]);observed=list(struct.unpack('<'+str(count)+'I',native[24:]));assert (magic,p,a,first,last,count)==(b'R14D',P,A,A+1,B-1,B-A-1)
assert expected==observed and all(expected)
output=dict(status='PASS',a=A,p=2*A,prime=P,sufficient_B=B,first_b=A+1,last_b=B-1,finite_cases=len(expected),zero_determinants=0,all_case_residues_match=True,Bernoulli_coefficients_checked=N+1,independent_Bernoulli_tables_match=True,integer_convolution_max_bound=(N+1)*(P-1)**2,integer_convolution_word_bits=64,laplace_signed_int64_bound=(2*A-1)*(P-1)**2,matrix_algorithms=['native numeric forward differences and Gaussian elimination','independent symbolic Stirling coefficients and division-free subset expansion'],bernoulli_algorithms=['FLINT inverse-series/product arithmetic','standard-library exact Kronecker integer inversion with complete product identity'],native_residue_sha256=hashlib.sha256(native).hexdigest(),native_source_digest_mode='lf-normalized',native_source_sha256=hashlib.sha256((V/'rank14_scan.cpp').read_bytes().replace(b'\r\n',b'\n')).hexdigest(),flint_version=flint.__version__,numpy_version=np.__version__,elapsed_seconds=round(time.monotonic()-started,3),scope='Every remaining finite order-fourteen source matrix is nonsingular over the prime field, with independently validated Bernoulli inputs and complete matching residue lists. Combined with the audited exact eventual theorem and B7=80640 this proves all b>=8 in the formal prefix model. Numerical arithmetic independence and Gaussian identities are not asserted.')

# Full regenerated mathematical payloads must agree with the preserved certificate.
for name in ("rank14-bernoulli.bin","rank14-residues-native.bin"):
 assert (S/name).read_bytes()==(V/name).read_bytes(),name
assert threshold==json.loads((V/"eventual_threshold_checks.json").read_text())
print("Preserved complete certificate reproduced; scratch",S,flush=True)

output["preserved_payloads_reproduced"]=True
(V/'rank14-completion-replay.json').write_text(json.dumps(output,indent=2)+'\n',encoding='utf-8');print('Complete independent order-fourteen scan PASS',flush=True)
