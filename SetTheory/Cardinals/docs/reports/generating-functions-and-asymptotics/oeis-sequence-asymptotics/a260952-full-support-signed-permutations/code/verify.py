import math,json,itertools,sys
from fractions import Fraction
from pathlib import Path
import mpmath as mp
mp.mp.dps=100
OUT=Path(__file__).resolve().parents[1]/'data'
N=600
fac=[math.factorial(k) for k in range(N+1)]
c=[0]*(N+1)
for n in range(1,N+1): c[n]=fac[n]-sum(c[k]*fac[n-k] for k in range(1,n))
# Exact type B and D values from formal quotient.
b=[1]+[2**n*fac[n]-sum(c[k]*2**(n-k)*fac[n-k] for k in range(1,n+1)) for n in range(1,26)]
d=[(b[n]-3*c[n])//2 for n in range(2,26)]
assert b[:11]==[1,1,5,35,309,3287,41005,588487,9571125,174230863,3513016445]
assert d[:9]==[1,13,135,1537,19811,289073,4741923,86705417,1752264235]
# Exact shifted Stirling transform in integer scaling q=2.
S=[1]
a=[1]
for m in range(1,N+1):
 if m>1:
  S=[0]+[ (S[k-1] if k-1<len(S) else 0)+k*(S[k] if k<len(S) else 0) for k in range(1,m)]
 a.append(-sum(c[k]*2**(m-k)*S[k-1] for k in range(1,m+1)))
assert a[:11]==[1,-1,-1,-5,-35,-319,-3557,-46617,-699547,-11801263,-220778973]
# Direct signed-permutation enumeration, using the stated connectivity test.
brute=[]
for n in range(1,7):
 coeff=[0]*(n+1)
 for p in itertools.permutations(range(1,n+1)):
  for mask in range(1<<n):
   w=[-p[i] if mask>>i&1 else p[i] for i in range(n)]
   missing=False
   for cut in range(n):
    if all(abs(w[j])<=cut for j in range(cut)) and all(w[j]>cut for j in range(cut,n)):
     missing=True;break
   if not missing:coeff[mask.bit_count()]+=1
 pred=[fac[n]*math.comb(n,r)-sum(c[k]*fac[n-k]*math.comb(n-k,r) for k in range(1,n+1) if n-k>=r) for r in range(n+1)]
 assert coeff==pred,(n,coeff,pred)
 brute.append({'n':n,'negative_sign_coefficients':coeff})
# asymptotic checks
fall=lambda n,r:mp.fprod(n-j for j in range(r))
tau=mp.log(3)
coefs=[mp.mpf(1),-2*tau,-mp.mpf(9)/4*tau**2,-mp.mpf(27)/2*tau**3,-mp.mpf(1755)/16*tau**4,-mp.mpf(9099)/8*tau**5,-mp.mpf(907821)/64*tau**6]
late=[]
for m in [30,60,100,200,400,600]:
 lead=-mp.mpf(2)**(m+1)*fac[m]/(9*tau**(m+1))
 ratio=mp.mpf(a[m])/lead
 errs=[]
 for R in range(7):
  approx=sum(coefs[r]/fall(m,r) for r in range(R+1))
  errs.append({'order':R,'error':mp.nstr(ratio-approx,25),'scaled_error':mp.nstr((ratio-approx)*m**(R+1),25)})
 late.append({'m':m,'ratio':mp.nstr(ratio,30),'errors':errs})
# direct normalized counts evaluated at high precision
D=[mp.mpf(c[k])/fac[k] for k in range(N+1)]
def exactnorm(n,q):return q**n-mp.fsum(D[k]*q**(n-k)/math.comb(n,k) for k in range(1,n+1))
def sparse_coeff(lam):
 e=mp.exp(lam)
 return [e-1,-(1+lam**2/2)*e+1,e*(lam**4/8+lam**3/3+lam**2/2+lam-1)-lam+1,-(lam**6*e+8*lam**5*e+18*lam**4*e+40*lam**3*e+24*lam**2*e-96*lam*e+96*lam+192*e-192)/48]
sparse=[]
for lam in [mp.mpf('.1'),mp.mpf(1),mp.mpf(5),mp.mpc(1,mp.mpf('.5'))]:
 ff=sparse_coeff(lam)
 for n in [50,100,200,400,600]:
  exact=exactnorm(n,1+lam/n)
  errors=[mp.nstr((exact-sum(ff[j]/n**j for j in range(R+1)))*n**(R+1),25) for R in range(4)]
  sparse.append({'lambda':str(lam),'n':n,'normalized':mp.nstr(exact,25),'scaled_errors_R0_to_R3':errors})
# Exact half endpoint identity and q1 cancellation, and H expansion through4.
endpoint=[]
for n in [30,60,100,200,400,600]:
 for q in [mp.mpf(1),mp.mpf('1.01'),mp.mpf(2),mp.mpf('3.5')]:
  h=n//2
  L=1-mp.fsum(D[k]*q**(-k)/math.comb(n,k) for k in range(1,h+1))
  H=mp.fsum(q**j*D[n-j]/math.comb(n,j) for j in range(n-h))
  exact=exactnorm(n,q)/q**n
  assert abs(exact-(L-q**(-n)*H))<mp.mpf('1e-95')
  if q==1:assert abs(L-H)<mp.mpf('1e-95')
  HH=[1,q-2,2*q*q-2*q-1,6*q**3-2*q*q-3*q-5,24*q**4+6*q**3-12*q*q-9*q-32]
  endpoint.append({'n':n,'q':str(q),'H':mp.nstr(H,25),'Herror_times_n5':mp.nstr((H-sum(HH[j]/n**j for j in range(5)))*n**5,25)})
report={'status':'all_exact_assertions_passed','max_n':N,'first_B':b[:16],'first_D':d[:14],'first_A260952':a[:21],'signed_bruteforce':brute,'late':late,'sparse':sparse,'endpoint':endpoint}
(OUT/'verification.json').write_text(json.dumps(report,indent=2))
print(json.dumps({'status':report['status'],'max_n':N,'brute_nmax':6,'A260952_m600_ratio':late[-1]['ratio'],'late_m600_scaled_error_R4':late[-1]['errors'][4]['scaled_error'],'late_m600_scaled_error_R6':late[-1]['errors'][6]['scaled_error']},indent=2))
