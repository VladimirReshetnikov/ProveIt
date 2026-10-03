"""Non-certified numerical inverse replay; theoretical bracket is in the proof."""
import mpmath as mp,json
from pathlib import Path
import os
P=Path(os.environ.get("HISTORIC_TREE_OUTPUT_DIR", Path(__file__).parent));mp.mp.dps=100
I=Path(os.environ.get("HISTORIC_TREE_INPUT_DIR", P))
j=json.loads((I/'numerics_150dps.json').read_text());h=json.loads((I/'exact_values_0_202.json').read_text())
rho=mp.mpf(j['rho']);C=mp.mpc(j['C_real'],j['C_imag']);la=(13+mp.sqrt(71)*1j)/2
A={(0,0):mp.mpf(1),(1,0):mp.mpf(1),(0,1):mp.mpf(1)}
for d in range(2,5):
 for k in range(d+1):
  l=d-k;nu=k*la+l*mp.conj(la)
  A[k,l]=60*mp.fsum(A[i,t]*A[k-i,l-t] for i in range(k+1) for t in range(l+1) if (i,t) not in ((0,0),(k,l)))/((3-nu)*(4-nu)*(5-nu)-120)
def Q(x,d):
 return mp.re(1+mp.fsum(2*v*C**k*mp.conj(C)**l*rho**(k*la+l*mp.conj(la))*mp.exp(mp.loggamma(x+3-k*la-l*mp.conj(la))-mp.loggamma(x+3))/mp.gamma(3-k*la-l*mp.conj(la)) for (k,l),v in A.items() if 1<=k+l<=d and k!=l))
def F(x,d):return mp.log(30)+mp.loggamma(x+3)-(x+3)*mp.log(rho)+mp.log(Q(x,d))
rows=[]
for n in (75,100,150,200):
 L=mp.log(h[n]);solutions={str(d):mp.findroot(lambda x:F(x,d)-L,n) for d in (0,1,2,4)}
 Lm=(mp.log(h[n])+mp.log(h[n+1]))/2;xm=mp.findroot(lambda x:F(x,4)-Lm,n+mp.mpf('.5'))
 rows.append({'n':n,'threshold_hn_inverse_root_minus_n':{d:mp.nstr(x-n,40) for d,x in solutions.items()},'geometric_midpoint_inverse_root':mp.nstr(xm,40),'midpoint_ceiling_equals_exact_integer_inverse':int(mp.ceil(xm))==n+1})
assert all(x['midpoint_ceiling_equals_exact_integer_inverse'] for x in rows)
res={'status':'Exploratory numerical replay using fitted, non-interval-certified constants; no unconditional ceiling rule asserted','rows':rows}
(P/'inverse_validation.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
