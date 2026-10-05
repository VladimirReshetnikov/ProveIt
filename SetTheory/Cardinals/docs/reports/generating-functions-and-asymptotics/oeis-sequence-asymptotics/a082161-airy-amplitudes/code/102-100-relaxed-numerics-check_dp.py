import mpmath as mp,json,sys,time,hashlib
from pathlib import Path
mp.mp.dps=90
import argparse
parser=argparse.ArgumentParser(description="Optional exact-integer DP followed by uncertified numerical diagnostics")
parser.add_argument("max_n",nargs="?",type=int,default=3000)
args=parser.parse_args()
N=args.max_n
if not 10 <= N <= 10000:
 raise ValueError("max_n must be an integer from 10 through 10000")
print("NUMERICAL DIAGNOSTICS ONLY: no certified amplitude digits or interval bounds",flush=True)
A=mp.airyaizero(1)
base=Path(__file__).resolve().parent
formal=json.load(open(base/'endpoint_9.json'))
import sympy as S
a=S.symbols('a')
coefs={kind:[mp.mpf(str(S.N(S.sympify(z).subs(a,str(A)),95))) for z in formal[kind]['log_correction']] for kind in ['R','C']}
ratios={kind:[mp.mpf(str(S.N(S.sympify(z).subs(a,str(A)),95))) for z in formal[kind]['ratio']] for kind in ['R','C']}
# also wide-step extrapolate gamma from 15 sample points near end
samples=set([10,20,50,100,200,500,1000,2000,3000,4000,5000])|set(range(max(1,N-1400),N+1,100))
Rp=[1];Cpp=[0];Cp=[1];rprev=cprev=1;out=[]
start=time.time()
knownR=[1,1,3,16,127,1363,18628,311250,6173791,142190703]
knownC=[1,1,3,15,111,1119,14487,230943,4395855,97608831]
for n in range(1,N+1):
 R=[1]*(n+1);C=[1]*(n+1)
 for m in range(1,n+1):
  R[m]=(m+1)*(Rp[m] if m<n else 0)+R[m-1]
  C[m]=(m+1)*(Cp[m] if m<n else 0)+C[m-1]-(m-1)*(Cpp[m-1] if m<n else 0)
 r,c=R[-1],C[-1]
 if n<len(knownR) and (r!=knownR[n] or c!=knownC[n]):raise RuntimeError("initial exact sequence mismatch")
 if n in samples:
  z=mp.mpf(n)**(-mp.mpf(1)/3)
  row={'n':n}
  for kind,val,prev,alpha in [('R',r,rprev,mp.mpf(1)),('C',c,cprev,mp.mpf(3)/4)]:
   logu=mp.log(val)-mp.loggamma(n+1)-n*mp.log(4)-3*A*n**(mp.mpf(1)/3)-alpha*mp.log(n)
   corr=[sum(coefs[kind][j-1]*z**j for j in range(1,order+1)) for order in range(7)]
   gamma=[mp.exp(logu-co) for co in corr]
   q=mp.mpf(val)/prev/(4*n)
   ratio_errors=[q-sum(ratios[kind][j]*z**j for j in range(order+1)) for order in [3,4,5,6,7,8,9]]
   row[kind]={'logu':mp.nstr(logu,80),'gamma_corrected_0_to_6':[mp.nstr(g,60) for g in gamma],'q':mp.nstr(q,80),'ratio_error_3_to_9':[mp.nstr(g,50) for g in ratio_errors]}
  out.append(row)
  print(n,'gammaR',row['R']['gamma_corrected_0_to_6'][-1],'gammaC',row['C']['gamma_corrected_0_to_6'][-1],flush=True)
 Rp=R;Cpp,Cp=Cp,C;rprev,cprev=r,c
json.dump({'N':N,'precision':mp.mp.dps,'seconds':time.time()-start,'samples':out},open(base/f'exact_dp_{N}.json','w'),indent=2)
print('done',time.time()-start)
