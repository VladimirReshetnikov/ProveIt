#!/usr/bin/env python3
"""Exact integer inputs, high-precision diagnostics; finite data are not proofs."""
import sys,csv,json,math
from pathlib import Path
import decimal_math as mp
from coefficients import read_coefficients, coefficients
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parent.parent
mp.mp.dps=int(sys.argv[1]) if len(sys.argv)>1 else 80
a=read_coefficients(ROOT/'data/coefficients_snapshot.txt'); N=len(a)-1
# Independent Python generator and stored October 1 ratios.
assert a[:81]==coefficients(80)
prior=list(csv.DictReader((ROOT/'data/prior_diagnostics.csv').open()))
for row in prior:
 n=int(row['n'])
 if n<=N: assert abs(mp.mpf(a[n])/a[n-1]-mp.mpf(row['ratio_a_n_over_a_n_minus_1']))<mp.mpf('1e-35')
row=[1]; B=[1]
for _ in range(N):
 new=[row[-1]]
 for x in row:new.append(new[-1]+x)
 row=new; B.append(row[0])
r=[mp.mpf(0)]+[mp.mpf(a[n])/a[n-1] for n in range(1,N+1)]
ws=[mp.mpf(0)]+[mp.lambertw(n) for n in range(1,N+1)]
def log_model(n):
 w=ws[n]; return n*(w-1+1/w)-1+w*w+3*w-mp.log(1+w)/2
rows=[]
for n in range(2,N+1):
 w=ws[n]; R=n/w+2+w/(2*(1+w)**2); delta=r[n]-R
 D=mp.log(a[n])-mp.log(B[n])-w*w-3*w
 E=mp.log(a[n])-log_model(n)
 # variance of the (n-1)-tilted law, divided by the squared mean
 v=r[n+1]/r[n]-1 if n<N else mp.nan
 vr=(v-w/(n*(1+w)))*n*n/w if n<N else mp.nan
 rows.append([n,w,r[n],delta,n*delta/w**2,D,E,mp.exp(D),v,vr])
with (ROOT/'data/diagnostics.csv').open('w') as f:
 wr=csv.writer(f);wr.writerow(['n','W','ratio','ratio_residual','n_residual_over_W2','log_Bell_normalization','log_smooth_normalization','Bell_normalization','relative_tilt_variance','variance_residual_n2_over_W'])
 for rr in rows:wr.writerow([mp.nstr(x,45) for x in rr])
# Independently verify the functional coefficient recurrence exactly through 35.
powers=[[1]+[0]*35]
for k in range(1,38):
 old=powers[-1]; powers.append([sum(a[j]*old[m-j] for j in range(m+1)) for m in range(36)])
for n in range(1,36): assert a[n]==sum(a[k]*powers[k+2][n-1-k] for k in range(n))
def coeff_power(power,m):
 b=[1]
 for s in range(1,m+1):
  num=sum(((power+1)*j-s)*a[j]*b[s-j] for j in range(1,s+1))
  assert num%s==0;b.append(num//s)
 return b[-1]
for nn in [10,100,1000,10000]:
 assert 2*coeff_power(nn-1,2)==nn*nn+3*nn-4
 assert 6*coeff_power(nn-2,3)==nn**3+9*nn*nn+14*nn-72
endpoint=[]
for n in [100,200,400,800,1200,1600]:
 if n>N:continue
 w=ws[n]; t=n/r[n]; d=w/(1+w); L=min(n-2,math.ceil(16*float(w)))
 S=mp.mpf(0); curvature=mp.mpf(0); localmax=mp.mpf(0)
 for m in range(L+1):
  b=coeff_power(n+1-m,m)
  S+=mp.mpf(a[n-1-m])*b/a[n]
  D=mp.mpf(a[n-1-m])*r[n]**(m+1)/a[n]
  pm=mp.exp(-t)*t**m/mp.factorial(m)
  curvature+=pm*D
  for j in [m]:
   local=mp.log(r[n-j]/r[n])+d*j/n
   localmax=max(localmax,abs(local))
 J=1-S
 pred=mp.exp(t)/r[n]*(1+((3+d)*t*t+2*d*t)/(2*n))+2/r[n]
 K=mp.exp(t)/r[n]*curvature
 endpoint.append(dict(n=n,L=L,W=str(w),endpoint_sum=str(S),complement=str(J),complement_residual_scaled=str((J-2/r[n])*n*n/w**2),balance_residual_scaled=str((1-pred)*n*n/w**4),curvature_error_scaled=str((curvature-1-d*(t*t+2*t)/(2*n))*n*n/w**4),local_window_error_scaled=str(localmax*n*n/w**3)))
(ROOT/'data/endpoint_diagnostics.json').write_text(json.dumps(endpoint,indent=2))
sweep=[]
for n in [100,200,400,800,1200,1600]:
 if n>N:continue
 w=ws[n]
 for cutoff in [8,12,16,24]:
  L=min(n-2,math.ceil(cutoff*float(w))); S=mp.mpf(0)
  for m in range(L+1):S+=mp.mpf(a[n-1-m])*coeff_power(n+1-m,m)/a[n]
  sweep.append({'n':n,'cutoff':cutoff,'L':L,'J':str(1-S),'scaled_J_residual':str((1-S-2/r[n])*n*n/w**2)})
(ROOT/'data/window_sweep.json').write_text(json.dumps(sweep,indent=2))
with (ROOT/'data/results_table.tex').open('w') as f:
 f.write(r'\begin{table}[htbp]\centering\small\begin{tabular}{rrrrr}\toprule'+'\n')
 f.write(r'$n$ & $r_n-R(n)$ & $n\Delta_n/w^2$ & $D_n^B$ & $a_n/(B_ne^{w^2+3w})$ \\ \midrule'+'\n')
 for rr in rows:
  if rr[0] in [100,200,400,800,1200,1600]:
   f.write(f'{rr[0]} & {float(rr[3]):.8f} & {float(rr[4]):.6f} & {float(rr[5]):.8f} & {float(rr[7]):.8f} '+r'\\'+'\n')
 f.write(r'\bottomrule\end{tabular}\caption{Exact integer inputs; high-precision decimal diagnostics. No limit is inferred from this finite table.}\end{table}'+'\n')
with (ROOT/'data/endpoint_table.tex').open('w') as f:
 f.write(r'\begin{table}[htbp]\centering\small\begin{tabular}{rrrr}\toprule'+'\n')
 f.write(r'$n$ & $L$ & $n^2(J_n-2/r_n)/w^2$ & $n^2\mathcal E_n/w^4$ \\ \midrule'+'\n')
 for e in endpoint:
  f.write(f"{e['n']} & {e['L']} & {float(e['complement_residual_scaled']):.8f} & {float(e['balance_residual_scaled']):.8f} "+r'\\'+'\n')
 f.write(r'\bottomrule\end{tabular}\caption{The complementary mass and the complete balance defect are tested separately. The $5$ suggested by the third column has a rigorous lower-bound explanation, but no matching upper-bound proof is supplied.}\end{table}'+'\n')

selected=[20,50,100,200,400,800,1200,1600]
for rr in rows:
 if rr[0] in selected:print(' '.join(mp.nstr(x,13) for x in rr[:8]))
print('ENDPOINTS',json.dumps(endpoint,indent=2)); print('Exact recurrence checks passed; N=',N)
