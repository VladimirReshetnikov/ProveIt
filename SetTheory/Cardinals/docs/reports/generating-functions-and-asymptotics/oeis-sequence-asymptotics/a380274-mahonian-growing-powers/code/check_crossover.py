import mpmath as mp, json, time
from pathlib import Path
OUT = Path(__file__).resolve().parent
mp.mp.dps=90
Ns={20,22,40,42,80,82,160,162,320,322}
a_coeff=[mp.mpf(1),-mp.mpf(27)/25,mp.mpf(21087)/61250,-mp.mpf(19894023)/3062500,mp.mpf(18889730796483)/907878125000]
def theta(delta,q):
 total=mp.mpf(0);psi=mp.mpf(0)
 for m in range(200):
  x=mp.mpf(m)+delta
  mult=1 if x==0 else 2
  v=mult*mp.exp(-q*(x*x-delta*delta)/2)
  total+=v;psi+=v*(x**4-delta**4)
  if m>2 and v<mp.mpf('1e-85'): break
 return total,psi
rows=[]; endpoint_rows=[]; unnormalized_rows=[]; row=[1]; t=time.time()
for n in range(1,max(Ns)+1):
 old=row; row=[]; run=0
 for k in range(len(old)+n-1):
  if k<len(old):run+=old[k]
  if k>=n:run-=old[k-n]
  row.append(run)
 if n not in Ns:continue
 N=n*(n-1)//2; center=N//2; delta=mp.mpf(N%2)/2; C=row[center]
 sigma2=mp.mpf(n*(n-1)*(2*n+5))/72
 # Exact central ratio also checks the cancellation-sensitive curvature.
 xnext=delta+1
 neighbor=row[center-1]
 a_lattice=-2*sigma2*mp.log(mp.mpf(neighbor)/C)/(xnext*xnext-delta*delta)
 a4=sum(a_coeff[j]/mp.mpf(n)**j for j in range(5))
 for rho in [mp.mpf('0.2'),mp.mpf(1),mp.mpf(5)]:
  r=rho*sigma2
  exact=mp.mpf(0)
  for m in range(center+1):
   x=mp.mpf(m)+delta; co=row[center-m]
   term=(1 if x==0 else 2)*mp.exp(r*mp.log(mp.mpf(co)/C))
   exact+=term
   if m>10 and term<mp.mpf('1e-80'):break
  th,_=theta(delta,rho); curv,_=theta(delta,rho*a4); _,psi=theta(delta,rho)
  appr=curv-mp.mpf(81)*rho/(25*mp.mpf(n)**4)*psi
  log_exact = r*mp.log(C) + mp.log(exact)
  log_approx = r*(mp.loggamma(n+1)-mp.log(2*mp.pi*sigma2)/2)-rho*(mp.mpf(3)*n*n/400+mp.mpf(5883)*n/490000+mp.mpf(13963)/500000)+mp.log(th)-rho*delta*delta/2
  unnormalized_rows.append(dict(n=n,delta=str(delta),rho=str(rho),log_ratio=mp.nstr(log_exact-log_approx,30),n_log_ratio=mp.nstr(n*(log_exact-log_approx),30)))
  rows.append(dict(n=n,delta=str(delta),rho=str(rho),power=str(r),exact=mp.nstr(exact,35),theta=mp.nstr(th,35),relative_theta_error=mp.nstr(exact/th-1,20),relative_n4_error=mp.nstr(exact/appr-1,20),n5_relative_n4_error=mp.nstr(n**5*(exact/appr-1),20),curvature_discrete=mp.nstr(a_lattice,30),curvature_n4=mp.nstr(a4,30)))
 for scale in [1,2,4]:
  r=mp.mpf(n)**scale; exact=mp.mpf(1+2*delta); first=None; excess=mp.mpf(0)
  for m in range(1,center+1):
   co=row[center-m]
   term=2*mp.exp(r*mp.log(mp.mpf(co)/C))
   if first is None:first=term
   excess+=term
   if m>10 and term < first*mp.mpf('1e-80'):break
  exact+=excess
  endpoint_rows.append(dict(n=n,delta=str(delta),power_scale=scale,T=mp.nstr(exact,35),relative_gaussian_integral_error=mp.nstr(exact/mp.sqrt(2*mp.pi*sigma2/r)-1,25),log_modal_excess=mp.nstr(mp.log(excess),25),excess_to_first_shell=mp.nstr(excess/first,25)))
 print('n',n,'seconds',round(time.time()-t,2),flush=True)
with open(OUT / 'numerical_checks.json','w') as f:json.dump(rows,f,indent=2)
with open(OUT / 'endpoint_checks.json','w') as f:json.dump(endpoint_rows,f,indent=2)
with open(OUT / 'unnormalized_checks.json','w') as f:json.dump(unnormalized_rows,f,indent=2)
for row in rows:
 if row['rho']=='1.0':print(row)
