from pathlib import Path
import sympy as s,json
target=Path(__file__).resolve().parents[1]/'build'/'first_negative_values.json'
target.parent.mkdir(exist_ok=True)
out=[]
seen={row['m']for row in out}
for m in range(2,15):
 if m in seen:continue
 N=8*m;ix=list(range(1-m,m));d=len(ix)
 V=s.Matrix(d,d,lambda k,r:2*s.Rational(s.binomial(2*m,m+2*ix[k]-ix[r]),4**m)if abs(2*ix[k]-ix[r])<=m else 0)
 A=s.eye(d)-V;C=A.copy();C[0,:]=s.ones(1,d);inv=C.inv()
 matrices=[V];y=s.zeros(d,1);y[0]=1;h=[inv*y];lam=[s.S.One];real=[s.S.One];p=[s.S.Zero]
 record=[];found=None
 for n in range(1,N+1):
  matrices.append(s.Matrix(d,d,lambda k,r:V[k,r]*s.Rational((-2*(2*ix[k]-ix[r]))**n,s.factorial(n))))
  b=sum((matrices[j]*h[n-j]for j in range(1,n+1)),s.zeros(d,1));lam.append(sum(b))
  target=b-sum((lam[j]*h[n-j]for j in range(1,n+1)),s.zeros(d,1));rhs=target.copy();rhs[0]=0;hn=inv*rhs
  assert A*hn==target and sum(hn)==0;h.append(hn)
  real.append((-1)**(n//2)*lam[n]if n%2==0 else s.S.Zero)
  if n%2:assert lam[n]==0
  p.append(s.factor(real[n]-sum(k*p[k]*real[n-k]for k in range(1,n))/n))
  if n>2*m and n%2==0:
   record.append({'degree':n,'coefficient':str(p[n]),'sign':int(s.sign(p[n]))})
   if p[n]<0:found=n;break
 row={'m':m,'first_negative_after_missing_degree':found,'checked_through_degree':n,'coefficients_after_missing':record};out.append(row)
 target.write_text(json.dumps({'scope':'Exact finite orientation; no formula for all m','rows':out},indent=2)+'\n')
 print('m',m,'first negative after cancellation',found,'value approx',float(p[n]),flush=True)
