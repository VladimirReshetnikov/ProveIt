"""Check asymptotic inverses against exact recurrence targets; no curve fitting."""
import mpmath as m
import json
m.mp.dps=100
N=500
row=[1]
counts=[1]
for n in range(1,N+1):
 sums=[0]*(len(row)+1)
 for j in range(len(row)-1,-1,-1):sums[j]=sums[j+1]+row[j]
 row=[0]+[row[k-1]+k*sums[k] for k in range(1,n+1)]
 counts.append(sum(row))

def coeff(w):
 c1=(20*w**3+86*w**2+128*w+67)/(24*(w+1)**3)
 c2=(1168*w**6+9968*w**5+34692*w**4+64536*w**3+69380*w**2+42208*w+11857)/(1152*(w+1)**6)
 c3=(756544*w**9+9366816*w**8+50906544*w**7+160729864*w**6+327216240*w**5+448817556*w**4+419091724*w**3+261418266*w**2+102110592*w+20174567)/(414720*(w+1)**9)
 return [c1,c2-c1*c1/2,c3-c1*c2+c1**3/3]

def H(x,J):
 w=m.lambertw(x/m.e);r=x/w
 return x*m.log(r)-x+r-m.mpf('1.5')*m.log(r)-m.log(w+1)/2-2-m.log(2*m.pi)/2+sum(c/r**(j+1) for j,c in enumerate(coeff(w)[:J]))
results=[]
for n in [50,100,200,500]:
 n=m.mpf(n);L=m.log(counts[int(n)]);w=m.lambertw(n/m.e);r=n/w
 for J in [0,1,2]:
  x=m.findroot(lambda x:H(x,J)-L,n)
  scale=(x-n)*r**(J+1)*(w+1)
  results.append({'n':int(n),'J':J,'inverse_error':m.nstr(x-n,25),'scaled_error':m.nstr(scale,25),'next_log_coefficient':m.nstr(coeff(w)[J],25)})
  print(n,J,m.nstr(x-n,12),m.nstr(scale,12),'expected',m.nstr(coeff(w)[J],12))
with open('inverse_checks.json','w') as f:json.dump(results,f,indent=2)
