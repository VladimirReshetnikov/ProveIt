import json,math,pathlib
p=pathlib.Path(__file__).parent
exec((p/'check_renewal.py').read_text().split('rows=[]')[0])
def pols(x):return [(x*x+8)/6,x*(x**4+11*x*x-6)/72,(5*x**8+40*x**6-561*x**4-1074*x*x-4848)/6480,x*(5*x**10-5*x**8-1539*x**6+3339*x**4+15264*x*x+173988)/155520]
rows=[]
for m in [10,20,40]:
 for target in [-2,-1,0,1,2]:
  k=round(m+target*math.sqrt(m));x=(k-m)/math.sqrt(m);exact=float(success(m,k));phi=math.exp(-x*x/2)/math.sqrt(2*math.pi);ap=.5*math.erfc(x/math.sqrt(2))
  errors=[]
  for j,P in enumerate(pols(x),1):ap+=phi*P*m**(-j/2);errors.append(exact-ap)
  rows.append({'m':m,'k':k,'x':x,'exact':exact,'errors_orders1to4':errors,'scaled_error4':errors[-1]*m**2.5})
print(json.dumps(rows,indent=2));(p.parent/'checks'/'transition-exact-checks.json').write_text(json.dumps(rows,indent=2))
