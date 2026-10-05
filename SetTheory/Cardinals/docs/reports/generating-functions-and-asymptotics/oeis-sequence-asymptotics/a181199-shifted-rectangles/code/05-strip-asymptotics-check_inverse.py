from pathlib import Path
import sympy as s,json
t,l,a,d1,d2=s.symbols('t l a d1 d2')
w=1/t+a*l+(a*a*l-d1)*t+(-a**3*l*l/2+(a**3+a*d1)*l-a*d1-d2)*t*t
logw=l+s.series(s.log(s.expand(t*w)),t,0,4).removeO()
res=s.series(w-a*logw+d1/w+d2/(w*w)-1/t,t,0,3).removeO().expand()
if res!=0:raise RuntimeError(res)
out={'passed':True,'checked_orders':[0,1,2],'method':'direct formal substitution in logarithmic forward expansion'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
