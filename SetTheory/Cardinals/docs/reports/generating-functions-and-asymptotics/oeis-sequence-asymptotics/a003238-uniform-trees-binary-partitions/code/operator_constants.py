from fractions import Fraction as F
from pathlib import Path
import json
from certified_interval import IV,S,expminus,binary_product,rational_power
U0=F(1,1024);RU=F(117,200)
if not 3**200<2**317:raise RuntimeError('rho upper bound fails')
D=[31,24,24,28];D7=[434,852,3306];C=[1]
for d in D:C.append(C[-1]*d)

def power_sum_upper(start,p):
 return rational_power(start,-p)+rational_power(start,1-p)/(p-1)

def get_constants():
 common=expminus(-2-U0)*3**10;tails=[];checks=[]
 for r,d in enumerate(D):
  pp=10-(r+1)*RU
  series=sum((rational_power(k,-pp) for k in range(3,32)),IV.of(0))+power_sum_upper(32,pp)
  val=common/(F(3,2)**(r+1)-1)*series
  if val.hi>=d*S:raise RuntimeError(('D constant',r,val.decimal()))
  checks.append({'type':'rho','r':r,'upper_interval':val.decimal(),'integer_bound':d})
  tails.append(common/(F(3,2)**(r+1)-1)*power_sum_upper(16,pp))
 for r,d in enumerate(D7):
  pp=3-(r+1)*RU
  series=sum((rational_power(k,-pp) for k in range(3,32)),IV.of(0))+power_sum_upper(32,pp)
  val=common/(128*F(3,2)**(r+1)-1)*series
  if val.hi>=d*S:raise RuntimeError(('D7 constant',r,val.decimal()))
  checks.append({'type':'7rho','r':r,'upper_interval':val.decimal(),'integer_bound':d})
 Cb=29*binary_product(U0)*2**36/127
 return tails,Cb,checks
if __name__=='__main__':
 tails,Cb,checks=get_constants()
 out={'status':'PASS','D':D,'D7':D7,'C':C,'checks':checks,'tail_constants':[x.decimal() for x in tails],'tail_integer_bounds':[x.integer_bounds() for x in tails],'Cb':Cb.decimal(),'Cb_integer_bounds':Cb.integer_bounds()}
 Path(__file__).with_name('OPERATOR_CONSTANTS_CERTIFICATE.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
