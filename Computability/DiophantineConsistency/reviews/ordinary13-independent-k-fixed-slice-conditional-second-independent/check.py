from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-fixed-slice-conditional-second-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-independent-k-fixed-slice-conditional')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());rows={n:(op,a,b) for n,op,a,b in g['source']}
for n,row in {'C':('-','qF','alpha'),'Bt':('-','g27','F'),'R':('+','g47','g50'),
'Z':('-','g32','Bt'),'Dstar':('+','g58','g59'),'g72':('-','g71','Q'),
'V':('-','g76','c'),'Fa':('-','y2','g82')}.items():assert rows[n]==row
# Exact graph controls for the fixed-slice carrier family, without huge ports.
checks=0
for beta in (15,21,31):
 for kp in range(1,(beta-3)//2+1):
  for h in (2,3):
   q=beta+1;K0=(h-1)*beta+kp;F=kp+1;alpha=beta-kp-1
   for k in (0,1,3):
    ell=q**7*k;tau=ell+1;r=tau-ell-k+(k*beta+1)*h
    v=[1,F-1,alpha-1,0,0,0,1,0,r,0,k,0,0];ports=[beta,K0,0,beta]
    e=dict(zip(g['witnesses'],v));e.update(zip(g['fixed_numerals'],ports))
    for n,op,x,y in g['source']:
     x=e[x] if isinstance(x,str) else x;y=e[y] if isinstance(y,str) else y
     e[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
    assert min(v)>=0 and e['C']==1 and e['Bt']==beta*h and e['Z']==beta*tau
    assert e['G']==q*(beta-kp)-1
    checks+=1
# The main Pell congruence and natural strong-period witness for small controls.
period_checks=0
for a in range(1,8):
 H=3+4*a;delta=a*a+H;A=a+2
 for c in range(2,7):
  f,t=1,0
  for j in range(1,c**8+1):
   f,t=A*f+delta*t,f+A*t
   if f%(c*c)==1 and t%(c*c)==0:break
  else:raise AssertionError((a,c))
  assert t>0 and t%(c*c)==0
  i=delta*(t//(c*c));I=i*c*c
  assert I*I==delta*(f*f-1)
  period_checks+=1
 x,y=1,0
 for j in range(20):
  assert (x-a*y-pow(2,j,H))%H==0
  x,y=A*x+delta*y,x+A*y
# Odd auxiliary Pell indices produce integral V and the stated unit identity.
for I in range(2,9):
 x,y=1,0
 for j in range(1,10):
  x,y=I*x+(I*I-1)*y,x+I*y
  if j%2:
   assert x%I==0
   for eps in (-1,1):
    V=eps*(x//I)
    assert y*y-I*I*(y*y-V*V)==1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduced':True,'graph_carrier_controls':checks,
 'strong_finite_period_controls':period_checks,'main_congruence_controls':True,
 'odd_auxiliary_norm_controls':True,'main_and_aux_conditions_remain_undecided':True,
 'lean_executed':False},sort_keys=True,indent=2))
