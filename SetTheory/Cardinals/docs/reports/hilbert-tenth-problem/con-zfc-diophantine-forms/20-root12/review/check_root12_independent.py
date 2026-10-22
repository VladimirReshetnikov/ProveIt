#!/usr/bin/env python3
"""Independent paired-trace norm and integer-Pell diagnostics."""
from pathlib import Path
import json, random, math
from collections import Counter
ROOT=Path(__file__).resolve().parents[1]
p=json.loads((ROOT/'amalgamation/main_root12_product.json').read_text())
rng=random.Random(20261022)

def run(values):
 out=dict(values)
 for n,op,a,b in p['source']:
  a=a if isinstance(a,int) else out[a];b=b if isinstance(b,int) else out[b]
  out[n]={'+' : lambda:a+b, '-':lambda:a-b,'*':lambda:a*b}[op]()
 return out
for trial in range(100):
 v={n:rng.randrange(-2,4) for n in p['witnesses']+p['fixed_numerals']}
 e=run(v)
 q=v['Bm1']*v['J']+1;cw=q-v['F']-v['alpha'];X=v['w']*q;Y=v['s']*q**3;E=X*Y;k=v['eta']+v['zeta'];c=k*Y+v['eta'];a=E+Y;H=4*a+3;delta=a*a+H
 R=((q-1)*(q-v['F'])+v['alpha'])*(q*q-1)+(v['MC']+q*v['MF'])*v['J']
 lf=E*k*Y;A=1+lf*(lf+k);I=v['i']*c*c;D=1+delta*I*I;Q=(delta*I)**2;d=Q-1
 z0=c+R*D;vv=c*v['T'];P=D*vv*vv+z0*z0;ee=Q*P-1;B=2*Q*vv*z0;M=2*(k*I*I+v['T']**2)
 S=2*M*(lf+k);L=H*S+1;G=1+delta*c*c;W=H*v['t']+L*(X+a*c)
 # Coefficients of cleared F_H(z), independent of quadratic-ring emitter.
 C0=H*H*(d*M*M*A-ee);q2=-2*d*H*H*(d*M*M*A+ee);q0=C0*C0+H**4*D*B*B
 coeff={8:d**4,6:2*d*d*q2,4:q2*q2+2*d*d*q0-4*D*H**4*B*B*d*d,2:2*q2*q0-8*D*H**4*B*B*d*C0,0:q0*q0-4*D*H**4*B*B*C0*C0}
 K=W*W-L*L*G;trace=[2,2*W]
 for n in range(2,9):trace.append(2*W*trace[-1]-K*trace[-2])
 norm=sum(ai*ai*K**i for i,ai in coeff.items())
 norm+=sum(ai*aj*K**j*trace[i-j] for i,ai in coeff.items() for j,aj in coeff.items() if i>j)
 Nk=k-v['h']*E-R;Nt=(v['Kconstant']+v['w'])*cw+q-v['F']-v['z']*(q-1)
 assert norm==e['Res12']
 assert Nk*Nt*(1+norm)-1==e[p['output']]
count=0
for I in range(2,201):
 D=I*I-1;sf=D;square=1
 for f in range(2,math.isqrt(D)+1):
  while sf%(f*f)==0:sf//=f*f;square*=f
 assert sf*square*square==D
 for x in range(2,I+1):
  z2,rem=divmod(x*x-1,sf)
  if not rem and math.isqrt(z2)**2==z2:base=(x,math.isqrt(z2));break
 x,z=1,0
 for n in range(1,101):
  x,z=base[0]*x+sf*base[1]*z,base[1]*x+base[0]*z
  if x%I==0:
   assert z%square==0
   count+=1
ledger=Counter(row[1] for row in p['source'])
assert len(p['witnesses'])==12 and len(p['source'])==123
assert ledger['*']==81 and ledger['+']+ledger['-']==42
receipt={'norm_check':'Independent five-coefficient expansion and paired-power trace recurrence, not builder quadratic-ring implementation','signed_assignments':100,'variables':12,'operations':123,'multiplications':81,'additions_subtractions':42,'pell_scan':{'I_range':[2,200],'fundamental_indices':[1,100],'divisible_first_coordinate_cases':count,'integrality_failures':0},'scope':'Supplementary exact finite diagnostics. The uniform proofs are separate; this does not construct an accepting K215 witness or newly verify the inherited compiler.'}
(ROOT/'review/ROOT12_INDEPENDENT_CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
