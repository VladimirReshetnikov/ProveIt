#!/usr/bin/env python3
"""Independent direct-formula check of fixed-mod-three finalizer.
Source X/Y/cap come from the literal prefix; source encoding is a separate audit.
"""
import argparse,json,gzip,random,hashlib
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('circuit',type=Path);ap.add_argument('--fixed',type=Path);a=ap.parse_args();p=a.circuit
obj=json.loads(p.read_text());fpath=a.fixed or p.with_name('FIXED_COEFFICIENTS.json');binding=json.loads(fpath.read_text());fixed={}
for key,e in binding.items():
 raw=gzip.decompress((fpath.parent/e['file']).read_bytes());fixed[key]=int.from_bytes(raw[1:],'little')*(-1 if raw[0] else 1)
rng=random.Random(20261023);count=0
for prime in [1000000007,1000000009,998244353]:
 for case in range(120):
  v={k:(0 if case==0 else 1 if case==1 else -1 if case==2 else rng.randint(-30,30)) for k in obj['variables']}
  ev=[]
  for n in obj['nodes']:
   k=n['kind']
   if k=='variable':r=v[n['name']]
   elif k=='literal':r=int(n['value'])
   elif k=='fixed':r=fixed[n['name']]
   elif k=='add':r=ev[n['left']]+ev[n['right']]
   elif k=='sub':r=ev[n['left']]-ev[n['right']]
   elif k=='mul':r=ev[n['left']]*ev[n['right']]
   else:raise ValueError(k)
   ev.append(r%prime)
  named={k:ev[i] for k,i in obj['named_nodes'].items()};mod=lambda z:z%prime
  vt=v['t'] if 't' in v else v['f'];vg=v['g0'] if 'g0' in v else v['g'];vk=v['k0'] if 'k0' in v else v['k']
  b=mod(6*vt+4);g=mod(b*vg);k=mod(b*(3*vk+2))
  X,Y,cap=named['X'],named['Y'],named['cap'] if 'cap' in named else named['Ccap']
  L=mod(v['l']*Y);U=mod(2*L*X);V=mod(4*g*v['w']*Y);W=mod(b*v['w'])
  A=mod(U*(V+1));B=mod(2*X+1);C=mod(6*v['c0']-1)
  Phalf=mod(L*X*U*V);P=mod(2*Phalf);K=mod(X+1+k*(P-2))
  S=mod(2*A-5);T=mod(3*W*C-2*(W*W-1));Q=mod((Phalf*Phalf-1)*K*K+1)
  Delta=mod(8*cap**3*g*K*K-g*g*(32*(C-K*L)**2*cap**3+g*g*K*K))
  xi=mod(v['z']*v['x']);D=mod((A*A-4)*C*C+4);E=mod(C*C*D*xi)
  F=mod(4*(A*A-4)*E*E+1);G=mod(2*(A+2)*(A-2)**2*E*E-1)
  Omega=mod(16*E);H=mod(C+(B-C)*F+Omega*F*v['y']);I=mod((G*G-1)*H*H+1)
  rho=mod(T+S*v['y']);Sigma=mod(xi*pow(S,5,prime));Theta=mod((rho**3-rho*S*S-S**3)*(rho*rho+23*S*S))
  seed=mod(b*Q);aa=mod(seed+(9*Delta-3)*(seed*v['z'])**2);dd=mod(D*F*I);Z=mod(Sigma*v['m']-Theta)
  result=mod((Z*Z-Sigma*Sigma*(aa+dd))**2-4*Sigma**4*aa*dd)
  assert result==ev[obj['output']],(prime,case)
  for key,val in [('b',b),('C',C),('A',A),('K',K),('Q',Q),('Delta',Delta),('Sigma',Sigma),('Theta',Theta),('D',D),('E',E),('F',F),('G',G),('H',H),('I',I)]:
   assert named[key]==val,(prime,case,key)
  count+=1
out={'circuit':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'independent_full_tail_cases':count,'status':'PASS','scope':'Direct finalizer formulas including every internal bridge register; source prefix is checked separately.'}
Path(__file__).with_name(p.stem+'_TAIL_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
