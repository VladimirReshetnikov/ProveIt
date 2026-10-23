"""Independent arithmetic diagnostics for locally authored shifted-carrier circuits.
Requires NumPy only for exact finite-field polynomial convolution. No upstream code.
"""
import json,random,hashlib
from pathlib import Path
import numpy as np
HERE=Path(__file__).resolve().parent
KINDS=['base','b','ac','ac2','half','half_aux']
EXPECTED={'base':(110,1081),'b':(111,1041),'ac':(114,1033),'ac2':(116,1025),'half':(119,1023),'half_aux':(124,1022)}
def get(x,e):return e[x] if isinstance(x,str) else x
def evaluate(packet,values,p):
 e=dict(values)
 for n,o,a,b in packet['source']:
  x,y=get(a,e),get(b,e);e[n]=(x+y if o=='+' else x-y if o=='-' else x*y)%p
 return e
def norm8(v,p):
 rad=[v['A']%p,v['G']%p,v['D']%p]
 def mul(a,b):
  c=[0]*8
  for i,x in enumerate(a):
   for j,y in enumerate(b):
    f=x*y
    for bit,r in enumerate(rad):
     if i&j&(1<<bit):f*=r
    c[i^j]=(c[i^j]+f)%p
  return c
 out=[1]+[0]*7
 for ta in [-1,1]:
  for ga in [-1,1]:
   for fa in [-1,1]:
    r=[v['W'],-v['HM']*ta,-v['L']*ga,0,0,0,0,0]
    r=[x*v['d']%p for x in mul(r,r)]
    r[0]=(r[0]-v['H']**2*(v['P']+v['U']-1))%p
    # H² Baux f, with Baux=2Qvb, v=cT; D*Baux²=4PU.
    r[4]=(r[4]+fa*v['H']**2*2*v['Q']*v['c']*v['T']*v['b'])%p
    out=mul(out,r)
 assert out[1:]==[0]*7
 return out[0]
def metadata(packet):
 names=set(packet['witnesses']+packet['fixed_numerals']);defs={}
 for n,o,a,b in packet['source']:
  assert n not in names and o in '+-*'
  assert all(not isinstance(x,str) or x in names for x in (a,b))
  names.add(n);defs[n]=(a,b)
 todo=[packet['output']] if 'output' in packet else [x for row in packet['comparisons'] for x in row if isinstance(x,str)]
 live=set()
 while todo:
  n=todo.pop()
  if n in live:continue
  live.add(n)
  if n in defs:todo.extend(x for x in defs[n] if isinstance(x,str))
 assert live==names
 led={'operations':len(defs),'multiplications':sum(r[1]=='*' for r in packet['source']),'additions_subtractions':sum(r[1]!='*' for r in packet['source'])}
 assert led==packet['ledger'];return led

def degree(packet,p,seed):
 rng=random.Random(seed)
 e={n:np.array([rng.randrange(1,p),rng.randrange(1,p)],dtype=np.int64) for n in packet['witnesses']}
 e.update({n:np.array([rng.randrange(1,p)],dtype=np.int64) for n in packet['fixed_numerals']})
 def g(x):return e[x] if isinstance(x,str) else np.array([x%p],dtype=np.int64)
 for n,o,a,b in packet['source']:
  x,y=g(a),g(b)
  if o=='*':r=np.convolve(x,y)%p
  else:
   r=np.zeros(max(len(x),len(y)),dtype=np.int64);r[:len(x)]+=x;r[:len(y)]+=y if o=='+' else -y;r%=p
  while len(r)>1 and r[-1]==0:r=r[:-1]
  e[n]=r
 return {n:len(e[n])-1 for n in ['Nk','Nt','N','polynomial']}

def main():
 if not __debug__:raise SystemExit('Assertions must remain enabled; do not use -O.')
 report={'scope':'Arithmetic diagnostics, not new kernel formalization or proof of consistency. Uniform exact-degree proof is in SHIFTED12_PROOF.md.','variants':{}}
 rng=random.Random(2026102305)
 for kind in KINDS:
  packet=json.loads((HERE/f'positive12_shift_{kind}_product.json').read_text());system=json.loads((HERE/f'positive12_shift_{kind}_system.json').read_text())
  meta=metadata(packet);metadata(system);assert(meta['operations'],packet['exact_degree'])==EXPECTED[kind]
  assert len(system['source'])==len(packet['source'])-4
  count=0
  for p in [251,65521,1000003]:
   for _ in range(60):
    vals={n:rng.randrange(-13,14) for n in packet['witnesses']+packet['fixed_numerals']}
    e=evaluate(packet,vals,p);assert e['N']==norm8(e,p)
    assert e['polynomial']==(e['Nk']*e['Nt']*(1+e['N'])-1)%p
    es=evaluate(system,vals,p);assert es['N']==e['N']
    count+=1
  for _ in range(150):
   vals={n:rng.randrange(-9,10) for n in packet['witnesses']+packet['fixed_numerals']}
   e=evaluate(packet,vals,4);assert e['N'] in [0,1]
  degrees=[degree(packet,p,s) for p,s in [(65521,199),(65519,502)]]
  for deg in degrees:assert deg=={'Nk':7,'Nt':2,'N':EXPECTED[kind][1]-9,'polynomial':EXPECTED[kind][1]}
  report['variants'][kind]={'ledger':meta,'system_ledger':system['ledger'],'independent_radical_assignments':count,'unit_congruence_assignments':150,'degree_diagnostics':degrees}
 # Tests of the exact strict bounds used for positive carrier translations.
 for _ in range(600):
  q=rng.randrange(16,100);X=q*rng.randrange(1,100000);Y=q**3*rng.randrange(1,100);E=X*Y
  R=rng.randrange(3*q+1,q**4-2);k=E+R+rng.randrange(1,10000);eta=rng.randrange(1,k);c=k*Y+eta
  a=E+Y;H=4*a+3;de=a*a+H;ell=E*k*Y;A=1+ell*(ell+k);I=rng.randrange(1,100)*c*c
  D=1+de*I*I;T=rng.randrange(1,10000)*10**rng.randrange(0,25);v=c*T;b=c+R*D;M0=k*(I*I+T*T)
  assert ell>2*c
  assert a*c-ell>0 and 2*((a+2)*c-ell)-k>0
  assert M0*M0*A>b*b
  assert ((2*M0)**2*A)>(b+v*(a+2)*I)**2
  assert ((a+2)*I)**2<4*D
 report['strict_translation_bound_assignments']=600
 # Synthetic eight-factor zeros. These are kernel witnesses, not machine runs.
 fixtures=0
 for S in range(2,10):
  for tau in range(2,6):
   H=7;M=13;g=17;f=2;c=1;T=3;v=3;b=5;Q=S*S;y=1;L=H*M+1;W=L*g+H*(M*tau+y)
   vals=dict(A=tau*tau,G=g*g,D=f*f,H=H,HM=H*M,L=L,W=W,d=Q-1,Q=Q,c=c,T=T,b=b,P=Q*f*f*v*v,U=Q*b*b)
   for p in [251,65521]:assert norm8(vals,p)==0
   fixtures+=1
 report['synthetic_radical_zero_witnesses']=fixtures
 # Recorded circuit hashes bind the diagnostics to exact delivered bytes.
 report['circuit_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(HERE.glob('positive12_shift_*.json'))}
 (HERE/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
