from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta-zero-main-obstruction-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
checks=0
for q in range(2,20):
 for s in range(1,8):
  for w in range(15):
   X=q*w;Y=q**3*s;U=Y*q*q;H=3+4*Y*(X+1)
   for epsilon in (-1,1):
    L=abs(X-epsilon); assert 0<L<=X+1 and 3*q*q*L<H
    assert (3*q*q*L)%H!=0 and (U*L)%H!=0
    for t in (-7,0,5):
     # Exact certificate identity in integer arithmetic, with no divisibility hypothesis.
     assert 3*q*q*L-H*(q*q*L-4*(X+1)*t)==-4*(X+1)*(U*L-H*t)
    checks+=1
# Exact full graph main-root decomposition when eta=zeta=0.
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
def ev(w,p):
 d=dict(zip(g['witnesses'],w));d.update(zip(g['fixed_numerals'],p))
 for n,op,a,b in g['source']:
  x=d[a] if isinstance(a,str) else a;y=d[b] if isinstance(b,str) else b
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
for t in range(300):
 v=[(t*(i+3)+i*i+1)%9 for i in range(13)];v[0]+=1;v[9]=v[10]=0
 p=[(t*(j+2)+j)%7+1 for j in range(4)]
 d=ev(v,p);q=1+v[0]*p[0];Y=q**3*(v[7]+1);X=q*v[6];U=Y*q*q;H=3+4*Y*(X+1)
 assert d['c']==0 and d['kbase']==0 and d['Dstar']==U*X+H*(U*v[12]+d['R']+1)
 assert d['A1']==d['Dstar']**2-U**2
src=(D/'ZeroOrdinateMainObstruction.lean.src').read_text()
for token in ['theorem modulus_dvd_three','theorem modulus_excludes','Trace75IntegralTransport.natural_dvd_of_signed','theorem zero_ordinate_impossible','(hq : 2≤q) (hY : q^3≤Y) (hX : X=q*w)','(hnorm : z*z=ι (Y*(q*q))*ι (Y*(q*q)))']:
 assert token in src,token
print(json.dumps({'nonzero_small_multiple_controls':checks,'actual_graph_main_decompositions':300,'units_and_model_graph_binding_proved':False,'lean_executed':False},sort_keys=True,indent=2))
