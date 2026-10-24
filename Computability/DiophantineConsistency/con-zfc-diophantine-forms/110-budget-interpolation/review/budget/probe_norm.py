import json,time
from sympy.polys.rings import ring
from sympy import ZZ
from pathlib import Path
root=Path(__file__).resolve().parents[2]
R,x,a,b,c,d,C,D=ring('x,a,b,c,d,C,D',ZZ)
z=R.zero

def mm(p,q):
 o=[z,z,z,z]
 for i in range(4):
  for j in range(4):o[i^j]+=p[i]*q[j]*(c if i&j&1 else 1)*(d if i&j&2 else 1)
 return o
T2=[x*x+c+d,2*x,2*x,R(2)]
J=[D*(T2[0]-a-b)-C]+[D*t for t in T2[1:]]
K=mm(J,J);K[0]-=4*(D*D*a*b+D*C*(a+b))
f=mm(K,K);f=[v-64*D**3*a*b*C*T2[i] for i,v in enumerate(f)]
g0=f[0]**2+d*f[2]**2-c*(f[1]**2+d*f[3]**2)
g1=2*(f[0]*f[2]-c*f[1]*f[3])
s=time.time();expected=g0*g0-d*g1*g1;print('expected',len(expected),time.time()-s,flush=True)
p=json.load(open(root/'guard/budget12_tau_centered.json'));nr=p['named_registers'];cuts={nr[k]:v for k,v in [('center',x),('scaled_Df',a),('scaled_Dtau',b),('scaled_Dmain',c),('scaled_Ag',d),('scaled_Cy',C),('delta',D)]}
cache={}
def get(i):
 if i in cuts:return cuts[i]
 if i in cache:return cache[i]
 n=p['nodes'][i];op=n[0]
 if op=='integer':o=R(n[1])
 elif op in ('add','sub','mul'):
  A,B=get(n[1]),get(n[2]);o=A+B if op=='add' else A-B if op=='sub' else A*B
 else:raise ValueError(n)
 cache[i]=o;return o
s=time.time();actual=get(p['output']);print('actual',len(actual),time.time()-s,expected==actual,flush=True)
