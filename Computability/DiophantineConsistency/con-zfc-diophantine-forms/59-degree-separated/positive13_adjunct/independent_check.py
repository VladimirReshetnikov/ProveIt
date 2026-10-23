#!/usr/bin/env python3
"""Stdlib-only independent adjunct identity, wiring and degree witness review."""
from pathlib import Path
from collections import Counter,defaultdict
import gzip,hashlib,json,random
R=Path(__file__).resolve().parent
def require(v,s):
 if not v:raise ValueError(s)
class P:
 def __init__(self,d=0):self.d={((0,)*8):d}if type(d)is int and d else{}if type(d)is int else{k:v for k,v in d.items()if v}
 def __add__(self,o):
  o=o if isinstance(o,P)else P(o);d=dict(self.d)
  for m,c in o.d.items():d[m]=d.get(m,0)+c
  return P(d)
 __radd__=__add__
 def __neg__(self):return P({m:-c for m,c in self.d.items()})
 def __sub__(self,o):return self+-o if isinstance(o,P)else self+P(-o)
 def __rsub__(self,o):return -self+o
 def __mul__(self,o):
  o=o if isinstance(o,P)else P(o);d=defaultdict(int)
  for m,c in self.d.items():
   for n,e in o.d.items():d[tuple(a+b for a,b in zip(m,n))]+=c*e
  return P(d)
 __rmul__=__mul__
 def __pow__(self,n):
  z=P(1)
  for _ in range(n):z=z*self
  return z
 def __eq__(self,o):return self.d==(o.d if isinstance(o,P)else P(o).d)
def var(i):return P({tuple(int(j==i)for j in range(8)):1})
M,C,V,y=[var(i)for i in range(4)];Q=M*C
Z=C*(V*V-1)+(Q-1)*y*(2-M*y)
require(M*Z==Q*V*V-(Q-1)*(M*y-1)**2-1,'universal quotient identity')
W,U,S,g,tau=[var(i)for i in range(5)]
N=(W*W+U*U*g*g-S*S*tau*tau)**2-4*W*W*U*U*g*g
prod=P(1)
for sg in [-1,1]:
 for st in [-1,1]:prod=prod*(W-sg*U*g-st*S*tau)
require(N==prod,'universal two-root norm identity')
U,H,l,b,G,z,k=[var(i)for i in range(7)];W=U*b+H*(U*l+z);A=1+l*(l+k);D=b*b-G
C2=U*U*D+2*U*H*b*z+H*H*(2*U*l*z+z*z-U*U*l*k-U*U)
rhs=4*U**4*H*H*l*l*D+4*U*U*H*b*l*C2+C2*C2-4*U**4*H*H*G*(l*k+1)
require((W*W+U*U*G-U*U*H*H*A)**2-4*W*W*U*U*G==rhs,'universal degree cancellation identity')
body=json.loads((R/'thirteen_positive_degree126.json').read_text());parent=json.loads((R/'upstream/low_degree/thirteen_positive_degree132.json').read_text());pin=json.loads((R/'PARENT_PIN.json').read_text())
require(hashlib.sha256((R/'upstream/low_degree/thirteen_positive_degree132.json').read_bytes()).hexdigest()==pin['parent_sha256'],'parent hash')
require(body['source'][:73]==parent['source'][:73],'unchanged authenticated parent prefix')
expected=[['M','+','a',1],['ap3','+','a',3],['Caux','*','ap3','r62'],['daux','-','Aaux',1],['V2','*','V','V'],['V2m1','-','V2',1],['Za','*','Caux','V2m1'],['My','*','M','y'],['twomMy','-',2,'My'],['dy','*','daux','y'],['Zb','*','dy','twomMy'],['Z','+','Za','Zb'],['Zguard','+',1,'Z'],['Nguard','+','N',1],['factor1','*','Nt','Nguard'],['factor2','*','factor1','strong'],['factor3','*','factor2','Zguard'],['out','-','factor3',1]]
require(body['source'][73:]==expected,'exact new suffix and unscaled guard')
rows=body['source'];known=set(body['witnesses']+body['fixed_numerals']);live={body['output']}
for n,op,a,b in rows:
 require(n not in known and op in '+-*','gate name/operator')
 require(all(type(x)is int or x in known for x in [a,b]),'topological order');known.add(n)
for n,op,a,b in reversed(rows):
 require(n in live,'gate liveness');live.update(x for x in [a,b]if type(x)is str)
require(set(body['witnesses']+body['fixed_numerals'])<=live,'leaf liveness')
require(len(body['witnesses'])==13 and len(rows)==body['operations']==91,'metric')
pins=json.loads((R/'READONLY_PINS.json').read_text())
for path,want in pins.items():require(hashlib.sha256((R/path).read_bytes()).hexdigest()==want,'read-only source pin: '+path)
binding=json.loads((R/body['coefficient_binding_file']).read_text());records={r['port']:r for r in binding['materialization']['files']};ports={};raw_hashes={}
for n,path in body['coefficient_payloads'].items():
 packed=(R/path).read_bytes();raw=gzip.decompress(packed);rec=records[{'K0':'K','MF':'MF_source'}.get(n,n)]
 require(hashlib.sha256(packed).hexdigest()==rec['gzip_sha256']and hashlib.sha256(raw).hexdigest()==rec['sha256'],'complete coefficient port hashes')
 ports[n]=int.from_bytes(raw,'little');raw_hashes[n]=hashlib.sha256(raw).hexdigest()
require(ports['beta']==2**590069-1,'actual complete package coefficient scale')

def uadd(a,b,p,sgn=1):
 c={k:v for k,v in a.items()}
 for k,v in b.items():c[k]=(c.get(k,0)+sgn*v)%p
 return {k:v for k,v in c.items()if v}
def umul(a,b,p):
 c=defaultdict(int)
 for i,v in a.items():
  for j,w in b.items():c[i+j]=(c[i+j]+v*w)%p
 return {k:v for k,v in c.items()if v}
rays=[]
for p,scale in [(1000003,2),(1000033,3),(1000037,4)]:
 vals={n:{0:v%p}for n,v in ports.items()};vals.update({n:{1:scale if n=='t'else 1}for n in body['witnesses']})
 for n,op,a,b in rows:
  a={0:a%p}if type(a)is int else vals[a];b={0:b%p}if type(b)is int else vals[b]
  vals[n]=umul(a,b,p)if op=='*'else uadd(a,b,p,1 if op=='+'else-1)
 require(max(vals['N'])==68 and max(vals['strong'])==34 and max(vals['Z'])==22 and max(vals['out'])==126,'degree ray')
 require(vals['out'][126]==vals['Nt'][2]*vals['N'][68]*vals['strong'][34]*vals['Z'][22]%p,'independent leading product')
 rays.append({'prime':p,'t_scale':scale,'degree':126,'nonzero_leading_coefficient':vals['out'][126]})
# Exact algebra behind small-negative-norm descent, with no bounded-search claim.
m,x,y=[var(i)for i in range(3)]
xnew=m*x-(m*m-1)*y;ynew=m*y-x
require(xnew*xnew-(m*m-1)*ynew*ynew==x*x-(m*m-1)*y*y,'universal descent norm preservation')
receipt={'status':'PASS','positive_variables':13,'operations':91,'operation_counts':dict(Counter(row[1]for row in rows)),'exact_degree':126,'universal_ring_identities':4,'finite_field_lower_degree_witnesses':rays,'coefficient_tuple':'complete package39/44 tuple, beta=2^590069-1','parent_sha256':pin['parent_sha256'],'read_only_source_pins_checked':len(pins),'coefficient_raw_hashes':raw_hashes,'proof_sha256':hashlib.sha256((R/'PROOF.md').read_bytes()).hexdigest(),'circuit_sha256':hashlib.sha256((R/'thirteen_positive_degree126.json').read_bytes()).hexdigest(),'degree_upper_bound':'From the verified norm cancellation and degree bounds D0<=16,C2<=32,N<=68,Ns<=34,Z<=22,Nt<=2; see independent review prose.','limitations':'No inherited compiler or kernel claim. All-integer sign/completeness proof is reviewed in the accompanying prose.'}
print(json.dumps(receipt,indent=2))
