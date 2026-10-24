#!/usr/bin/env python3
"""Read-only independent scalar12 front/whole-norm/graded-lex peer replay."""
from collections import Counter
import gzip
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
HERE=ROOT/'candidates/scalar-carrier12'
VARS=['j','C','z','h','r','v','w','T','c','n','t','s']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
OPS={'add','sub','mul'}

def need(ok,message):
 if not ok:raise ValueError(message)
def digest(x):return sha256(x).hexdigest()
class Poly:
 def __init__(self,x=0):self.t=dict(x)if isinstance(x,dict)else({():x}if x else{})
 @staticmethod
 def var(x):return Poly({(x,):1})
 def __add__(self,y):
  y=y if isinstance(y,Poly)else Poly(y);out=dict(self.t)
  for m,c in y.t.items():
   out[m]=out.get(m,0)+c
   if not out[m]:del out[m]
  return Poly(out)
 __radd__=__add__
 def __neg__(self):return Poly({m:-c for m,c in self.t.items()})
 def __sub__(self,y):return self+(-y)
 def __rsub__(self,y):return Poly(y)+(-self)
 def __mul__(self,y):
  y=y if isinstance(y,Poly)else Poly(y);out={}
  for m,c in self.t.items():
   for n,d in y.t.items():
    k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
  return Poly({m:c for m,c in out.items()if c})
 __rmul__=__mul__
 def __pow__(self,n):
  out=Poly(1)
  for _ in range(n):out=out*self
  return out

# Independent transcribed semantic registers. The carrier is checked in its
# expanded five-term form rather than the producer's factored schedule.
FRONT=[('J','6*j+1'),('qm','beta*J'),('q','qm+1'),('W0','12*w+4'),
 ('X','q*W0'),('Y','(2*v+1)*q**3'),('E','X*Y'),('a','E+Y'),('H','4*a+3'),
 ('Delta','a*a+H'),('F','(K0+W0)*C-z*qm'),
 ('R','(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J'),('k','R+1+h*E'),
 ('eta','c-Y*k'),('zeta','k-eta'),('coneU','cone_A*F'),('coneV','cone_B*C'),
 ('G','coneU*coneV-(q-coneU-coneV)**2'),('Peta','eta*zeta'),
 ('Pair','G*Peta-(t*t-G-Peta+1)**2'),('Dg','(3*Pair-4)*s*s+1'),
 ('I','s*r*c*c'),('Df','1+Delta*I*I'),('Q','Delta*Delta*I*I'),('delta','Q-1'),
 ('V','Df*(c-R+4*I*T)-c'),('Cy','Q*V*V-1'),('ell','E*Y'),
 ('Dt','1+ell*(ell+1)*k*k'),('K','X*(X+2*a*c)-1'),('S','I*H**5'),
 ('zcarrier','H*T+K'),
 ('Acarrier','zcarrier**5+3*H**2*zcarrier**3-19*H**3*zcarrier**2-57*H**5'),
 ('center','S*n-Acarrier'),('ra','9*S*S*Df'),('rb','81*S*S*Dt'),
 ('re','729*S*S*Dg'),('cn','S*S*Cy')]

def main():
 helper=HERE/'source/independent_norm_oracle.py'
 need(digest(helper.read_bytes())=='e368fc829ddbadf972c293b8283c5463f3641e0b6dc28e093515e9e1ccd28e83','known independent conjugate oracle')
 spec=importlib.util.spec_from_file_location('scalar12_peer_oracle',helper)
 oracle=importlib.util.module_from_spec(spec);spec.loader.exec_module(oracle)
 out={}
 for variant in ['rational','integral']:
  p=json.loads((HERE/(variant+'.json')).read_bytes());nodes=p['nodes'];nm=p['named_registers']
  stops={};covered=set();env={v:Poly.var(v)for v in VARS+PORTS}
  def expand(i):
   covered.add(i)
   if i in stops:return stops[i]
   row=nodes[i]
   if row[0]=='integer':return Poly(row[1])
   if row[0]in ['variable','coefficient']:return env[row[1]]
   a,b=expand(row[1]),expand(row[2])
   return a+b if row[0]=='add'else a-b if row[0]=='sub'else a*b
  for name,text in FRONT:
   if name=='cn'and variant=='integral':text='S*S*delta*Cy'
   need(expand(nm[name]).t==eval(text,{'__builtins__':{}},env).t,'own free-ring register '+name)
   stops[nm[name]]=Poly.var(name);env[name]=stops[nm[name]]
  x,a,b,e,c,d=[oracle.variable(i)for i in range(6)]
  values={i:oracle.Poly(r[1])for i,r in enumerate(nodes)if r[0]=='integer'}
  for name,value in [('center',x),('ra',a),('rb',b),('re',e),('cn',c)]:values[nm[name]]=value
  if variant=='rational':values[nm['ndelta']]=d
  for i in range(nm['x2'],len(nodes)):
   covered.add(i);row=nodes[i]
   if row[0]=='integer':continue
   u,v=values[row[1]],values[row[2]];values[i]=u+v if row[0]=='add'else u-v if row[0]=='sub'else u*v
  fraction=oracle.Poly({(0,0,0,0,1,-1):1})
  expected=d**8*oracle.norm_oracle(x,[a,b,e,fraction])if variant=='rational'else oracle.norm_oracle(x,[a,b,e,c])
  need(values[p['output']].t==expected.t and len(expected.t)==495,'own complete independent495-term norm')
  need(all(i in covered for i,r in enumerate(nodes)if r[0]in OPS),'every arithmetic node independently covered')
  order=['T','j','w','v','s','r','c','C','z','h','n','t'];lead=[]
  def key(m):return(sum(m),)+m
  for r in nodes:
   if r[0]=='integer':q=((0,)*12,Poly(r[1]))
   elif r[0]=='coefficient':q=((0,)*12,Poly.var(r[1]))
   elif r[0]=='variable':
    m=[0]*12;m[order.index(r[1])]=1;q=(tuple(m),Poly(1))
   else:
    u,v=lead[r[1]],lead[r[2]]
    if r[0]=='mul':q=(tuple(a+b for a,b in zip(u[0],v[0])),u[1]*v[1])
    elif key(u[0])>key(v[0]):q=u
    elif key(u[0])<key(v[0]):q=(v[0],-v[1]if r[0]=='sub'else v[1])
    else:q=(u[0],u[1]-v[1]if r[0]=='sub'else u[1]+v[1])
    need(bool(q[1].t),'own noncancelling leading induction at every gate')
   lead.append(q)
  mon,coefficient=lead[p['output']]
  if variant=='rational':
   ex={'j':576,'w':144,'v':144,'s':80,'r':80,'c':160,'T':16};want=2**1200*3**720*Poly.var('beta')**576
  else:
   ex={'j':704,'w':176,'v':176,'s':96,'r':96,'c':192,'T':16};want=2**1424*3**880*Poly.var('beta')**704
  need(mon==tuple(ex.get(v,0)for v in order)and coefficient.t==want.t,'own exact distinguished degree coefficient')
  counts=dict(Counter(r[0]for r in nodes if r[0]in OPS))
  need(sum(counts.values())==p['operations']==(145 if variant=='rational' else 141),'own operation count')
  out[variant]={'equation_sha256':digest((HERE/(variant+'.json')).read_bytes()),'operations':p['operations'],
    'degree':sum(mon),'whole_front_free_ring':True,'every_arithmetic_node_covered':True,
    'independent_norm_terms':len(expected.t),'all_gate_graded_lex_leading_nonzero':True,'selected_monomial':ex}
 binding=json.loads((HERE/'coefficients/BINDING.json').read_bytes())
 parent=ROOT/json.loads((HERE/'SOURCE_PINS.json').read_bytes())['coefficient_binding_source']
 need(binding==json.loads(parent.read_bytes()),'entire old six-port binding unchanged')
 payloads={}
 for name,pin in binding['payloads'].items():
  raw=gzip.decompress((HERE/'coefficients'/pin['file']).read_bytes())
  oldraw=gzip.decompress((parent.parent/pin['file']).read_bytes())
  need(raw==oldraw and digest(raw)==pin['raw_sha256'],'own byte-complete original coefficient '+name)
  payloads[name]=pin['raw_sha256']
 # Run reviewed author checks without permitting them to write candidate files.
 commands=[['python','-B',str(HERE/'check.py')],['python','-B','-O',str(HERE/'check.py')],
  ['python','-B',str(ROOT/'tools/build_scalar_carrier12.py'),'--check'],
  ['python','-B','-O',str(ROOT/'tools/build_scalar_carrier12.py'),'--check']]
 replay=[]
 for command in commands:
  p=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  need(p.returncode==0,'reviewed read-only replay failed: '+p.stdout.decode())
  replay.append({'command':command,'exit_code':0,'stdout_sha256':digest(p.stdout)})
 report={'status':'PASS','optimized_python':bool(sys.flags.optimize),'variants':out,'whole_six_coefficients':payloads,
  'proof_sha256':digest((HERE/'PROOF.md').read_bytes()),'checker_sha256':digest((HERE/'check.py').read_bytes()),
  'generator_sha256':digest((ROOT/'tools/build_scalar_carrier12.py').read_bytes()),'read_only_replays':replay,
  'ordinary_review':'Accepted after direct reading ofPROOF, PRIME_TWELVE, INTERPOLATION12§5-6 and signed quadratic folding. Nonzero bootstrap, prime-order separation, scalar p-adic carrier, arbitrary nonzero strong multiplier and fixed-I residue completeness are chronologically licensed.',
  'boundary':'Ordinary mathematical proof plus complete free-ring literal and exact degree certificates; inherited native/refutation calibration explicit. No new Lean/internal-ZFC completion.'}
 target=Path(__file__).with_name('scalar-carrier12-peer_OPTIMIZED.json'if sys.flags.optimize else'scalar-carrier12-peer.json')
 target.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
 print(json.dumps(report,indent=2))

if __name__=='__main__':main()
