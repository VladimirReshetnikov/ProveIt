#!/usr/bin/env python3
"""Independent replay: does not import builder or execute any upstream script."""
from pathlib import Path
from collections import Counter
import json,gzip,hashlib,random,math
import sympy as sp
ROOT=Path(__file__).resolve().parent
pnames=['beta','K0','MC','MF'];syms=sp.symbols('beta K0 MC MF');V=['f','g','h','k','l','w','x','y','z','m']

def hashbytes(b):return hashlib.sha256(b).hexdigest()
def port_data():
 binding=json.loads((ROOT.parent/'coefficients/COEFFICIENT_BINDING.json').read_text());out={}
 for p in binding['ports']:
  raw=(ROOT.parent/'coefficients'/p['file']).read_bytes();assert hashbytes(raw)==p['sha256'];assert len(raw)==p['bytes']
  out[p['port']]=int.from_bytes(raw,'little')
 return {a:out[b] for a,b in [('beta','beta'),('K0','K'),('MC','MC'),('MF','MF_source')]}
def fixed_data(ports):
 b=json.loads((ROOT/'FIXED_BINDING.json').read_text());out={}
 for name,r in b['leaves'].items():
  z=(ROOT/r['file']).read_bytes();assert hashbytes(z)==r['gzip_sha256'];raw=gzip.decompress(z);assert hashbytes(raw)==r['sha256']
  val=r['sign']*int.from_bytes(raw,'little');out[name]=val
  if 'power_of_two'in r:assert val==1<<r['power_of_two']
  else:
   poly=sp.Poly(sp.sympify(r['expression'],locals=dict(zip(pnames,syms))),*syms)
   expected=sum(int(co)*math.prod(ports[n]**a for n,a in zip(pnames,mon)) for mon,co in poly.terms());assert val==expected
 return out

def literal(v,cert,fixed,ports,p):
 def mod(x):return x%p
 f,g,h,k,l,w,x,y,z,m=[v[n] for n in V];W=cert['maximum_weight'];Kcode=cert['Kcode'];H=cert['target_exponents']
 b=mod(1+3*f);base=mod(fixed['beta_source']*b*b);Dcode=0
 for row in cert['rows']:
  for t in row['terms']:
   poly=sp.Poly(sp.sympify(t['weighted_coefficient'],locals=dict(zip(pnames,syms))),*syms)
   co=sum(int(c)*math.prod(pow(ports[n],a,p) for n,a in zip(pnames,mon)) for mon,c in poly.terms())%p
   Dcode=mod(Dcode+co*pow(base,t['encoding_exponent'],p))
 # Direct finite geometric sums, deliberately independent from builder recurrence.
 powers=[1]
 for i in range(Kcode+2):powers.append(mod(powers[-1]*base))
 ell=mod(sum(powers[e] for e in cert['weights']));N0=powers[W+1];N1=mod(4*powers[Kcode+1]);N=mod(N0*N1)
 mask=mod(N0-1-(b-1)*ell);targets=mod(sum(powers[e] for e in H));Tcode=mod(mask+(base-2)*targets*N0)
 Jcode=mod(2*(pow(base,cert.get('padding_exponent',0),p)+g)**2*Dcode+sum(powers[1:Kcode+2]));Scode=mod(g+Jcode*N0);Rcode=mod((Scode+Tcode+1)*N+Tcode+1)
 X=mod((N-1)*Rcode);Y=mod(N*N);Ccap=mod(b*powers[W]);L=mod(l*Y);U=mod(2*L*X);vv=mod(4*g*w*Y);ww=mod(b*w)
 A=mod(U*(vv+1));B=mod(2*X+1);C=mod(B+(A-2)*h);Pn=mod(U*U*vv);KK=mod(X+1+k*(Pn-2));S=mod(2*A-5);T=mod(3*ww*C-2*(ww*ww-1))
 r1=mod((Pn*Pn-4)*KK*KK+4);Delta=mod(8*Ccap**3*g*KK*KK-g*g*(32*(C-KK*L)**2*Ccap**3+g*g*KK*KK));O=mod(f*f*l*l*Delta);xi=mod(z*x)
 D=mod((A*A-4)*C*C+4);E=mod(C*C*D*xi);F=mod(4*(A*A-4)*E*E+1);G=mod(2*(A+2)*(A-2)**2*E*E-1);Omega=mod(16*E);HH=mod(C+(B-C)*F+Omega*F*y);I=mod((G*G-1)*HH*HH+1)
 Sigma=mod(xi*pow(S,5,p));t=mod(T+S*y);Theta=mod((t**3-t*S*S-S**3)*(t*t+23*S*S));r0=mod(b*(1+(3*O-4)*b*b*z*z));r2=mod(D*F*I);weight2=mod(r0*(Pn*Pn+KK*KK+3));center=mod(Sigma*m-Theta)
 a0=mod(Sigma*Sigma*r0);a1=mod(Sigma*Sigma*r0*r0*r1);a2=mod(Sigma*Sigma*weight2*weight2*r2);vn=mod(center*center+a2-a0-a1);wn=mod(vn*vn+4*center*center*a2-4*a0*a1);out=mod(wn*wn-16*vn*vn*center*center*a2)
 return {'F10':out,'b':b,'base':base,'Dcode':Dcode,'N0':N0,'N1':N1,'N':N,'X':X,'Y':Y,'Ccap':Ccap,'Delta':Delta,'G':G,'H':HH,'r0':r0,'r1':r1,'r2':r2,'a0':a0,'a1':a1,'a2':a2,'Sigma':Sigma,'Theta':Theta}

def evaluate(body,vs,fixed,p):
 vals=[]
 for n in body['nodes']:
  k=n['kind']
  if k=='literal':a=n['value']
  elif k=='variable':a=vs[n['name']]
  elif k=='fixed':a=fixed[n['name']]
  else:
   a,b=vals[n['left']],vals[n['right']];a=a+b if k=='add' else a-b if k=='sub' else a*b
  vals.append(a%p)
 return vals

def degree(body,fixed,p):
 ds=[];ls=[]
 for n in body['nodes']:
  k=n['kind']
  if k=='variable':dd,ll=1,1
  elif k=='literal':dd,ll=0,n['value']%p
  elif k=='fixed':dd,ll=0,fixed[n['name']]%p
  else:
   a,b=n['left'],n['right']
   if k=='mul':dd,ll=ds[a]+ds[b],ls[a]*ls[b]%p
   else:
    dd=max(ds[a],ds[b]);aa=ls[a] if ds[a]==dd else 0;bb=ls[b] if ds[b]==dd else 0;ll=(aa+bb if k=='add' else aa-bb)%p
  ds.append(dd);ls.append(ll)
 out=body['output'];assert ls[out]!=0
 return {'prime':p,'degree':ds[out],'leading_coefficient':ls[out]}

def symbolic_source(body,cert):
 # Cut the circuit at its named base B and retain native ports as independent
 # indeterminates. This is an exact sparse-polynomial proof of D, not sampling.
 binding=json.loads((ROOT/'FIXED_BINDING.json').read_text())['leaves'];cache={}
 zero=(0,0,0,0,0);baseid=body['named_nodes']['base']
 def polyexpr(expr):
  poly=sp.Poly(sp.sympify(expr,locals=dict(zip(pnames,syms))),*syms)
  return {(0,)+tuple(mon):int(co) for mon,co in poly.terms() if co}
 def add(a,b,sgn=1):
  out=dict(a)
  for mon,co in b.items():out[mon]=out.get(mon,0)+sgn*co
  return {mon:co for mon,co in out.items() if co}
 def mul(a,b):
  out={}
  for ma,ca in a.items():
   for mb,cb in b.items():
    mon=tuple(x+y for x,y in zip(ma,mb));out[mon]=out.get(mon,0)+ca*cb
  return {mon:co for mon,co in out.items() if co}
 def go(i):
  if i in cache:return cache[i]
  if i==baseid:out={(1,0,0,0,0):1}
  else:
   n=body['nodes'][i];k=n['kind']
   if k=='literal':out={zero:n['value']} if n['value'] else {}
   elif k=='fixed':out=polyexpr(binding[n['name']]['expression'])
   else:
    assert k!='variable','Uncut variable in source code';a,b=go(n['left']),go(n['right'])
    out=mul(a,b) if k=='mul' else add(a,b,-1 if k=='sub' else 1)
  cache[i]=out;return out
 expected={}
 for row in cert['rows']:
  for t in row['terms']:
   term={(t['encoding_exponent'],)+mon[1:]:co for mon,co in polyexpr(t['weighted_coefficient']).items()}
   expected=add(expected,term)
 assert go(body['named_nodes']['Dcode'])==expected
 expected_targets={(e,0,0,0,0):1 for e in cert['target_exponents']}
 assert go(body['named_nodes']['targetsum'])==expected_targets
 return {'D_exact_symbolic_terms':len(expected),'target_sum_exact':True,'independent_native_port_indeterminates':4}

def identities():
 a,F,E,h,C,B,y,r,S=sp.symbols('a F E h C B y r S');Fm1=4*((2*a)**2-4)*E**2
 assert sp.expand((a-1)*Fm1-1-(2*(2*a+2)*(2*a-2)**2*E**2-1))==0
 assert sp.expand(C+(B-C)*F+16*E*F*y-(C+F*(B-C+16*E*y)))==0
 assert sp.expand((r**3-r*S*S-S**3)-(r*(r*r-S*S)-S*S*S))==0
 # Verify the collected norm against literal eight signed factors in a polynomial ring.
 X,u,v,w=sp.symbols('X u v w');aa,bb,cc=u*u,v*v,w*w;vn=X*X+cc-aa-bb;wn=vn*vn+4*X*X*cc-4*aa*bb
 rhs=sp.prod(X+e*u+f*v+g*w for e in [-1,1] for f in [-1,1] for g in [-1,1]);assert sp.expand(wn*wn-16*vn*vn*X*X*cc-rhs)==0
 return {'exact_G_rewrite':True,'exact_H_rewrite':True,'exact_cubic_rewrite':True,'exact_eight_factor_norm':True}

def main():
 ports=port_data();fixed=fixed_data(ports);report={'symbolic_tail_identities':identities(),'circuits':[]};rng=random.Random(730710)
 for file in sorted((ROOT/'generated').glob('sun10_*.json')):
  body=json.loads(file.read_text());certpath=ROOT/body['positional_certificate'];assert hashbytes(certpath.read_bytes())==body['certificate_sha256'];cert=json.loads(certpath.read_text())
  co=[]
  for row in cert['rows']:
   for t in row['terms']:
    poly=sp.Poly(sp.sympify(t['weighted_coefficient'],locals=dict(zip(pnames,syms))),*syms)
    co.append(sum(int(c)*math.prod(ports[n]**a for n,a in zip(pnames,mon)) for mon,c in poly.terms()))
  C=1+sum(abs(c) for c in co);assert len(co)==136;assert fixed['beta_source']>2048*C;assert body['beta_source_exponent']%2==0
  p=1000000007;checks=0
  for j in range(30):
   vs={n:rng.randrange(-100000,100001) for n in V};values=evaluate(body,vs,fixed,p);expected=literal(vs,cert,fixed,ports,p)
   for name,val in expected.items():assert values[body['named_nodes'][name]]==val,(file,name,j)
   checks+=1
  ds=[degree(body,fixed,p) for p in [1009,1000003,1000000007]];assert all(d['degree']==body['degree_upper_bound'] for d in ds)
  assert sorted(n['name'] for n in body['nodes'] if n['kind']=='variable')==sorted(V);counts=dict(Counter(n['kind'] for n in body['nodes'] if 'left'in n));assert counts==body['operation_counts'];assert sum(counts.values())==body['total_operations']
  report['circuits'].append({'file':file.name,'status':'PASS','degree':ds[0]['degree'],'operations':sum(counts.values()),'actual_weighted_coefficient_count':len(co),'absolute_sum_plus_one_bit_length':C.bit_length(),'beta_source_exponent':body['beta_source_exponent'],'strict_beta_gt_2048_C':True,'literal_source_and_tail_replays':checks,'degree_certificates':ds,'exact_source_polynomial_identity':symbolic_source(body,cert),'sha256':hashbytes(file.read_bytes())})
 report['status']='PASS';(ROOT/'VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
