#!/usr/bin/env python3
"""Independent standard-library verifier. Does not import build.py.

Exact identities, all fixed coefficients, structural prefix maps, complete
small-register transcription, liveness/counts, and a cancellation-resolved
degree certificate are checked. These finite checks do not replace PROOF.md.
"""
from pathlib import Path
from functools import lru_cache
from collections import Counter
import gzip,hashlib,json,math,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def require(ok,message):
 if not ok:raise ValueError(message)
def read(p):return json.loads((ROOT/p).read_text())
def sha(b):return hashlib.sha256(b).hexdigest()
def C(z):return {():z} if z else {}
def V(n):return {((n,1),):1}
def add(*xs):
 r={}
 for p in xs:
  for m,c in p.items():r[m]=r.get(m,0)+c
 return {m:c for m,c in r.items() if c}
def neg(x):return {m:-c for m,c in x.items()}
def sub(x,y):return add(x,neg(y))
def mul(*xs):
 r=C(1)
 for p in xs:
  q={}
  for m,a in r.items():
   for n,b in p.items():
    e=dict(m)
    for k,v in n:e[k]=e.get(k,0)+v
    e=tuple(sorted(e.items()));q[e]=q.get(e,0)+a*b
  r={m:c for m,c in q.items() if c}
 return r
def power(x,n):
 r=C(1)
 while n:
  if n&1:r=mul(r,x)
  n//=2
  if n:x=mul(x,x)
 return r
def subst(p,values):
 out=C(0)
 for mon,coeff in p.items():
  term=C(coeff)
  for n,e in mon:term=mul(term,power(values.get(n,V(n)),e))
  out=add(out,term)
 return out
def encode(p):return [[[[n,e] for n,e in m],c] for m,c in sorted(p.items())]

def verify_majorant():
 A,t,i=V('A'),V('t'),V('i');J=sub(mul(C(4),A),C(5));delta=sub(power(A,2),C(1));D=add(C(1),mul(delta,t));e=mul(i,J,t);F=add(C(1),mul(delta,D,power(e,2)))
 T=mul(i,t,add(mul(A,J,sub(mul(C(2),D),t)),mul(C(3),t),C(-4)))
 Q=add(mul(C(20),t,sub(mul(C(3),t),C(4)),power(A,3)),neg(mul(t,sub(mul(C(83),t),C(116)),power(A,2))),neg(mul(C(10),add(mul(C(7),power(t,2)),mul(C(-14),t),C(8)),A)),mul(C(109),power(t,2)),mul(C(-224),t),C(116))
 defect=sub(power(T,2),mul(C(4),D,F));require(defect==sub(mul(power(i,2),power(t,2),Q),mul(C(4),D)),'exact local majorant identity')
 shifted=sub(subst(Q,{'A':add(A,C(2)),'t':add(t,C(4))}),power(add(A,C(2)),2))
 require(len(shifted)==12 and all(c>0 for c in shifted.values()),'12 positive coefficients proving Q>A^2')
 require(shifted[()]==1344,'positive shift constant')
 # This checks why excluding C=1 is essential for this particular majorant.
 bad=subst(defect,{'A':C(3),'t':C(1),'i':C(1)})
 require(bad==C(-308),'C=1 negative control')
 require(len(T)==8 and len(defect)==13,'local expansion census')
 return dict(local_majorant_terms=8,defect_terms=13,positive_shift_terms=12,positive_shift_constant=1344,C1_negative_control=-308,Q_shift=encode(shifted),defect=encode(defect))

def verify_outer_identity():
 E,O,u,v,d,e=[V(n) for n in ['E','O','u','v','d','e']]
 a=sub(power(u,2),d);b=sub(power(v,2),e);th=sub(E,mul(O,add(u,v)));O2=power(O,2)
 lhs=sub(power(add(power(th,2),mul(O2,sub(a,b))),2),mul(C(4),O2,a,power(th,2)))
 B=add(power(E,2),neg(mul(C(2),E,O,add(u,v))),mul(O2,add(d,e)))
 rhs=add(power(B,2),mul(C(4),O2,u,v,B),mul(C(4),power(O,4),add(mul(d,power(v,2)),mul(a,e))))
 require(lhs==rhs,'cancellation-resolved outer identity')
 return dict(outer_identity_terms=len(lhs))

def verify_binding(label,obj):
 b=read(obj['fixed_binding']);require(b['profile']==label,'binding profile')
 ports={}
 for r in b['ports']:
  data=(ROOT/r['path']).read_bytes();raw=gzip.decompress(data)
  require(sha(data)==r['gzip_sha256'] and sha(raw)==r['raw_sha256'],'port payload hashes')
  value=int.from_bytes(raw,'little');require(value.bit_length()==r['bits'],'port bits');ports[r['name']]=value
 pv=[ports[n] for n in ['beta','K0','MC','MF']]
 recs=obj['coefficient_recipes'];values={}
 if isinstance(recs,list):rr={r['name']:r['terms'] for r in recs}
 else:rr=recs
 for name,terms in rr.items():
  values[name]=sum(t.get('integer',t.get('coefficient'))*math.prod(v**e for v,e in zip(pv,t.get('port_powers',t.get('powers')))) for t in terms)
 meta=obj['source_parameters'];values['base_scale']=1<<meta['base_exp']
 values['threshold_scale' if label=='h1868' else 'threshold_6480184']=1<<meta['threshold_exp']
 out={};rawbytes=0
 for r in b['fixed']:
  data=(ROOT/r['path']).read_bytes();raw=gzip.decompress(data);v=r['sign']*int.from_bytes(raw,'little')
  require(sha(data)==r['gzip_sha256'] and sha(raw)==r['raw_sha256'],'fixed payload hashes')
  require(abs(v).bit_length()==r['bits'] and v==values[r['name']],'fixed leaf reconstructed exactly')
  out[r['name']]=v;rawbytes+=len(raw)
 require({n['name'] for n in obj['nodes'] if n['kind']=='fixed'}==set(out),'all and only live fixed leaves bound')
 return out,dict(fixed_leaves=len(out),fixed_raw_bytes=rawbytes,port_bits={r['name']:r['bits'] for r in b['ports']})

def poly_at(obj,index,cuts):
 ns=obj['nodes']
 @lru_cache(None)
 def at(k):
  if k in cuts:return V(cuts[k])
  n=ns[k];t=n['kind']
  if t=='literal':return C(n['value'])
  if t in ['fixed','variable']:return V(t+'.'+n['name'])
  a,b=at(n['left']),at(n['right'])
  return add(a,b) if t=='add' else sub(a,b) if t=='sub' else mul(a,b)
 return at(index)

class TermInterner:
 def __init__(self):self.keys=[];self.ids={}
 def intern(self,key):
  if key not in self.ids:self.ids[key]=len(self.keys);self.keys.append(key)
  return self.ids[key]

def structural_terms(obj,cut,terms):
 ns=obj['nodes'];intern=terms.intern
 @lru_cache(None)
 def at(i):
  if i in cut:return intern(('variable',cut[i]))
  n=ns[i];k=n['kind']
  if k=='literal':return intern(('literal',n['value']))
  if k in ['variable','fixed']:return intern((k,n['name']))
  a,b=at(n['left']),at(n['right']);ka,kb=terms.keys[a],terms.keys[b]
  if ka[0]=='literal' and kb[0]=='literal':return intern(('literal',ka[1]+kb[1] if k=='add' else ka[1]-kb[1] if k=='sub' else ka[1]*kb[1]))
  if k=='mul':
   if ka==('literal',1):return b
   if kb==('literal',1):return a
   if ka==('literal',0) or kb==('literal',0):return intern(('literal',0))
  if k=='add':
   if ka==('literal',0):return b
   if kb==('literal',0):return a
  if k=='sub':
   if a==b:return intern(('literal',0))
   if kb==('literal',0):return a
  if k in ['mul','add']:a,b=sorted([a,b])
  return intern((k,a,b))
 return at

def verify_transcription(label,obj,parent):
 names=obj['named_nodes'];pn=parent['named_nodes'];ns=obj['nodes']
 expected_vars={'b','g','h','s','w','c','i','j','n'};actual=[n['name'] for n in ns if n['kind']=='variable'];require(set(actual)==expected_vars and len(actual)==9,'exact nine-variable set')
 require(poly_at(obj,names['C'],{})==add(V('variable.c'),C(1)),'C is the successor of c')
 terms=TermInterner();newtree=structural_terms(obj,{names['C']:'C'},terms);oldtree=structural_terms(parent,{},terms)
 pref=['A','B1','J','V0','a0','Omega','E0','R','N','capbase','B','Gsource','Usource','ell','targets']
 for name in pref:require(newtree(names[name])==oldtree(pn[name]),'prefix identity '+name)
 def check(name,cutnames,formula):
  cuts={names[n]:n for n in cutnames};p=poly_at(obj,names[name],cuts)
  require(p==formula,'exact register '+name)
 x={n:V(n) for n in names};v=lambda n:x[n];one=C(1)
 check('Am1',['A'],sub(power(v('A'),2),one))
 check('C2',['C'],power(v('C'),2))
 check('D',['Am1','C2'],add(one,mul(v('Am1'),v('C2'))))
 check('iC2',['C2'],mul(V('variable.i'),v('C2')))
 check('e0',['iC2','J'],mul(v('iC2'),v('J')))
 check('F',['Am1','D','e0'],add(one,mul(v('Am1'),v('D'),power(v('e0'),2))))
 check('Lambda',['C','D','A'],sub(add(one,mul(v('C'),v('D'))),v('A')))
 check('G',['A','F','Lambda'],add(v('A'),mul(v('F'),v('Lambda'))))
 check('Z',['B1','C'],add(v('B1'),mul(sub(V('variable.j'),one),v('C'))))
 check('H',['C','F','Z'],add(v('C'),mul(v('F'),v('Z'))))
 check('GH',['G','H'],mul(v('G'),v('H')))
 check('I',['GH','H'],add(one,sub(power(v('GH'),2),power(v('H'),2))))
 check('raw_a1',['D','F','I'],mul(v('D'),v('F'),v('I')))
 check('a1',['raw_a1'],mul(C(4),v('raw_a1')))
 check('Tmajor',['iC2','A','J','D','C2'],mul(v('iC2'),add(mul(v('A'),v('J'),sub(mul(C(2),v('D')),v('C2'))),mul(C(3),v('C2')),C(-4))))
 check('V1',['Tmajor','GH'],mul(v('Tmajor'),v('GH')))
 check('Theta',['E0','Omega','V0','V1'],sub(v('E0'),mul(v('Omega'),add(v('V0'),v('V1')))))
 check('Theta2',['Theta'],power(v('Theta'),2));check('Omega2',['Omega'],power(v('Omega'),2))
 check('polar_inner',['Theta2','Omega2','a0','a1'],add(v('Theta2'),mul(v('Omega2'),sub(v('a0'),v('a1')))))
 check('output',['polar_inner','Omega2','a0','Theta2'],sub(power(v('polar_inner'),2),mul(C(4),v('Omega2'),v('a0'),v('Theta2'))))
 # Exact source leading monomials are independent of the fixed coefficient ports.
 cuts={names['B']:'B',names['Usource']:'Us'};p=poly_at(obj,names['Gsource'],cuts);W=obj['source_parameters']['W']
 def weight(mon):return sum(e*(W if n=='Us' else 1 if n=='B' else 0) for n,e in mon)
 H=max(weight(m) for m in p);lead={m:c for m,c in p.items() if weight(m)==H}
 require(H==obj['source_parameters']['H'] and len(lead)==1,'source head isolated')
 require(next(iter(lead.values()))==1 and all(n in ['B','Us'] for n,e in next(iter(lead))),'source head equals a fixed monomial with coefficient one')
 return dict(prefix_register_identities=len(pref),new_register_identities=23,source_height=H,source_leader=encode(lead))

def check_topology(obj):
 ns=obj['nodes'];seen=set()
 for i,n in enumerate(ns):
  if n['kind'] in ['add','sub','mul']:require(0<=n['left']<i and 0<=n['right']<i,'topological edge')
 def visit(i):
  if i in seen:return
  seen.add(i);n=ns[i]
  if 'left'in n:visit(n['left']);visit(n['right'])
 visit(obj['output']);require(len(seen)==len(ns),'all nodes live')
 counts=dict(Counter(n['kind'] for n in ns if n['kind'] in ['add','sub','mul']))
 require(counts==obj['operation_counts'] and sum(counts.values())==obj['total_operations'],'exact live gate census')
 return counts

def degree_proof(obj,fixed):
 meta=obj['source_parameters'];r,nu,W=meta['r'],meta['nu'],meta['W'];a=r+4*nu+2
 om=5*a+2*W+3;v0=3*a+r+1;v1=18*a+r+24;d0=3*a+r+2;d1=31*a+2*r+48;E=a+4;B=2*om+d1
 require(B>max(2*E,E+om+v0,E+om+v1,2*om+d0),'unique Bsmall leader')
 terms=[2*B,2*om+v0+v1+B,4*om+d0+2*v1,4*om+2*v0+d1]
 degree=max(terms);require(degree==terms[0] and terms.count(degree)==1,'unique final leading summand')
 require(degree==86*r+328*nu+8*W+272==obj['exact_degree'],'exact cancellation degree formula')
 # At all variables=t, exact leading coefficients of the actual constant-bound
 # prefix are nonzero modulo these primes. Combined with the universal unique
 # leader proof this certifies degree attainment, not merely an upper estimate.
 residues=[]
 for prime in [1000000007,1000000009,998244353]:
  ns=obj['nodes'];memo={}
  def lead(k):
   if k in memo:return memo[k]
   n=ns[k];kind=n['kind']
   if kind=='variable':out=(1,1)
   elif kind in ['literal','fixed']:
    value=(n['value'] if kind=='literal' else fixed[n['name']])%prime;out=(0,value) if value else (-1,0)
   else:
    da,aa=lead(n['left']);db,bb=lead(n['right'])
    if kind=='mul':out=(da+db,aa*bb%prime) if aa and bb else (-1,0)
    elif da!=db:out=(da,aa) if da>db else (db,bb if kind=='add' else -bb%prime)
    else:
     cc=(aa+(bb if kind=='add' else -bb))%prime
     require(cc or da<=0,'unexpected prefix leading cancellation')
     out=(da,cc) if cc else (-1,0)
   memo[k]=out;return out
  nn=obj['named_nodes'];expected={'R':r,'N':nu,'A':a,'Omega':om,'V0':v0,'E0':E}
  for name,de in expected.items():require(lead(nn[name])[0]==de,'prefix exact degree '+name)
  A0=lead(nn['A'])[1];R0=lead(nn['R'])[1];Om0=lead(nn['Omega'])[1];Z0=2*R0%prime
  delta_lead=(60*65536*pow(A0,31,prime)*pow(Z0,2,prime))%prime
  output_lead=pow(Om0,4,prime)*pow(delta_lead,2,prime)%prime
  require(output_lead!=0,'actual specialized nonzero leading coefficient')
  residues.append(dict(prime=prime,degree=degree,leading_coefficient=output_lead))
 return dict(r=r,nu=nu,a=a,Omega_degree=om,V1_degree=v1,defect1_degree=d1,Bsmall_degree=B,four_summand_degrees=terms,exact_degree=degree,attainment=residues)

def main():
 pins=read('SOURCE_PINS.json')
 for p in pins['files']:require(sha((ROOT/p['path']).read_bytes())==p['sha256'],'authenticated inherited source '+p['path'])
 result=dict(status='PASS',majorant=verify_majorant(),norm=verify_outer_identity(),profiles={})
 for label,count,degree in [('compact2082',442,1520186),('h1868',456,1376378)]:
  obj=read('equations/'+label+'.json');parent=read('parents/'+label+'.json')
  require(obj['total_operations']==count and obj['exact_degree']==degree,'advertised metrics')
  require(obj['parent_source_hash']==sha(json.dumps(parent,sort_keys=True,separators=(',',':')).encode()),'exact parent binding')
  values,binding=verify_binding(label,obj);census=check_topology(obj);trans=verify_transcription(label,obj,parent);deg=degree_proof(obj,values)
  result['profiles'][label]=dict(variables=9,domain='positive',operations=count,operation_counts=census,binding=binding,transcription=trans,degree_certificate=deg)
 # Independent comparison of the authored constructor with both frozen circuits.
 with tempfile.TemporaryDirectory() as tmp:
  subprocess.run([sys.executable]+(['-O'] if sys.flags.optimize else [])+[str(ROOT/'build.py'),'--output',tmp],check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  for label in result['profiles']:
   require(json.loads((Path(tmp)/(label+'.json')).read_text())==read('equations/'+label+'.json'),'full deterministic reconstruction '+label)
 # Structural corruption must be detected by the independent transcription checker.
 damaged=read('equations/h1868.json');damaged['nodes'][damaged['named_nodes']['Tmajor']]['kind']='add'
 try:verify_transcription('h1868',damaged,read('parents/h1868.json'))
 except ValueError:pass
 else:raise ValueError('corrupt-majorant negative control accepted')
 result['negative_controls']=['C=1 has negative defect','altered majorant gate rejected']
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
