"""Independent arithmetic diagnostics. Imports no upstream or local builder."""
from pathlib import Path
import collections,gzip,hashlib,json,math,random
import numpy as np
ROOT=Path(__file__).resolve().parent
RNG=random.Random(809732)
PORTS=['beta','K0','MC','MF']
def run(obj,vals,mod=None):
 vals=dict(vals)
 for n,o,x,y in obj['source']:
  x=vals[x] if isinstance(x,str) else x;y=vals[y] if isinstance(y,str) else y
  z=x+y if o=='+' else x-y if o=='-' else x*y
  vals[n]=z%mod if mod else z
 return vals

def plain(obj,v):
 q=v['beta']*v['J']+1;X=v['w']*q;Y=v['s']*q**3;E=X*Y;k=v['eta']+v['zeta'];c=k*Y+v['eta'];aa=E+Y;H=4*aa+3;delta=aa*aa+H;D=X+aa*c+v['gamma']*H;ell=E*k*Y
 R=((q-1)*(q-v['F'])+v['alpha'])*(q*q-1)+(v['MC']+q*v['MF'])*v['J']
 f=v['f'];T=v['T'];V=f*f*(c*T-R)-c if obj['squared_modulus'] else c*(T*f-1)-R*f*f
 I=v['i']*c*c;A0=delta*(f*f-1);tau=ell+v['r'] if obj['first_gap'] else v['tau'];y=V+v['u'] if obj['auxiliary_gap'] else v['y']
 N0=tau*tau-ell*(ell+k);N1=D*D-delta*c*c;Na=A0*(V*V-y*y)+y*y;Nk=k-v['h']*E-R;Nt=(v['K0']+v['w'])*(q-v['F']-v['alpha'])+q-v['F']-v['z']*(q-1)
 if obj['finalizer']=='normalized_scaled_product':
  S2=(delta*I)**2;Na=S2*(V*V-y*y)+y*y
  return N0*N1*Na*Nk*Nt*(delta*f*f-S2)-delta
 if obj['finalizer']=='ordinary_minimum3':return (N0*N1)**2+(Na*Nk*Nt-1)**2+(I*I-A0)**2-1
 if obj['finalizer']=='normalized_minimum4':return N0*N0+Na*Na+(f*f-delta*I*I)**2+(N1*Nk*Nt-1)**2-3
 return N0*N1*Na*Nk*Nt*(1+I*I-A0)-1

def polynomials(obj,coeff,p,seed):
 rr=random.Random(seed); vals={v:np.array([rr.randrange(1,19),rr.randrange(1,19)],dtype=np.int64) for v in obj['witnesses']}
 vals.update({v:np.array([coeff[v]%p],dtype=np.int64) for v in PORTS})
 def trim(a):
  a=a%p;ix=np.flatnonzero(a);return a[:int(ix[-1])+1] if len(ix) else np.array([0],dtype=np.int64)
 for n,o,x,y in obj['source']:
  x=vals[x] if isinstance(x,str) else np.array([x],dtype=np.int64);y=vals[y] if isinstance(y,str) else np.array([y],dtype=np.int64)
  if o=='*':z=np.convolve(x,y)
  else:
   z=np.zeros(max(len(x),len(y)),dtype=np.int64);z[:len(x)]+=x;z[:len(y)]+=y if o=='+' else -y
  vals[n]=trim(z)
 out=vals[obj['output']]
 if len(out)-1!=obj['exact_degree']:raise ValueError(('degree',obj['name'],len(out)-1,obj['exact_degree']))
 return {'prime':p,'seed':seed,'degree':len(out)-1,'leading_coefficient':int(out[-1])}

def pell(a,n):
 x,y=1,0;u,v=a,1;D=a*a-1
 while n:
  if n&1:x,y=x*u+D*y*v,x*v+y*u
  u,v=u*u+D*v*v,2*u*v;n//=2
 return x,y

def main():
 binding=json.loads((ROOT/'../native/COEFFICIENT_BINDING.json').read_text());coeff={};payloads=[]
 for port,filename in binding['binding'].items():
  rec=next(r for r in binding['ports'] if r['name']==filename.split('.')[0]);z=(ROOT/'../native'/filename).read_bytes();raw=gzip.decompress(z)
  if hashlib.sha256(z).hexdigest()!=rec['gzip_sha256'] or hashlib.sha256(raw).hexdigest()!=rec['sha256']:raise ValueError('binding')
  coeff[port]=int.from_bytes(raw,'little');payloads.append({'port':port,'sha256':rec['sha256'],'bits':coeff[port].bit_length()})
 if coeff['beta']!=(1<<binding['native_base_exponent'])-1 or coeff['MC']%4!=2:raise ValueError('tuple phase')
 records=[];raw_checks=0
 for path in sorted(ROOT.rglob('p*_degree*.json')):
  obj=json.loads(path.read_text());seen=set(obj['witnesses']+PORTS)
  for n,o,x,y in obj['source']:
   if n in seen or o not in ['+','-','*'] or any(isinstance(v,str) and v not in seen for v in [x,y]):raise ValueError('DAG')
   seen.add(n)
  needed={obj['output']}
  for n,o,x,y in obj['source'][::-1]:
   if n in needed:needed.update([x,y])
  if any(r[0] not in needed for r in obj['source']) or set(obj['witnesses']+PORTS)-needed:raise ValueError('liveness')
  if len(obj['source'])!=obj['operations']:raise ValueError('operations')
  for _ in range(150):
   v={n:RNG.randrange(-3,5) for n in obj['witnesses']+PORTS}
   if run(obj,v,1000003)[obj['output']]!=plain(obj,v)%1000003:raise ValueError('independent formula')
   raw_checks+=1
  records.append({'file':str(path.relative_to(ROOT)),'operations':len(obj['source']),'counts':dict(collections.Counter(r[1] for r in obj['source'])),'degree_checks':[polynomials(obj,coeff,p,seed) for p in [1000003,1000033,1000037] for seed in [8,80,808]]})
 # Exact squared-modulus reconstruction, with valid normalized strong square.
 examples=[]
 for a in [2,3,4,5]:
  for r in ([3,7] if a==2 else [3]):
   _,c=pell(a,r);delta=a*a-1
   # psi_a(r*c) divisible by c^2, from composition modulo c^2.
   f,ordn=pell(a,r*c);i=ordn//(c*c)
   if ordn!=i*c*c:raise ValueError('strong index division')
   S=delta*i*c*c;xx,y=pell(S,r)
   if xx%S:raise ValueError('odd quotient')
   V=xx//S;num=V+c+r*f*f;den=c*f*f
   if num%den:raise ValueError('square reconstruction')
   T=num//den
   if not (T>0 and V>1 and y>V and S*S*V*V-(S*S-1)*y*y==1 and V==f*f*(c*T-r)-c):raise ValueError('reconstruction')
   examples.append({'A':a,'R':r,'c':c,'T_bits':T.bit_length(),'f_bits':f.bit_length()})
 # A separate exact obstruction: deleting sqrt(D) loses a genuine condition.
 a,r,c,i=2,3,15,1;delta=a*a-1;S=delta*i*c*c;D=1+delta*i*i*c**4;V=D*(c-r)-c;y=4*S*S-1
 if math.isqrt(D)**2==D or S*S*V*V-(S*S-1)*y*y!=1:raise ValueError('radical obstruction')
 report={'all_checks_pass':True,'native_payloads':payloads,'circuits':records,'independent_formula_checks':raw_checks,'squared_modulus_examples':examples,'root_coupling_obstruction':{'A':a,'R':r,'c':c,'i':i,'S':S,'D_nonsquare':D,'T':1,'V':V,'y':y},'scope':'Finite identities and degree diagnostics only; inherited unbounded compiler/rank proofs remain dependencies.'}
 (ROOT/'SHORT_CHECK_RESULTS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
