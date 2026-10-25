#!/usr/bin/env python3
"""Independent, assertion-free replay of normalized product-square circuits."""
from pathlib import Path
from collections import Counter
from hashlib import sha256
import json,gzip,random,copy,math
H=Path(__file__).resolve().parent
checks=0

def need(ok,label):
 global checks
 if not ok: raise ValueError(label)
 checks+=1

def evaluate(d,inputs,p=None):
 env=dict(inputs)
 for name,op,a,b in d['source']:
  av=env[a] if isinstance(a,str) else a; bv=env[b] if isinstance(b,str) else b
  value=av+bv if op=='+' else av-bv if op=='-' else av*bv
  env[name]=value if p is None else value%p
 return env

def closed(v,weight,p):
 J,F,alpha,i,T,w,s,n,eta,zeta=(v[x] for x in ['J','F','alpha','i','T','w','s','n','eta','zeta'])
 beta,K0,MC,MF=(v[x] for x in ['beta','K0','MC','MF'])
 q=beta*J+1;h=q-1;X=w*q;mu=q*q+1;Y=q**3*s;k=eta+zeta;c=k*Y+eta
 A=mu*Y*(X+1)+1;Delta=A*A-1;HH=4*A-5;V0=X*mu**2*Y**2;E=1+V0*(V0+1)*k*k
 R=(h*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J;e=k-R-1;C=q-F-alpha;B=(K0+w)*C-F
 U=i*c*c;a=Delta*U*U*E;F0=1+a;G=E*F0;Fsq=1+4*a*F0;Q=Delta*(Fsq-1)
 b=c*(T+alpha)-R;V=Fsq*b-c;Kpos=X*(3*c-2*X)+2;M=h*mu*mu*HH
 L=V*V if weight=='V2' else b*V
 Z=h*mu*mu*(HH*(n-L*B)+Kpos)-HH*(mu*mu*B+h*e)
 N=(Q-1)*Z*Z-M*M*G*(Q*V*V-1)
 pairs=dict(q=q,Y=Y,X=X,c=c,U=U,Delta=Delta,Dtau=E,DpI2=a,Df=F0,Dg=G,Fsqr=Fsq,Q=Q,cTR=b,V=V,Znum=Z,Mtot=M,N=N)
 return {k:x%p for k,x in pairs.items()}

# Each numeral is the source133 numeral, byte for byte. Container metadata may differ.
binding=json.loads((H/'coefficients/BINDING.json').read_text()); old_binding=json.loads((H/'source/equation_84.json').read_text())['coefficient_binding'];ports={}
for name,e in binding['ports'].items():
 data=(H/'coefficients'/e['file']).read_bytes();raw=gzip.decompress(data);val=int.from_bytes(raw,'little')
 need(sha256(data).hexdigest()==e['gzip_sha256'],name+' gzip')
 need(sha256(raw).hexdigest()==e['raw_sha256']==old_binding['ports'][name]['raw_sha256'],name+' exact numeral')
 need(val.bit_length()==e['bits'],name+' bits')
 ports[name]=val
need(ports['beta']>=31 and ports['beta']%2==1 and ports['K0']>0 and 0<ports['MC']<ports['beta']<ports['MF']<2*ports['beta'],'port box')

rng=random.Random(170081)
primes=[2**61-1,2**89-1,2**127-1]
reports=[]
for count,oldcount,degree in [(81,84,750),(82,85,560)]:
 d=json.loads((H/f'equation_{count}.json').read_text());old=json.loads((H/f'source/equation_{oldcount}.json').read_text())
 need(d['coefficient_binding']==binding,'binding complete')
 need(d['witnesses']==['J','F','alpha','i','T','w','s','n','eta','zeta'],'inputs')
 known=set(d['witnesses']+d['fixed_numerals']);deg={x:1 for x in d['witnesses']}|{x:0 for x in d['fixed_numerals']}
 for name,op,a,b in d['source']:
  need(name not in known and op in '+-*','unique gate '+name)
  need(all(not isinstance(v,str) or v in known for v in (a,b)),'topology '+name)
  da=deg[a] if isinstance(a,str) else 0;db=deg[b] if isinstance(b,str) else 0
  deg[name]=da+db if op=='*' else max(da,db);known.add(name)
 need(deg['N']==degree,'global degree upper')
 live={'N'}
 for name,op,a,b in reversed(d['source']):
  if name in live:live.update(v for v in (a,b) if isinstance(v,str))
 need(live==known,'all nodes live')
 need(len(d['source'])==count and dict(Counter(r[1] for r in d['source']))==d['operation_breakdown'],'count')
 need(d['parent_sha256']==sha256((H/f'source/equation_{oldcount}.json').read_bytes()).hexdigest(),'parent pin')
 # Distinct inputs include negative n-s, so translation is not accidentally tested only on positive shifted data.
 cases=[]
 for p in primes:
  for j in range(24):
   inp={x:rng.randrange(1,19) for x in d['witnesses']}|{x:v%p for x,v in ports.items()}
   if j==0:inp['n']=1;inp['s']=17
   env=evaluate(d,inp,p);ref=closed(inp,d['transport_weight'],p)
   need(all(env[k]==v for k,v in ref.items()),'independent formula')
   q=env['q'];trans=dict(inp);trans['Y']=q**3*inp['s'];trans['n']=inp['n']-inp['s'];trans.pop('s')
   prev=evaluate(old,trans,p)
   need(prev['Znum']==pow(q,3,p)*env['Znum']%p,'whole carrier normalization')
   need(prev['Mtot']==pow(q,3,p)*env['Mtot']%p,'whole denominator normalization')
   need(prev['N']==pow(q,6,p)*env['N']%p,'whole polynomial normalization')
   need(env['Fsqr']==pow(1+2*env['DpI2'],2,p),'doubled trace identity')
   need(env['Q']==4*env['Delta']**2*env['U']**2*env['Dg']%p,'G divides Q identity')
   cases.append((inp,p,env['N']))
 # Actual graph mutations must disagree with the independently computed complete polynomial.
 mutations=[('Y',2,'q2'),('fouraF0',2,3),('Q',3,'DpI2'),('brk',1,'-'),('Znum',1,'+'),('inside',1,'+')]
 for target,column,value in mutations:
  mutant=copy.deepcopy(d)
  for row in mutant['source']:
   if row[0]==target:row[column]=value;break
  need(any(evaluate(mutant,v,p)['N']!=want for v,p,want in cases),'mutation rejected '+target)
 reports.append(dict(file=f'equation_{count}.json',operations=count,degree_upper=degree,mutations_rejected=len(mutations)))

# Full polynomial rays, with exact modular coefficients (not sampled t values).
def padd(a,b,p,sgn=1):
 c=[0]*max(len(a),len(b))
 for i,v in enumerate(a):c[i]=v
 for i,v in enumerate(b):c[i]=(c[i]+sgn*v)%p
 while len(c)>1 and c[-1]==0:c.pop()
 return c

def pmul(a,b,p):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):
    c[i+j]=(c[i+j]+x*y)%p
 while len(c)>1 and c[-1]==0:c.pop()
 return c

ray_reports=[]
for p in primes:
 weights={x:rng.randrange(1,13) for x in ['J','F','alpha','i','T','w','s','n','eta','zeta']}
 q0=ports['beta']%p*weights['J']%p;k0=weights['eta']+weights['zeta'];t0=weights['T']+weights['alpha'];C0=q0-weights['F']-weights['alpha']
 for count,degree in [(81,750),(82,560)]:
  d=json.loads((H/f'equation_{count}.json').read_text());env={x:[0,v] for x,v in weights.items()}|{x:[v%p] for x,v in ports.items()}
  for name,op,a,b in d['source']:
   av=env[a] if isinstance(a,str) else [a%p];bv=env[b] if isinstance(b,str) else [b%p]
   env[name]=pmul(av,bv,p) if op=='*' else padd(av,bv,p,1 if op=='+' else -1)
  out=env['N'];need(len(out)-1==degree,'ray degree')
  if count==81:
   lead=2**14*pow(q0,506,p)*pow(weights['w'],46,p)*pow(weights['s'],108,p)*pow(weights['i'],20,p)*pow(k0,64,p)*pow(t0,4,p)*C0**2%p
  else:lead=-2**10*pow(q0,384,p)*pow(weights['w'],34,p)*pow(weights['s'],80,p)*pow(weights['i'],14,p)*pow(k0,46,p)*t0**2%p
  need(out[-1]==lead and lead!=0,'complete leading form')
  ray_reports.append(dict(operations=count,prime=str(p),degree=degree,leading_coefficient=str(lead)))

# Small Pell controls for the local doubling/extraction mechanism, independent of source satisfiability.
controls=0
for A in range(2,9):
 Delta=A*A-1
 for tau in range(2,9):
  for U in range(1,11):
   E=tau*tau;a=Delta*U*U*E;F0=1+a;G=E*F0;Fsq=1+4*a*F0;Q=Delta*(Fsq-1)
   need(Fsq==(1+2*a)**2 and Q==4*Delta*Delta*U*U*G,'integer double')
   for V in [1,2,5]:
    need(math.gcd(G,(Q-1)*(Q*V*V-1))==1,'integer coprimality')
    controls+=1
report=dict(status='PASS',checks=checks,circuits=reports,full_polynomial_rays=ray_reports,local_coprimality_controls=controls,scope='Audits transcription, exact numeral binding, local identities, degree and mutation rejection; not a consistency decision or substitute for the unbounded proof.')
(H/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json')).write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
