#!/usr/bin/env python3
"""Independent finite algebra and graph checks; not a proof of consistency."""
from pathlib import Path
from collections import Counter
from math import gcd,isqrt
import json,random,hashlib,gzip
HERE=Path(__file__).resolve().parent
P=1000000007
SPECS={
 'equation_14_raw.json':(14,70,189,{'*':40,'+':17,'-':13}),
 'equation_14_reduced.json':(14,71,157,{'*':40,'+':17,'-':14}),
 'equation_13_anchored.json':(13,72,433,{'*':41,'+':19,'-':12}),
}
def need(ok,msg):
 if not ok:raise ValueError(msg)
def eval_graph(d,v,mod=None):
 e=dict(v)
 for n,op,a,b in d['source']:
  x=a if isinstance(a,int) else e[a];y=b if isinstance(b,int) else e[b]
  z=x+y if op=='+' else x-y if op=='-' else x*y
  e[n]=z%mod if mod else z
 return e

def hand(v,mode):
 J,F,alpha,z,h,i,T,s,w,eta,zeta,gamma,t=(v[x]for x in ['J','F','alpha','z','h','i','T','s','w','eta','zeta','gamma','t'])
 beta,K0,MC,MF=(v[x]for x in ['beta','K0','MC','MF'])
 q=beta*J+1;X=w*q;Y=s*q**3;E=X*Y;k=eta+zeta
 ell=E*k*Y;c=k*Y+eta;a=E+Y;H=4*a+3;delta=a*a+H;D=X+a*c+gamma*H
 A=1+ell*(ell+k);R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
 N1=D*D-delta*c*c;Nk=k-h*E-R;Nt=(K0+w)*(q-F-alpha)+(q-F)-z*(q-1)
 if mode=='root_saturated':
  I=i*c*c;W=delta*A*I*I;f2=v['f']**2;Q=delta*W;Ns=f2-W;G=A
 elif mode=='root_anchored':
  I=(a+2)*D*i*c*c;W=delta*A*I*I;f2=1+W;Q=delta*W;Ns=1;G=A*f2
 else:
  mult=A*i*(a+2)*D if mode=='triple' else A*i
  I=mult*c*c;S=delta*I;W=delta*I*I
  f2=1+W if mode=='triple'else v['f']**2
  Ns=1 if mode=='triple' else f2-W
  Q=delta*(f2-1)if mode=='reduced'else S*S
  G=A*f2 if mode=='triple'else A
 V=f2*(c*T-R)-c
 ep=(Q-1)*t*t-G*(Q*V*V-1)
 return N1*Nk*Nt*(3*ep+1)*Ns-1

def trim(a):
 while len(a)>1 and a[-1]%P==0:a.pop()
 return [x%P for x in a]
def add(a,b,sign=1):
 r=[0]*max(len(a),len(b))
 for j,x in enumerate(a):r[j]=x
 for j,x in enumerate(b):r[j]=(r[j]+sign*x)%P
 return trim(r)
def mul(a,b):
 r=[0]*(len(a)+len(b)-1)
 for j,x in enumerate(a):
  if x:
   for k,y in enumerate(b):r[j+k]=(r[j+k]+x*y)%P
 return trim(r)
def uni(d,ports=None):
 e={x:[0,1]for x in d['witnesses']}
 ports=ports or {'beta':3,'K0':5,'MC':7,'MF':11}
 e.update({x:[v%P]for x,v in ports.items()})
 for n,op,a,b in d['source']:
  x=[a%P]if isinstance(a,int)else e[a];y=[b%P]if isinstance(b,int)else e[b]
  e[n]=mul(x,y)if op=='*'else add(x,y,1 if op=='+'else -1)
 return e

def leader(v,mode):
 q=v['beta']*v['J'];k=v['eta']+v['zeta'];e=v['w']*v['s']*q**4;c=k*v['s']*q**3
 A=(v['w']*v['s']**2*k*q**7)**2;Lt=v['w']*(q-v['F']-v['alpha'])-v['z']*q
 common=v['gamma']*v['h']*v['T']**2*Lt
 if mode=='root_saturated':return -24*common*v['i']**4*A**3*e**9*c**11*v['f']**4
 if mode=='reduced':return -24*common*v['i']**2*A**3*e**7*c**7*v['f']**6
 if mode=='root_anchored':return 24*common*v['i']**8*A**5*e**29*c**27
 return 1536*common*v['i']**14*A**8*e**19*c**31

def graph_checks(d,spec,ports):
 n,ops,degree,breakdown=spec
 need(len(d['witnesses'])==n,'witness count')
 need(len(set(d['witnesses']))==n,'duplicate witness')
 seen=set(d['witnesses']+d['fixed_numerals']);parents={}
 for name,op,a,b in d['source']:
  need(name not in seen,'duplicate gate '+name);need(op in '+-*','bad operation')
  for x in (a,b):need(isinstance(x,int)or x in seen,'forward/unknown reference '+str(x))
  parents[name]=[x for x in (a,b)if isinstance(x,str)];seen.add(name)
 need(len(d['source'])==ops,'operation count');need(dict(Counter(r[1]for r in d['source']))==breakdown,'operation breakdown')
 live={d['output']};todo=list(live)
 while todo:
  x=todo.pop()
  for p in parents.get(x,[]):
   if p not in live:live.add(p);todo.append(p)
 need(live==seen,'dead coordinate/gate/port')
 # Upper degree: the complete N1 identity cancels its nominal degree22 terms.
 deg={x:1 for x in d['witnesses']};deg.update({x:0 for x in d['fixed_numerals']})
 for name,op,a,b in d['source']:
  da=0 if isinstance(a,int)else deg[a];db=0 if isinstance(b,int)else deg[b]
  deg[name]=da+db if op=='*'else max(da,db)
  if name=='N1':deg[name]=18
 need(deg[d['output']]==degree,'upper degree')
 u=uni(d,ports);need(len(u[d['output']])-1==degree,'univariate attained degree')
 mode='root_saturated'if'root_saturated'in d['name']else 'root_anchored'if'root_anchored'in d['name']else'reduced'
 sv={x:1 for x in d['witnesses']};sv['beta']=ports['beta']%P
 need(u[d['output']][-1]==leader(sv,mode)%P,'leading coefficient')
 return mode,{'variables':n,'operations':ops,'breakdown':breakdown,'degree':degree,'all_gates_inputs_ports_live':True,'univariate_leading_mod_1000000007':u[d['output']][-1]}

def pell(a,n):
 x,y=1,0
 for _ in range(n):x,y=a*x+(a*a-1)*y,x+a*y
 return x,y

def local_checks():
 # Elementary product formula, raw/reduced equality on the strong equation,
 # and all relevant modulo4 norm exclusions.
 rng=random.Random(953572)
 for _ in range(400):
  Q,G,V,t=(rng.randrange(-30,31)for _ in range(4))
  need(Q*(t*t-G*V*V)-t*t+G==(Q-1)*t*t-G*(Q*V*V-1),'fold identity')
 for a in range(4):
  delta=(a*a-1)%4
  for x in range(4):
   for y in range(4):need((x*x-delta*y*y)%4!=3,'negative unit residue')
 anchor_controls=0
 for a in range(2,8):
  delta=a*a-1
  for rank in range(1,5):
   D,c=pell(a,rank)
   need(D*D-delta*c*c==1,'main Pell sample')
   for A in range(2,11):
    for i in range(1,4):
     I=a*D*i*c*c;W=delta*A*I*I;F2=1+W;Q=delta*W;B=Q-1
     need(gcd(A,F2*B)==1,'first anchored coprimality')
     need(gcd(F2,B)==1,'base anchored coprimality')
     for L in range(-2,3):
      V=F2*L-c;Caux=Q*V*V-1
      need(gcd(A,Caux)==1,'first auxiliary coprimality')
      need(gcd(F2,Caux)==1,'root anchored coprimality');anchor_controls+=1
 # Small nontrivial coprime product controls. These exercise the lemma only,
 # and are not alleged ZFC consistency witnesses.
 accepted=0
 for S in range(2,20):
  for A in range(1,S+1):
   if S%A:continue
   for V in range(1,45):
    num=A*(S*S*V*V-1);den=S*S-1
    if num%den:continue
    t2=num//den;t=isqrt(t2)
    if t*t!=t2:continue
    tau=isqrt(A);need(tau*tau==A,'radicand extraction');need(t%tau==0,'integral quotient')
    y=t//tau;need((S*S-1)*y*y==S*S*V*V-1,'auxiliary recovery');accepted+=1
 # Concrete countercontrol if the coprimality hypothesis is deleted.
 A,S,V,t=45,2,2,15
 need((S*S-1)*t*t==A*(S*S*V*V-1)and isqrt(A)**2!=A,'missing-hypothesis countercontrol')
 # Finite matrix periods really can force a Pell ordinate to be divisible
 # by an arbitrary modulus; avoid factorial growth in this finite check.
 period_count=0
 for a in range(2,8):
  for M in range(2,15):
   x,y=1,0
   for n in range(1,M**4+1):
    x,y=(a*x+(a*a-1)*y)%M,(x+a*y)%M
    if (x,y)==(1,0):break
   else:raise ValueError('missing finite period')
   need(y==0,'period divisibility');period_count+=1
 return {'fold_controls':400,'norm_residue_controls':64,'anchored_coprimality_controls':anchor_controls,'accepted_small_product_controls':accepted,'finite_Pell_period_controls':period_count,'missing_coprimality_counterexample':{'A':45,'S':2,'V':2,'t':15}}

def main():
 binding=json.loads((HERE/'parents/COEFFICIENT_BINDING.json').read_text())
 ports={};pins={}
 for name,pin in binding['ports'].items():
  compressed=(HERE/'coefficients'/pin['file']).read_bytes();raw=gzip.decompress(compressed)
  need(hashlib.sha256(compressed).hexdigest()==pin['gzip_sha256'],'compressed coefficient '+name)
  need(hashlib.sha256(raw).hexdigest()==pin['raw_sha256'],'raw coefficient '+name)
  ports[name]=int.from_bytes(raw,'little');need(ports[name].bit_length()==pin['bits'],'coefficient bits '+name)
  pins[name]={'bits':pin['bits'],'sha256':pin['raw_sha256']}
 parent=json.loads((HERE/'parents/P66.json').read_text());prefix=[]
 for row in parent['source']:
  if row[0] not in ['tau2','N0']:prefix.append(row)
  if row[0]=='first_product':prefix.append(['A','+','first_product',1])
  if row[0]=='Nt':break
 receipt={'scope':'Finite graph/algebra checks; written proof handles all unbounded and calibration claims.','coefficient_binding':pins,'local':local_checks(),'graphs':{}}
 for filename,spec in SPECS.items():
  p=HERE/filename;d=json.loads(p.read_text());mode,info=graph_checks(d,spec,ports)
  need(d['source'][:len(prefix)]==prefix,'literal parent prefix '+filename)
  rng=random.Random(20261025)
  for _ in range(100):
   v={x:rng.randrange(1,9)for x in d['witnesses']+d['fixed_numerals']}
   need(eval_graph(d,v)[d['output']]==hand(v,mode),'independent full formula '+filename)
  # Genuine arithmetic mutation control: change a reachable operation.
  bad=json.loads(json.dumps(d));idx=next(j for j,r in enumerate(bad['source'])if r[0]=='Eprod');bad['source'][idx][1]='-'
  v={x:2 for x in d['witnesses']+d['fixed_numerals']}
  need(eval_graph(bad,v)[bad['output']]!=hand(v,mode),'mutation control')
  info['full_formula_controls']=100;info['arithmetic_mutation_rejected']=True;info['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
  receipt['graphs'][filename]=info
 print(json.dumps(receipt,indent=2,sort_keys=True))
if __name__=='__main__':main()
