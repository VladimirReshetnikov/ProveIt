#!/usr/bin/env python3
"""Separate exact polynomial-ring review; imports neither producer nor verifier."""
from collections import defaultdict
from pathlib import Path
import json, hashlib, random
NVAR=6
Z=(0,)*NVAR
def const(n):return {Z:n}if n else{}
def var(i):a=list(Z);a[i]=1;return{tuple(a):1}
def add(*ps):
 d=defaultdict(int)
 for p in ps:
  for m,c in p.items():d[m]+=c
 return{m:c for m,c in d.items()if c}
def scale(p,k):return{m:c*k for m,c in p.items()if c*k}
def mul(a,b):
 d=defaultdict(int)
 for m,c in a.items():
  for n,e in b.items():d[tuple(x+y for x,y in zip(m,n))]+=c*e
 return{m:c for m,c in d.items()if c}
def power(p,n):
 r=const(1)
 for _ in range(n):r=mul(r,p)
 return r
def prod(*ps):
 r=const(1)
 for p in ps:r=mul(r,p)
 return r
def sub(a,b):return add(a,scale(b,-1))
def require(q,msg):
 if not q:raise ValueError(msg)
def top(p,w):
 d=max(sum(a*b for a,b in zip(m,w))for m in p);return d,{m:c for m,c in p.items()if sum(a*b for a,b in zip(m,w))==d}
def subst(p,repl):
 out={}
 for m,c in p.items():
  r=const(c)
  for x,n in zip(repl,m):r=mul(r,power(x,n))
  out=add(out,r)
 return out
A,N,k,U,b,c=[var(i)for i in range(6)]
e2=prod(power(k,2),power(N,2));e1=prod(power(k,2),N,add(const(1),scale(N,-2),scale(power(N,2),-2)));NN=prod(N,add(N,const(1)));e0=add(const(1),prod(power(k,2),NN,sub(NN,const(1))))
E=add(prod(e2,power(A,2)),prod(e1,A),e0);S=add(prod(e2,A),e1);Delta=sub(power(A,2),const(1));G=prod(E,add(const(1),prod(Delta,power(U,2),E)));f=add(const(1),scale(prod(Delta,power(U,2),E),2));V=sub(prod(f,b),c)
require(E==add(prod(A,S),e0),'E quotient identity')
C2=prod(U,sub(scale(prod(A,E),2),S));D2=sub(power(C2,2),scale(G,4));D2identity=add(scale(prod(power(U,2),E,e0),4),prod(power(U,2),power(S,2)),scale(E,-4));require(D2==D2identity,'scalar norm defect')
theta=prod(power(U,2),b);Rc=sub(prod(theta,add(scale(E,3),e2)),sub(b,c));Sc=add(scale(power(E,2),4),scale(power(S,2),3),power(e2,2));Omega=prod(U,add(scale(prod(S,Rc),2),prod(A,sub(scale(prod(E,V),4),prod(theta,Sc)))))
EV=prod(E,V)
def quotient(p,j):return{(m[0]-j,)+m[1:]:v for m,v in p.items()if m[0]>=j}
Q1,Q3=quotient(EV,1),quotient(EV,3);require(all(v%2==0 for v in Q3.values()),'Q3 coefficient parity');qhalf={m:v//2 for m,v in Q3.items()};require(Omega==prod(U,sub(sub(scale(prod(A,EV),4),scale(Q1,2)),qhalf)),'whole product quotient identity')
D4=sub(power(Omega,2),scale(prod(G,power(V,2)),16));weights=[4,2,1,5,4,2]
d2,t2=top(D2,weights);d4,t4=top(D4,weights)
require(d2==34 and t2==scale(prod(power(U,2),power(A,2),power(N,6),power(k,4)),4),'scalar defect full leader')
expected4=scale(prod(power(A,6),power(N,8),power(k,8),power(U,6),power(b,2),sub(power(A,2),scale(power(N,4),6))),8)
require(d4==94 and t4==expected4,'whole defect full leader');require(len(Omega)==84 and len(D4)==594,'exact collected term counts')
# Entire highest forms after all ten-input dependencies, with q standing for beta*J and k for eta+zeta.
q,F,w,s,i,kk=[var(j)for j in range(6)]
A0=prod(power(q,2),w,s);N0=prod(q,s);U0=prod(i,power(kk,2),power(s,2));b0=scale(prod(power(q,3),sub(q,F)),-1);c0=prod(kk,s)
Qtop=scale(prod(power(A,10),power(U,4),power(k,4),power(N,4)),4)
M2top=scale(prod(power(A,2)),24*24) # separately times q^16 below
V2top=scale(prod(power(A,8),power(U,4),power(k,4),power(N,4),power(b,2)),4)
replacement=[A0,N0,kk,U0,b0,c0]
p202=prod(power(q,16),subst(prod(Qtop,M2top,t2,V2top),replacement))
p190=prod(power(q,16),subst(prod(Qtop,M2top,t4),replacement))
expect202=scale(prod(power(q,80),power(w,22),power(s,56),power(i,10),power(kk,32),power(sub(q,F),2)),9*2**12)
expect190=scale(prod(power(q,74),power(w,18),power(s,52),power(i,10),power(kk,32),power(sub(q,F),2),sub(power(w,2),scale(power(s,2),6))),9*2**11)
require(p202==expect202 and p190==expect190,'actual leading substitution')
root=Path(__file__).resolve().parent; graphs=[]
for name in ['start4127_positive10_degree202_ops99','start4127_positive10_degree190_ops120']:
 path=root/(name+'.json');j=json.loads(path.read_text());ops=j['source'];defined=set(j['witnesses'])|set(j['fixed_numerals']);ref={};counts=defaultdict(int)
 for dest,op,l,r in ops:
  require(dest not in defined,'duplicate gate');require(op in ['+','-','*'],'ordinary gate');require(all(isinstance(x,int)or x in defined for x in [l,r]),'topological gate');defined.add(dest);ref[dest]=[x for x in [l,r]if isinstance(x,str)];counts[op]+=1
 live=set();stack=[j['output']]
 while stack:
  x=stack.pop()
  if x in live:continue
  live.add(x);stack+=ref.get(x,[])
 require(all(x[0]in live for x in ops),'all gates live');require(all(x in live for x in j['witnesses']),'all inputs live');require(len(ops)==j['operations'],'operation count')
 cb=j['coefficient_binding'];fixed={}
 for port,meta in cb['ports'].items():
  raw=(root/cb['path']/meta['file']).read_bytes();require(hashlib.sha256(raw).hexdigest()==meta['sha256'],'fixed port hash');fixed[port]=int.from_bytes(raw,'big')
 # Probe the emitted DAG against separately transcribed complete formula. These are corroboration, not proof by sampling.
 rng=random.Random(20261026); probes=0
 for prime in [1000003,1000033]:
  for _ in range(20):
   inp={x:rng.randrange(1,100)for x in j['witnesses']};env={**inp,**{k:v%prime for k,v in fixed.items()}}
   for dst,op,l,r in ops:
    a=l if isinstance(l,int)else env[l];b_=r if isinstance(r,int)else env[r];env[dst]=({'+':lambda:a+b_,'-':lambda:a-b_,'*':lambda:a*b_}[op]())%prime
   J,F_,alpha,ii,T,w_,s_,n,eta,zeta=[inp[x]for x in j['witnesses']];beta,K0,MC,MF=[fixed[x]%prime for x in ['beta','K0','MC','MF']]
   h=beta*J;q_=h+1;C=q_-F_-alpha;X=q_*w_;NN=q_*s_;kk_=eta+zeta;c_=kk_*s_+eta;A_=NN*(X+1)+1;De=A_*A_-1;H=4*A_-5;vv=X*NN*NN;ell=vv*kk_;EE=1+ell*(ell+kk_);RR=(h*(q_-F_)+alpha)*(q_*q_-1)+(MC+q_*MF)*J;B=(K0+w_)*C-F_;UU=ii*c_*c_;aa=De*UU*UU*EE;FF=1+aa;GG=EE*FF;ff=aa+FF;QQ=4*De*aa*FF;bb=c_*T-RR;VV=ff*bb-c_;KK=X*(3*c_-2*X)+2;e6=6*(kk_-RR-1)-ell*(kk_*kk_-4);DD=6*q_**7;MM=h*DD*H;SS=(kk_*NN)*(ell+kk_-(kk_*NN)*(NN+1))
   if j['exact_degree']==202:rr=2;LL=bb*VV;Om=(2*A_*UU*EE-UU*SS)*VV
   else:
    rr=4;LL=UU*EE*bb*bb;ee2=(kk_*NN)**2;th=UU*UU*bb;Rc_=th*(3*EE+ee2)-(bb-c_);Sc_=4*EE*EE+3*SS*SS+ee2*ee2;Om=UU*(2*SS*Rc_+A_*(4*EE*VV-th*Sc_))
   Z0=h*DD*(H*(n-LL*B)+KK)-H*(DD*B+h*(e6-6*q_**4*s_));ZZ=Z0-MM*Om;expected=(QQ*(ZZ*ZZ-rr*rr*MM*MM*GG*VV*VV)+(rr*rr*MM*MM*GG-ZZ*ZZ))%prime
   require(expected==env[j['output']],'formula probe');probes+=1
  
 graphs.append({'name':name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'operations':len(ops),'breakdown':dict(counts),'all_inputs_and_gates_live':True,'fixed_port_hashes_match':True,'modular_complete_formula_probes':probes})
receipt={'method':'Independent exact sparse polynomial-ring computation, no source producer/checker imports; finite DAG formula probes labeled separately','center_terms':len(Omega),'whole_defect_terms':len(D4),'scalar_defect_exact_degree':d2,'whole_defect_exact_degree':d4,'whole_quotient_identity':True,'actual_complete_leading_forms_equal':True,'exact_output_degrees':[202,190],'graphs':graphs}
(root/'INDEPENDENT_ALGEBRA_REVIEW.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
