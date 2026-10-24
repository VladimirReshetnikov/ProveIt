#!/usr/bin/env python3
"""Independent finite algebra/degree/liveness verification for the new local reductions.

The literal circuit is data. No builder is imported. This is not a test
of consistency or a proof of the unbounded inherited semantic calibration.
"""
from pathlib import Path
import json, hashlib
from collections import Counter
from sparse import ring

ROOT=Path(__file__).resolve().parent

def require(condition,label):
    if not condition:
        raise RuntimeError(label)

def eq(p,q,label):
    require(not (p-q).d, label)

def needed(packet,roots):
    out=set(roots)
    for name,op,x,y in reversed(packet['source']):
        if name in out:
            out.update((x,y))
    return out

def run(packet,P,env,roots=None,start=0,stop=None):
    keep=needed(packet,roots) if roots is not None else None
    for name,op,x,y in packet['source'][start:stop]:
        if keep is not None and name not in keep:
            continue
        xx=env[x] if isinstance(x,str) else P(x)
        yy=env[y] if isinstance(y,str) else P(y)
        if op=='+': env[name]=xx+yy
        elif op=='-': env[name]=xx-yy
        elif op=='*': env[name]=xx*yy
        else: raise RuntimeError(op)
    return env

def graph_checks(packet,expected):
    req=needed(packet,[packet['output']])
    require(all(row[0] in req for row in packet['source']),'dead gate')
    require(set(packet['witnesses']+packet['fixed_numerals'])<=req,'dead input')
    require(len(packet['source'])==expected,'gate count')
    return dict(Counter(row[1] for row in packet['source']))

def prefix(packet,multiplier):
    names=packet['witnesses']; ports=packet['fixed_numerals']
    P=ring(names+ports,names); e={x:P.var(x) for x in names+ports}
    j,F,alpha,X,Y,r,eta,zeta,gamma=[e[x] for x in ['j','F','alpha','X','Y','r','eta','zeta','gamma']]
    beta,K0,MC,MF=[e[x] for x in ports]
    J=multiplier*j+1; q=beta*J+1; C=q-F-alpha
    E=X*Y; k=eta+zeta; c=k*Y+eta; a=E+Y
    H=4*a+3; Delta=a*a+H; ell=E*k*Y; b0=X+a*c
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    U=q*q*Y; r0=k-R-1
    Dstar=U*b0+H*(U*gamma+q*X*Y-r0)
    W=(q-1)*k+1; M0=q**3*(q-1)
    # Deliberately specify the original unfactored transport numerator.
    T1=(q*K0+X)*C+q*(q-F-1)
    Z=M0*(ell+k+q*W+r)+(q-1)*Y-q**3*W*T1
    A0=Z*Z-M0*M0*(ell*(ell+k)+1)
    A1=Dstar*Dstar-U*U*(1+Delta*c*c)
    specs={'A0':A0,'A1':A1,'a':a,'c':c,'Delta':Delta,'R':R}
    q0=multiplier*beta*j; k0=eta+zeta; R0=q0**3*(q0-F)
    Bt0=(K0*q0+X)*(q0-F-alpha)-q0*F
    leader0=-2*q0**8*k0**2*X*Y**2*Bt0
    leader1=8*q0**2*k0*X**2*Y**4*(q0**2*Y*gamma+R0)
    eq(A0.lead(),leader0,'first carrier leading form')
    eq(A1.lead(),leader1,'adaptive main leading form')
    require(A0.degree()==15 and A1.degree()==13,'carrier degrees')
    # The cancellation identity does not use any source equation.
    zz=U*gamma+q*X*Y-r0
    expanded=U**2*(2*a*c*X+X*X-H*c*c-1)+2*U*(a*c+X)*H*zz+H*H*zz*zz
    eq(A1,expanded,'adaptive cancellation identity')
    return P,e,specs,dict(q0=q0,k0=k0,R0=R0,Bt0=Bt0,leader0=leader0,leader1=leader1,
                          X=X,Y=Y,c=c,a=a,Delta=Delta,R=R)

receipts={}
p13=json.loads((ROOT/'p13_degree30.json').read_text())
P,e,spec,common=prefix(p13,3)
f,i,T,u=[e[x] for x in ['f','i','T','u']]
Delta=common['Delta']; c=common['c']; R=common['R']
I=i*c*c; V=f*f*(c*T-R)-c; Q=Delta*(f*f-1)
spec['Aa']=(V+u)**2-Q*u*(2*V+u)-1
spec['As']=f*f-Delta*I*I-1
run(p13,P,e,list(spec))
for key,val in spec.items(): eq(e[key],val,'P13 prefix '+key)
require([spec[x].degree() for x in p13['residuals']]==[15,13,13,14],'P13 degrees')
Pcut=ring(['A0','A1','Aa','As'])
cut={v:Pcut.var(v) for v in p13['residuals']}
start=1+max(idx for idx,row in enumerate(p13['source']) if row[0] in p13['residuals'])
run(p13,Pcut,cut,start=start)
eq(cut[p13['output']],sum((cut[x]**2 for x in p13['residuals']),Pcut(0)),'P13 SOS')
outlead=common['leader0']**2
require(outlead.degree()==30,'P13 output degree')
require(outlead.coef({'j':16,'eta':4,'X':4,'Y':4,'alpha':2,'beta':16})==4*3**16,'P13 fixed-port coefficient')
receipts['P13']={'degree':30,'operations':92,'breakdown':graph_checks(p13,92),
    'residual_degrees':[15,13,13,14],
    'selected_monomial':'j^16 eta^4 X^4 Y^4 alpha^2',
    'selected_coefficient':'4*(3*beta)^16',
    'sha256':hashlib.sha256((ROOT/'p13_degree30.json').read_bytes()).hexdigest()}
print('P13 exact prefix, finalizer, degree and liveness passed',flush=True)

p12=json.loads((ROOT/'p12_centered_product_split2.json').read_text())
P,e,spec,common=prefix(p12,6)
i,T=[e[x] for x in ['i','T']]
Delta=common['Delta']; c=common['c']; R=common['R']
I=i*c*c; D=1+Delta*I*I; M=Delta*I; dd=M*M-1; b=c*T-R; V=D*b-c
spec.update(I=I,D=D,Maux=M,dd=dd,b=b,V=V)
run(p12,P,e,list(spec))
for key,val in spec.items(): eq(e[key],val,'P12 prefix '+key)
require([I.degree(),D.degree(),M.degree(),dd.degree(),b.degree(),V.degree()]==[5,14,9,18,4,18],'P12 prefix degrees')

# A complete exact expansion over independent cut registers checks all
# cancellations through degrees86,85,84,83 in the actual norm suffix.
P5=ring(['a','c','i','b','n'],{'a':2,'c':2,'i':1,'b':4,'n':1})
aa,cc,ii,bb,nn=[P5.var(x) for x in ['a','c','i','b','n']]
delta=aa*aa+4*aa+3; ii0=ii*cc*cc; DD=1+delta*ii0*ii0
MM=delta*ii0; ddd=MM*MM-1; VV=DD*bb-cc
nu=nn+ii0*(bb+aa+2)
AA=MM*(ddd*(nu*nu+DD)+1-VV*VV)-2*ddd*nu
BB=2*ddd*(MM*nu-1)
NN=AA*AA-BB*BB*DD
cut5={'a':aa,'c':cc,'i':ii,'b':bb,'n':nn,'I':ii0,'D':DD,'Maux':MM,'dd':ddd,'V':VV}
start=1+next(idx for idx,row in enumerate(p12['source']) if row[0]=='V')
stop=1+next(idx for idx,row in enumerate(p12['source']) if row[0]=='N')
run(p12,P5,cut5,start=start,stop=stop)
eq(cut5['normA'],AA,'centered norm A')
eq(cut5['normB'],BB,'centered norm B')
eq(cut5['N'],NN,'centered norm N')
require(NN.degree()==82 and len(NN.d)==875,'centered norm exact expansion')
eq(NN.lead(),4*aa**12*cc**20*ii**10*bb**2,'centered norm leading form')
norm_expansion={'variables':['a','c','i','b','n'],'weights':[2,2,1,4,1],
 'terms':[{'powers':list(m),'coefficient':v} for m,v in sorted(NN.d.items())]}
(ROOT/'CENTERED_NORM_EXPANSION.json').write_text(json.dumps(norm_expansion,indent=2)+'\n')

Pcut=ring(['A0','A1','N']); cut={x:Pcut.var(x) for x in ['A0','A1','N']}
run(p12,Pcut,cut,start=stop)
eq(cut[p12['output']],(1+cut['A0'])*(1+cut['A1'])*(1+cut['N'])-1,'P12 product finalizer')
q0,k0,R0,Bt0,X,Y=[common[x] for x in ['q0','k0','R0','Bt0','X','Y']]
leaderN=4*i**10*k0**20*X**12*Y**32*R0**2
leaderP=common['leader0']*common['leader1']*leaderN
require(leaderP.degree()==110,'P12 exact output degree')
require(leaderP.coef({'j':18,'i':10,'eta':23,'X':16,'Y':39,'gamma':1,'alpha':1,'F':2,'beta':18})==64*6**18,'P12 fixed-port coefficient')
receipts['P12']={'degree':110,'operations':105,'breakdown':graph_checks(p12,105),
 'residual_degrees':[15,13,82],'compressed_norm_monomials':875,
 'selected_monomial':'j^18 i^10 eta^23 X^16 Y^39 gamma alpha F^2',
 'selected_coefficient':'64*(6*beta)^18',
 'sha256':hashlib.sha256((ROOT/'p12_centered_product_split2.json').read_bytes()).hexdigest()}
print('P12 exact prefix, complete centered norm, finalizer, degree and liveness passed',flush=True)

# The auxiliary reconstruction is checked independently over free symbols
# after replacing D by f^2. No numerical sample substitutes for this identity.
P5=ring(['M','v','V','f']); mm,vv,VV,ff=[P5.var(x) for x in ['M','v','V','f']]
dd=mm*mm-1; tt=vv-ff
AA=mm*(dd*(vv*vv+ff*ff)+1-VV*VV)-2*dd*vv
BB=2*dd*(mm*vv-1)
res=mm*dd*tt*tt-2*dd*tt+mm*(1-VV*VV)
eq(AA-BB*ff,res,'rational-root recovery identity')
eq(mm*res,dd*(mm*tt-1)**2-mm*mm*VV*VV+1,'auxiliary norm identity')

# Inspect the companion finalizer, preserving the same verified prefix.
sos=json.loads((ROOT/'p12_centered_sos_split2.json').read_text())
require(sos['source'][:stop]==p12['source'][:stop],'SOS prefix byte equality')
Pcut=ring(['A0','A1','N']); cut={x:Pcut.var(x) for x in ['A0','A1','N']}
run(sos,Pcut,cut,start=stop)
eq(cut[sos['output']],cut['A0']**2+cut['A1']**2+cut['N']**2,'P12 SOS finalizer')
receipts['P12_SOS']={'degree':164,'operations':104,'breakdown':graph_checks(sos,104)}

# Small Pell cases are a sanity check of the all-index recurrence proof only.
def pell(base,index):
    x,y=1,0
    for _ in range(index):
        x,y=base*x+(base*base-1)*y,x+base*y
    return x,y
examples=0
for base in range(2,12):
    for index in range(3,32,4):
        x,y=pell(base,index)
        require((y+1)%(base*base)==0,'canonical odd-index residue')
        examples+=1
receipts['finite_pell_sanity_examples']=examples
receipts['status']='passed'
receipts['scope']='Exact finite algebra, leading forms, circuit liveness and operation counts. Not consistency testing or an unbounded compiler/calibration proof.'
(ROOT/'CHECK_NEW.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(receipts,indent=2))

