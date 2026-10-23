#!/usr/bin/env python3
"""Independent exact, cut-based sparse-polynomial audit of root_opt's P12.

The evaluator is read as data; its builder is not imported. Prefix identities,
suffix identities over independent cut registers, and exact leading forms
compose to a full literal-circuit audit without expanding the huge output.
"""
import json, hashlib
from pathlib import Path
from collections import Counter
ROOT=Path(__file__).resolve().parent
INPUT=ROOT/'p12_product_split2.json'
packet=json.loads(INPUT.read_text())

def ring(variables, counted=None):
    counted=set(variables if counted is None else counted)
    N=len(variables); zero=(0,)*N
    weights=[int(v in counted) for v in variables]
    class P:
        def __init__(self,x=0): self.d=dict(x) if isinstance(x,dict) else ({zero:x} if x else {})
        @classmethod
        def var(cls,n):
            e=[0]*N; e[variables.index(n)]=1; return cls({tuple(e):1})
        def __add__(self,b):
            if not isinstance(b,P): b=P(b)
            c=dict(self.d)
            for e,a in b.d.items():
                c[e]=c.get(e,0)+a
                if not c[e]: del c[e]
            return P(c)
        __radd__=__add__
        def __neg__(self): return P({e:-a for e,a in self.d.items()})
        def __sub__(self,b): return self+-b if isinstance(b,P) else self+(-b)
        def __rsub__(self,b): return -self+b
        def __mul__(self,b):
            if not isinstance(b,P): b=P(b)
            c={}
            for e,a in self.d.items():
                for f,b0 in b.d.items():
                    g=tuple(x+y for x,y in zip(e,f)); c[g]=c.get(g,0)+a*b0
            return P({e:a for e,a in c.items() if a})
        __rmul__=__mul__
        def __pow__(self,n):
            a=self; c=P(1)
            while n:
                if n%2: c=c*a
                n//=2
                if n: a=a*a
            return c
        def degree(self): return max((sum(a*b for a,b in zip(e,weights)) for e in self.d),default=-1)
        def lead(self):
            k=self.degree(); return P({e:a for e,a in self.d.items() if sum(x*y for x,y in zip(e,weights))==k})
        def coef(self,powers):
            return self.d.get(tuple(powers.get(n,0) for n in variables),0)
    return P

def eq(a,b,label):
    if (a-b).d: raise RuntimeError(label)

def needed_gates(roots):
    needed=set(roots)
    for n,op,x,y in reversed(packet['source']):
        if n in needed: needed.update((x,y))
    return needed

def run(P,env,needed=None,start=0,stop=None):
    for row in packet['source'][start:stop]:
        n,op,x,y=row
        if needed is not None and n not in needed: continue
        a=env[x] if isinstance(x,str) else P(x)
        b=env[y] if isinstance(y,str) else P(y)
        env[n]={'+':lambda:a+b,'-':lambda:a-b,'*':lambda:a*b}[op]()
    return env

names=packet['witnesses']; ports=packet['fixed_numerals']
P=ring(names+ports,names); env={n:P.var(n) for n in names+ports}
j,F,alpha,i,T,X,Y,r,eta,zeta,n,gamma=(env[v] for v in names)
beta,K0,MC,MF=(env[v] for v in ports)
J=6*j+1; q=beta*J+1; C=q-F-alpha; E=X*Y; k=eta+zeta; c=k*Y+eta
ell=E*k*Y; a=E+Y; H=4*a+3; Delta=a*a+H; b0=X+a*c
R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
r0=k-R-1; U=q**5; Dstar=U*b0+H*(U*gamma+q**4*X-r0)
W=(q-1)*k+1; M0=q**3*(q-1)
# Deliberately the independent, unfactored transport carrier.
T1=(q*K0+X)*C+q*(q-F-1)
Z=M0*(ell+k+q*W+r)+(q-1)*Y-q**3*W*T1
A0=Z**2-M0**2*(ell*(ell+k)+1)
A1=Dstar**2-U**2*(1+Delta*c*c)
I=i*c*c; D=1+Delta*I*I; Caux=Delta*i*c; Maux=Delta*i*c**3
Q=Maux*Caux; dd=Q-1; V=D*(c*T-R)-c
spec={'A0':A0,'A1':A1,'D':D,'Caux':Caux,'Maux':Maux,'Q':Q,'dd':dd,'V':V,'Delta':Delta,'R':R,'c':c}
run(P,env,needed_gates(spec.keys()))
for key,value in spec.items(): eq(env[key],value,'prefix '+key)
eq(Q,Delta*(D-1),'Q=Delta(D-1)')
# Compare all relevant original graph prefixes exactly, independently of
# the builder. The same cut norm/finalizer is checked on both graphs below.
newpacket=packet
oldpacket=json.loads((ROOT/'reference/p12_product_split2_105.json').read_text())
packet=oldpacket
oldenv={v:P.var(v) for v in names+ports}
run(P,oldenv,needed_gates(spec.keys()))
for key,value in spec.items(): eq(oldenv[key],value,'original prefix '+key)
packet=newpacket

expected={'A0':15,'A1':17,'D':14,'Caux':7,'Maux':11,'Q':18,'dd':18,'V':18,'Delta':4,'R':4,'c':2}
for key,deg in expected.items():
    if spec[key].degree()!=deg: raise RuntimeError(('prefix degree',key,spec[key].degree(),deg))

q0=6*beta*j; k0=eta+zeta; c0=k0*Y; Delta0=X**2*Y**2
R0=q0**3*(q0-F); D0=Delta0*(i*c0**2)**2
Bt0=(K0*q0+X)*(q0-F-alpha)-q0*F
leader0=-2*q0**8*k0**2*X*Y**2*Bt0
leader1=8*q0**10*k0*X**2*Y**3*gamma
normAleader=(Delta0*i*c0)*D0**2*(Delta0*c0**2-R0**2)
eq(A0.lead(),leader0,'first leading form')
eq(A1.lead(),leader1,'main leading form')
# The two degree-43 summands in normA are checked explicitly. Every omitted
# summand has smaller degree (max32), and normB^2*D has degree74<86.
computedA=Q.lead()*Maux.lead()*D.lead()-Caux.lead()*V.lead()**2
eq(computedA,normAleader,'normA leading form')
if normAleader.degree()!=43: raise RuntimeError('normA exact degree')
leaderN=normAleader**2
leaderP=leader0*leader1*leaderN
if leaderP.degree()!=118: raise RuntimeError('output degree')
powers={'j':18,'i':10,'eta':25,'X':20,'Y':43,'gamma':1,'alpha':1,'beta':18}
co=leaderP.coef(powers)
if co!=16*6**18: raise RuntimeError(('selected coefficient',co))

# Exact suffix equality in the polynomial ring of independent cut registers.
P2=ring(['D','M','C','V','n']); d2,m2,c2,v2,n2=(P2.var(v) for v in ['D','M','C','V','n'])
q2=m2*c2; de=q2-1
cut={'D':d2,'Maux':m2,'Caux':c2,'V':v2,'n':n2,'dd':de}
start=next(i for i,row in enumerate(packet['source']) if row[0]=='Mn')
end=next(i for i,row in enumerate(packet['source']) if row[0]=='N')+1
run(P2,cut,start=start,stop=end)
na=de*m2*(n2*n2+d2)-2*de*n2+c2*(1-v2*v2)
nb=2*de*(m2*n2-1)
eq(cut['normA'],na,'normA cut')
eq(cut['normB'],nb,'normB cut')
eq(cut['N'],na*na-nb*nb*d2,'normN cut')

P3=ring(['A0','A1','N']); cut3={v:P3.var(v) for v in ['A0','A1','N']}
run(P3,cut3,start=end)
eq(cut3[packet['output']],(1+cut3['A0'])*(1+cut3['A1'])*(1+cut3['N'])-1,'output cut')
packet=oldpacket
oldcut={'D':d2,'Maux':m2,'Caux':c2,'V':v2,'n':n2,'dd':de}
oldstart=next(i for i,row in enumerate(packet['source']) if row[0]=='Mn')
oldend=next(i for i,row in enumerate(packet['source']) if row[0]=='N')+1
run(P2,oldcut,start=oldstart,stop=oldend)
eq(oldcut['normA'],na,'original normA cut')
eq(oldcut['normB'],nb,'original normB cut')
eq(oldcut['N'],na*na-nb*nb*d2,'original normN cut')
oldcut3={v:P3.var(v) for v in ['A0','A1','N']}
run(P3,oldcut3,start=oldend)
eq(oldcut3[packet['output']],(1+oldcut3['A0'])*(1+oldcut3['A1'])*(1+oldcut3['N'])-1,'original output cut')
packet=newpacket


# The SOS sibling has the identical verified residual graph and a separately
# checked exact finalizer. Its unique degree-172 term is N^2.
sospath=ROOT/'p12_sos_split2.json'
sospacket=json.loads(sospath.read_text())
sosend=next(i for i,row in enumerate(sospacket['source']) if row[0]=='N')+1
if sospacket['source'][:sosend]!=newpacket['source'][:end]:
    raise RuntimeError('optimized SOS prefix differs')
oldsos=json.loads((ROOT/'reference/p12_sos_split2_104.json').read_text())
oldsosend=next(i for i,row in enumerate(oldsos['source']) if row[0]=='N')+1
if oldsos['source'][:oldsosend]!=oldpacket['source'][:oldend]:
    raise RuntimeError('original SOS prefix differs')
for pp,ee,label in [(sospacket,sosend,'optimized'),(oldsos,oldsosend,'original')]:
    packet=pp
    scut={v:P3.var(v) for v in ['A0','A1','N']}
    run(P3,scut,start=ee)
    eq(scut[packet['output']],scut['A0']**2+scut['A1']**2+scut['N']**2,label+' SOS finalizer')
packet=sospacket
sosneed=needed_gates([packet['output']])
if any(row[0] not in sosneed for row in packet['source']): raise RuntimeError('SOS dead gate')
if not set(names+ports)<=sosneed: raise RuntimeError('SOS dead input')
if len(packet['source'])!=103: raise RuntimeError('SOS gate count')
if 2*leaderN.degree()!=172: raise RuntimeError('SOS degree')
sosreceipt={'operations':103,'breakdown':dict(Counter(row[1] for row in packet['source'])),'exact_total_degree':172,'original_104_gate_polynomial_exactly_equal':True,'sha256':hashlib.sha256(sospath.read_bytes()).hexdigest()}
packet=newpacket

# Exact recovery identity after the rational square root has become integer.
P4=ring(['M','C','n','V','f']); mm,cc,nn,vv,ff=(P4.var(v) for v in ['M','C','n','V','f'])
qq=mm*cc; de=qq-1; tt=nn-ff
AA=de*mm*(nn*nn+ff*ff)-2*de*nn+cc*(1-vv*vv)
BB=2*de*(mm*nn-1)
res=de*mm*tt*tt-2*de*tt+cc*(1-vv*vv)
eq(AA-BB*ff,res,'signed root recovery')
eq(mm*res,de*(mm*tt-1)**2-qq*vv*vv+1,'divided auxiliary norm')

# Finite Pell coefficient checks supplement the all-index recurrence proof.
def pell(A,t):
    x,y=1,0
    for _ in range(t): x,y=A*x+(A*A-1)*y,x+A*y
    return x,y
cases=0
for mm0 in range(2,10):
    for rr in range(3,32,4):
        xx,yy=pell(mm0,rr)
        if (yy+1)%(mm0*mm0): raise RuntimeError('Pell residue')
        cases+=1

needed=needed_gates([packet['output']])
if any(row[0] not in needed for row in packet['source']): raise RuntimeError('dead gate')
if not set(names+ports)<=needed: raise RuntimeError('dead input')
if len(packet['source'])!=104: raise RuntimeError('gate count')
receipt={'status':'passed','sos_sibling':sosreceipt,'method':'Independent exact symbolic prefix, exact suffix over independent cut registers, all-value recovery identities, exact leading forms and nonzero monomial. No builder import, no random evaluation substituted for identity.','variables':12,'original_105_gate_cut_identities_exactly_equal':True,'domain':'strictly positive integers','operations':104,'breakdown':dict(Counter(row[1] for row in packet['source'])),'residual_degrees':[15,17,86],'degree':118,'selected_monomial':'j^18 i^10 eta^25 X^20 Y^43 gamma alpha','selected_coefficient':'16*(6*beta)^18','fixed_port_independent_nonvanishing':True,'finite_auxiliary_congruence_cases':cases,'sha256':hashlib.sha256(INPUT.read_bytes()).hexdigest(),'scope_limit':'Not a proof-assistant certificate, no coefficient-byte verification or native compiler reproof; mathematical semantic review is in AUDIT12.md.'}
(ROOT/'CHECK12.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
