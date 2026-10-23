"""Transparent arithmetic-circuit refactoring of frozen package 30.

No theorem about the compiler is tested by this generator.  Every +,-,* is
charged, including multiplication by literal constants; comparisons are free.
"""
import json
from pathlib import Path
from collections import Counter

HERE=Path(__file__).resolve().parent
WITNESSES=['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']
PORTS=['beta','K0','MC','MF']
class Circuit:
    def __init__(self): self.rows=[]; self.cache={}
    def op(self,op,a,b,n=None):
        key=(op,*sorted([a,b],key=str)) if op in ('+','*') else (op,a,b)
        if key in self.cache: return self.cache[key]
        n=n or 'g'+str(len(self.rows)+1)
        self.rows.append([n,op,a,b]);self.cache[key]=n;return n
    def m(self,a,b,n=None):return self.op('*',a,b,n)
    def a(self,a,b,n=None):return self.op('+',a,b,n)
    def s(self,a,b,n=None):return self.op('-',a,b,n)
    def q(self,a,n=None):return self.m(a,a,n)

def build(weight='economical',kind='product'):
    C=Circuit();m,a,s,q=C.m,C.a,C.s,C.q
    qm1=m('beta','J','qm1');Qq=a(qm1,1,'q');q2=q(Qq,'q2');q3=m(q2,Qq,'q3')
    X=m('w',Qq,'X');Y=m('s',q3,'Y');E=m(X,Y,'E');k=a('eta','zeta','k')
    kY=m(k,Y,'kY');ell=m(E,kY,'ell');A=a(m(ell,a(ell,k)),1,'A')
    c=a(kY,'eta','c');av=a(E,Y,'a');H=a(m(4,av),3,'H');Delta=a(q(av),H,'Delta');c2=q(c,'c2')
    G=a(m(Delta,c2),1,'G');b0=a(X,m(av,c),'b0');qF=s(Qq,'F','qF');Cw=s(qF,'alpha','Cw')
    R=a(m(a(m(qm1,qF),'alpha'),s(q2,1)),m(a('MC',m(Qq,'MF')),'J'),'R')
    Nk=s(s(k,m('h',E)),R,'Nk');trans0=m(a('K0','w'),Cw,'trans0');trans2=m('z',qm1,'trans2')
    if kind=='shifted_system':
        transport_rhs=a('F',trans2,'transport_rhs'); nt_comparison=[trans0,transport_rhs]
    else:
        Nt=s(a(trans0,qF),trans2,'Nt');nt_comparison=[Nt,1]
    I=m('i',c2,'I');I2=q(I,'I2');Dm1=m(Delta,I2,'Dm1');D=a(Dm1,1,'D');Q=m(Delta,Dm1,'Q');d=s(Q,1,'d')
    T2=q('T','T2');v2=m(c2,T2,'v2');b=a(c,m(R,D),'b')
    if weight=='economical':
        M=m(k,a(I2,T2),'M');HM=m(H,M,'HM');L=a(HM,1,'L');W=a(b0,m(H,'t'),'W')
    elif weight=='cancellation1065':
        CC=a(a(E,m(2,a(X,Y))),m('s',q2),'CC')
        M=m(I,a(m(2,'T'),m(m(R,CC),m('i',c))),'M')
        HM=m(H,M,'HM')
        L=a(HM,1,'L')
        W=a(m(L,b0),m(H,'t'),'W')
    else:raise ValueError(weight)
    H2=q(H,'H2');n=m(q(HM),A,'n');dn=m(d,n,'dn')
    H2Q=m(H2,Q,'H2Q');HP=m(H2Q,m(D,v2),'HP');HU=m(H2Q,q(b),'HU')
    He=s(a(HP,HU),H2,'He');j=m(4,m(HP,HU),'j')
    W2=q(W,'W2');L2G=m(q(L),G,'L2G');Trace=m(2,m(d,a(W2,L2G)),'Trace')
    kd=m(d,s(W2,L2G),'kd');Knorm=q(kd,'Knorm')
    AA=m(2,a(dn,He),'AA');constant=s(q(s(dn,He)),j,'constant')
    at=s(Trace,AA,'at');bt=s(constant,Knorm,'bt');coef=m(16,m(dn,j),'coef')
    vr=s(m(at,a(m(at,Trace),m(2,bt))),coef,'vr');ur=s(q(bt),m(q(at),Knorm),'ur')
    N=a(m(ur,a(ur,m(Trace,vr))),m(Knorm,q(vr)),'N')
    result=dict(name=weight+'_'+kind,witnesses=WITNESSES,fixed_numerals=PORTS,
        domain='strictly positive integers',source=C.rows,
        coefficient_binding='../coefficients/COEFFICIENT_BINDING.json',
        proof='../sections/positive.tex',
        fixed_port_payloads={'beta':'beta.bin','K0':'K.bin','MC':'MC.bin','MF':'MF_source.bin'},
        provenance={'repository':'VladimirReshetnikov/ProveIt','commit':'8c6eec9d19ef80538c8e61ff6e0180040583446a',
                    'bases':['24-integer24/sections/positive.tex','25-hybrid12/proofs/HYBRID12_PROOF.md',
                             '26-ratio12/proofs/RATIO12_PROOF.md','30-quartic31/positive/POSITIVE12_PROOF.md']})
    if kind=='product':
        result['output']=s(m(m(Nk,Nt),a(N,1)),1,'polynomial')
        result['exact_degree']={'economical':1081,'cancellation1065':1065}[weight]
    else:
        result['comparisons']=[[Nk,1],nt_comparison,[N,0]]
        result['residual_exact_degrees']=[7,2,{'economical':1072,'cancellation1065':1056}[weight]]
        if kind=='shifted_system':result['coordinate_relation']='old z = new z + 1'
    counts=Counter(r[1] for r in C.rows)
    result['ledger']={'operations':len(C.rows),'multiplications':counts['*'],'additions_subtractions':counts['+']+counts['-']}
    return result

def evaluate(p,vals,modulus=None):
    d=dict(vals)
    for n,o,l,r in p['source']:
        l=l if isinstance(l,int) else d[l];r=r if isinstance(r,int) else d[r]
        v=l+r if o=='+' else l-r if o=='-' else l*r
        d[n]=v if modulus is None else v%modulus
    return d

def main():
    for w in ['economical','cancellation1065']:
        for k in ['product','system','shifted_system']:
            p=build(w,k);(HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
            print(p['name'],p['ledger'])
if __name__=='__main__':main()
