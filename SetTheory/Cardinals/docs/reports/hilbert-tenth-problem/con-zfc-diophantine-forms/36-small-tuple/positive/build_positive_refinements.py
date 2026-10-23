#!/usr/bin/env python3
"""Division-free positive-12 refinements; Python standard library only.

Emits live binary +,-,* circuits. Fixed integers are four ordered ports from
one complete compiler tuple. No received Python module is imported.
"""
from pathlib import Path
import json
from collections import Counter

HERE = Path(__file__).resolve().parent
VARS = ['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']
PORTS = ['beta','K0','MC','MF']

class Circuit:
    def __init__(self): self.rows=[]; self.cache={}
    def op(self,op,a,b,name=None):
        key=(op,*sorted([a,b],key=str)) if op in ('+','*') else (op,a,b)
        if key in self.cache: return self.cache[key]
        name=name or 'g'+str(len(self.rows)+1)
        self.rows.append([name,op,a,b]); self.cache[key]=name
        return name
    def m(self,a,b,n=None): return self.op('*',a,b,n)
    def a(self,a,b,n=None): return self.op('+',a,b,n)
    def s(self,a,b,n=None): return self.op('-',a,b,n)
    def q(self,a,n=None): return self.m(a,a,n)

def trim(rows, outputs):
    live={x for x in outputs if isinstance(x,str)}
    for n,op,a,b in reversed(rows):
        if n in live:
            live.update(x for x in (a,b) if isinstance(x,str))
    return [row for row in rows if row[0] in live]

def build(weight='short',system=False,shift_transport=False):
    if shift_transport and not system: raise ValueError('Only system is shifted')
    C=Circuit(); m,a,s,q=C.m,C.a,C.s,C.q
    qm1=m('beta','J','qm1'); Qq=a(qm1,1,'q'); q2=q(Qq,'q2'); q3=m(q2,Qq,'q3')
    X=m('w',Qq,'X'); Y=m('s',q3,'Y'); E=m(X,Y,'E'); k=a('eta','zeta','k')
    kY=m(k,Y,'kY'); ell=m(E,kY,'ell'); A=a(m(ell,a(ell,k)),1,'A')
    c=a(kY,'eta','c'); av=a(E,Y,'a'); H=a(m(4,av),3,'H'); Delta=a(q(av),H,'Delta'); c2=q(c,'c2')
    G=a(m(Delta,c2),1,'G'); b0=a(X,m(av,c),'b0'); qF=s(Qq,'F','qF'); Cw=s(qF,'alpha','Cw')
    R=a(m(a(m(qm1,qF),'alpha'),s(q2,1)),m(a('MC',m(Qq,'MF')),'J'),'R')
    Nk=s(s(k,m('h',E)),R,'Nk')
    NtLeft=m(a('K0','w'),Cw,'NtLeft'); zq=m('z',qm1,'zq')
    if shift_transport:
        NtRight=a('F',zq,'NtRight')
    else:
        Nt=s(a(NtLeft,qF),zq,'Nt')
    I=m('i',c2,'I'); I2=q(I,'I2'); Dm1=m(Delta,I2,'Dm1'); D=a(Dm1,1,'D'); Q=m(Delta,Dm1,'Q'); d=s(Q,1,'d')
    T2=q('T','T2'); v2=m(c2,T2,'v2'); b=a(c,m(R,D),'b'); P=m(Q,m(D,v2),'P'); U=m(Q,q(b),'U')
    if weight=='short':
        M=m(k,a(I2,T2),'M')
        HM=m(H,M,'HM'); L=a(HM,1,'L'); W=a(b0,m(H,'t'),'W')
        norm_degree=1072
    elif weight=='tight':
        Csharp=a(a(E,m(2,a(X,Y))),m('s',q2),'Csharp')
        M=m(I,a(m(2,'T'),m(m(R,Csharp),m('i',c))),'M')
        HM=m(H,M,'HM'); L=a(m(2,HM),1,'L'); W=a(m(L,b0),m(H,'t'),'W')
        norm_degree=1060
    else: raise ValueError(weight)
    H2=q(H,'H2'); n=m(q(HM),A,'n'); dn=m(d,n,'dn')
    HP=m(H2,P,'HP'); HU=m(H2,U,'HU'); He=s(a(HP,HU),H2,'He'); j=m(4,m(HP,HU),'j')
    W2=q(W,'W2'); L2G=m(q(L),G,'L2G'); Trace=m(2,m(d,a(W2,L2G)),'Trace')
    # Improvement 1: (d*(W^2-L^2 G))^2 uses three gates, not four.
    Knorm=q(m(d,s(W2,L2G)),'Knorm')
    AA=m(2,a(dn,He),'AA'); constant=s(q(s(dn,He)),j,'constant')
    at=s(Trace,AA,'at'); bt=s(constant,Knorm,'bt'); coef=m(16,m(dn,j),'coef')
    # Improvement 2: choose the negative remainder coefficient for a free
    # final norm comparison, retaining the same operation count upstream.
    v=s(coef,m(at,a(m(at,Trace),m(2,bt))),'vneg')
    u=s(q(bt),m(q(at),Knorm),'u')
    left=m(u,s(m(Trace,v),u),'NormLeft')
    right=m(Knorm,q(v),'NormRight')
    if system:
        comparisons=[[Nk,1],[NtLeft,NtRight] if shift_transport else [Nt,1],[left,right]]
        outputs=[x for pair in comparisons for x in pair]
        extra={'comparisons':comparisons,'residual_exact_degrees':[7,2,norm_degree]}
    else:
        N=s(right,left,'N')
        output=s(m(m(Nk,Nt),a(N,1)),1,'polynomial')
        outputs=[output]; extra={'output':output,'exact_degree':norm_degree+9}
    rows=trim(C.rows,outputs); counts=Counter(r[1] for r in rows)
    name=('short109' if weight=='short' else 'tight120')+('_shifted_system' if shift_transport else '_system' if system else '_product')
    return {'name':name,'witnesses':VARS,'fixed_numerals':PORTS,'domain':'strictly positive integers',
            'source':rows,**extra,'coefficient_binding':'../../coefficients/COEFFICIENT_BINDING.json',
            'ledger':{'operations':len(rows),'multiplications':counts['*'],
                      'additions_subtractions':counts['+']+counts['-']}}

def main():
    out=HERE/'circuits'; out.mkdir(exist_ok=True)
    for weight in ('short','tight'):
        for system,shift in ((False,False),(True,False),(True,True)):
            p=build(weight,system,shift)
            (out/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
            print(p['name'],p['ledger'])

if __name__=='__main__': main()
