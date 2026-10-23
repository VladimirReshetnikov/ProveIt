#!/usr/bin/env python3
"""Owned implementation of sourced scalar identities; no upstream Python imports.

Every binary +,-,* is charged, including multiplication by fixed integers.
Source30 trace/remainder algebra, source24 tight weights, and new weighted
carrier coefficient L=1+HM. See PROOF.md for semantics and exact degree.
"""
import json,hashlib
from collections import Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
VARIABLES=['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']
PORTS=['beta','K0','MC','MF']

class Circuit:
    def __init__(self): self.rows=[]; self.cache={}
    def op(self,op,a,b,name=None):
        key=(op,*sorted([a,b],key=str)) if op in ('+','*') else (op,a,b)
        if key in self.cache: return self.cache[key]
        name=name or 'g'+str(len(self.rows)+1)
        assert name not in [r[0] for r in self.rows]
        self.rows.append([name,op,a,b]);self.cache[key]=name;return name
    def a(self,a,b,n=None):return self.op('+',a,b,n)
    def s(self,a,b,n=None):return self.op('-',a,b,n)
    def m(self,a,b,n=None):return self.op('*',a,b,n)
    def q(self,a,n=None):return self.m(a,a,n)

def build(weight='tight',carrier='half',presentation='product'):
    C=Circuit();a,s,m,q=C.a,C.s,C.m,C.q
    qm1=m('beta','J','qm1');qq=a(qm1,1,'q');q2=q(qq,'q2');q3=m(q2,qq,'q3')
    ww=a('w',qq,'w_old') if weight=='shift' else 'w'
    X=m(ww,qq,'X');Y=m('s',q3,'Y');E=m(X,Y,'E');k=a('eta','zeta','k')
    kY=m(k,Y,'kY');ell=m(E,kY,'ell');A=a(m(ell,a(ell,k)),1,'A')
    c=a(kY,'eta','c');aa=a(E,Y,'a');ac=m(aa,c,'ac');b0=a(X,ac,'b0')
    H=a(m(4,aa),3,'H');Delta=a(q(aa),H,'Delta');c2=q(c,'c2');G=a(m(Delta,c2),1,'G')
    qF=s(qq,'F','qF');Cw=s(qF,'alpha','Cw')
    R=a(m(a(m(qm1,qF),'alpha'),s(q2,1)),m(a('MC',m(qq,'MF')),'J'),'R')
    Nk=s(s(k,m('h',E)),R,'Nk');transleft=m(a('K0',ww),Cw,'transleft')
    if presentation=='shifted_system':
        transright=a('F',m('z',qm1),'transright');Nt=None
    else:Nt=s(a(transleft,qF),m('z',qm1),'Nt')
    I=m('i',c2,'I')
    if weight=='short':
        I2=q(I,'I2');Dm1=m(Delta,I2,'Dm1');D=a(Dm1,1,'D');Q=m(Delta,Dm1,'Q')
        T2=q('T','T2');v2=m(c2,T2,'v2');M=m(k,a(I2,T2),'M')
    else:
        qr=m(Delta,I,'Qr');Q=q(qr,'Q');D=a(m(I,qr),1,'D');v=m(c,'T','v');v2=q(v,'v2')
        if weight in ('tight','shift'):
            Etilde=a(a(E,m(2,a(X,Y))),m('s',qq if weight=='shift' else q2),'Etilde')
        elif weight=='mid': Etilde=a(E,m(3,a(X,Y)),'Etilde')
        elif weight=='loose': Etilde=m(16,E,'Etilde')
        else: raise ValueError(weight)
        if weight=='loose':
            M=a(m(I,a(m(8,'T'),m(m(R,Etilde),m('i',c)))),1,'M')
        else: M=m(I,a(m(2,'T'),m(m(R,Etilde),m('i',c))),'M')
    d=s(Q,1,'d');b=a(c,m(R,D),'b')
    HM=m(H,M,'HM')
    if carrier=='plain':
        L=a(HM,1,'L');W=a(b0,m(H,'t'),'W')
    elif carrier in ('half','full'):
        L=a(HM if carrier=='half' else m(2,HM),1,'L')
        W=a(m(L,b0),m(H,'t'),'W')
    else:raise ValueError(carrier)
    H2=q(H,'H2');n=m(q(HM),A,'n');dn=m(d,n,'dn')
    HQ=m(H2,Q,'HQ');HP=m(HQ,m(D,v2),'HP');HU=m(HQ,q(b),'HU')
    He=s(a(HP,HU),H2,'He');j=m(4,m(HP,HU),'j')
    W2=q(W,'W2');L2G=m(q(L),G,'L2G');Trace=m(2,m(d,a(W2,L2G)),'Trace')
    Knorm=m(q(d),q(s(W2,L2G)),'Knorm');AA=m(2,a(dn,He),'AA')
    constant=s(q(s(dn,He)),j,'constant');at=s(Trace,AA,'at');bt=s(constant,Knorm,'bt')
    coef=m(16,m(dn,j),'coef');vbar=s(coef,m(at,a(m(at,Trace),m(2,bt))),'vbar')
    ur=s(q(bt),m(q(at),Knorm),'ur')
    term1=m(ur,s(m(Trace,vbar),ur),'term1');term2=m(Knorm,q(vbar),'term2')
    if presentation in ('system','shifted_system'):
        # Reverse the last subtraction in vr. No uncharged negation is used.
        comparisons=[[Nk,1],[transleft,transright] if presentation=='shifted_system' else [Nt,1],[term1,term2]];output=None
    else:
        N=s(term2,term1,'N')
        if presentation=='product':output=s(m(m(Nk,Nt),a(N,1)),1,'polynomial')
        elif presentation=='sos':output=a(a(q(s(Nk,1)),q(s(Nt,1))),q(N),'sos')
        else:raise ValueError(presentation)
        comparisons=None
    name='_'.join([weight,carrier,presentation])
    binding=json.loads((HERE/'COEFFICIENT_BINDING.json').read_text())
    assert binding['port_aliases']=={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}
    for item in binding['coefficient_files'].values():
        path=HERE/item['path']
        assert path.is_file(),('missing selected coefficient',str(path))
        assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256']
    out=dict(name=name,domain='strictly positive integers',witnesses=VARIABLES,
             fixed_numerals=PORTS,source=C.rows,coefficient_binding=binding,proof='PROOF.md',
             weight=weight,carrier=carrier,presentation=presentation)
    if output:out['output']=output
    else:out['comparisons']=comparisons
    norm_degree={('short','plain'):1072,('mid','full'):1064,('tight','full'):1060,
                 ('mid','half'):1060,('tight','half'):1056,('shift','half'):1052}[(weight,carrier)]
    if presentation=='product':out['exact_degree']=norm_degree+9
    elif presentation=='sos':out['exact_degree']=2*norm_degree
    else:
        out['residual_exact_degrees']=[7,2,norm_degree]
        out['exact_degree']=norm_degree
    out['degree_certificate']='PROOF.md, Section 8: uniform nonzero leading homogeneous form; CHECK_RESULTS.json supplies finite diagnostics only.'
    return out

def audit(p):
    env={n:1 for n in VARIABLES};env.update({n:0 for n in PORTS})
    for n,op,a,b in p['source']:
        assert n not in env
        da=0 if isinstance(a,int) else env[a];db=0 if isinstance(b,int) else env[b]
        env[n]=da+db if op=='*' else max(da,db)
    live=set([p['output']] if 'output' in p else [x for row in p['comparisons'] for x in row if isinstance(x,str)])
    for n,op,a,b in reversed(p['source']):
        assert n in live,('dead gate',n)
        live.update(x for x in [a,b] if isinstance(x,str))
    assert set(VARIABLES+PORTS)<=live
    counts=Counter(r[1] for r in p['source'])
    p['ledger']=dict(operations=len(p['source']),multiplications=counts['*'],
                     additions_subtractions=counts['+']+counts['-'],all_gates_live=True,all_ports_live=True)
    p['syntactic_degree_bound']=env.get(p.get('output','term1'))
    return p

def main():
    entries=[]
    for weight,carrier in [('short','plain'),('mid','full'),('tight','full'),('mid','half'),('tight','half'),('shift','half')]:
        for pres in ['product','system','shifted_system','sos']:
            p=audit(build(weight,carrier,pres));entries.append({k:p[k] for k in ['name','ledger','exact_degree','syntactic_degree_bound','degree_certificate']})
            (HERE/(p['name']+'.json')).write_text(json.dumps(p,indent=2)+'\n')
    (HERE/'BUILD_RECEIPT.json').write_text(json.dumps(entries,indent=2)+'\n');print(json.dumps(entries,indent=2))

if __name__=='__main__':main()
