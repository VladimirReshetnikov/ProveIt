#!/usr/bin/env python3
"""New ordinary algebra research. No Lean execution and no parent code imports."""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF']
class DAG:
    def __init__(self): self.rows=[]; self.cache={}
    def gate(self,op,a,b,name=None):
        if op in ('+','*') and str(a)>str(b): a,b=b,a
        key=op,a,b
        if key in self.cache:return self.cache[key]
        name=name or 'g'+str(len(self.rows))
        if any(r[0]==name for r in self.rows):raise ValueError(name)
        self.rows.append([name,op,a,b]);self.cache[key]=name;return name
    def add(self,a,b,name=None):return self.gate('+',a,b,name)
    def sub(self,a,b,name=None):return self.gate('-',a,b,name)
    def mul(self,a,b,name=None):return self.gate('*',a,b,name)
    def sq(self,a,name=None):return self.mul(a,a,name)
    def packet(self,variables,root,degree,name,residuals):
        live={root}
        for n,op,a,b in reversed(self.rows):
            if n in live:live.update((a,b))
        rows=[r for r in self.rows if r[0] in live]
        if not set(variables+PORTS)<=live:raise ValueError('dead input')
        return dict(name=name,domain='strictly positive integers',witnesses=variables,
          fixed_numerals=PORTS,source=rows,output=root,operations=len(rows),
          operation_breakdown=dict(Counter(r[1] for r in rows)),exact_degree=degree,
          residuals=residuals,coefficient_binding='whole compact44 tuple beta,K,MC,MF_source; MF already shifted',
          status='ordinary local equivalence/existence argument; native calibration inherited; Lean paused')
def prefix(d,m):
    a,s,p,z=d.add,d.sub,d.mul,d.sq
    J=a(p(m,'j'),1,'J');qm=p('beta',J,'qm');q=a(qm,1,'q')
    q2=z(q,'q2');q3=p(q2,q,'q3');U=p(q2,'Y','U')
    qF=s(q,'F','qF');C=s(qF,'alpha','C');E=p('X','Y','E')
    k=a('eta','zeta','k');kY=p(k,'Y','kY');c=a(kY,'eta','c');c2=z(c,'c2')
    aa=a(E,'Y','a');H=a(p(4,aa),3,'H');delta=a(z(aa),H,'Delta')
    b0=a('X',p(aa,c),'b0');ell=p(E,kY,'ell');W=a(p(qm,k),1,'W');M=p(q3,qm,'M')
    Bt=s(p(a(p(q,'K0'),'X'),C),p(q,'F'),'Bt')
    Z=s(a(p(M,a(a(ell,k),'r')),p(qm,'Y')),p(p(q3,W),Bt),'Z')
    A0=s(z(Z),p(z(M),a(p(ell,a(ell,k)),1)),'A0')
    G=a(p(qm,qF),'alpha','G');R=a(p(G,s(q2,1)),p(a('MC',p(q,'MF')),J),'R')
    r0=s(s(k,R),1,'r0');shift=s(a(p(U,'gamma'),p(q,E)),r0,'shift')
    Dstar=a(p(U,b0),p(H,shift),'Dstar');A1=s(z(Dstar),p(z(U),a(p(delta,c2),1)),'A1')
    return dict(c=c,c2=c2,Delta=delta,R=R,A0=A0,A1=A1)
def make13(mode):
    d=DAG();a,s,p,z=d.add,d.sub,d.mul,d.sq;r=prefix(d,3)
    f2=z('f','f2');rho=s(f2,1,'rho');Q=p(r['Delta'],rho,'Q');I=p('i',r['c2'],'I')
    strong=p(r['Delta'],z(I),'strong');As=s(rho,strong,'As')
    V=s(p(f2,s(p(r['c'],'T'),r['R'])),r['c'],'V');y2=z(a(V,'u'),'y2')
    Fa=s(y2,p(Q,s(y2,z(V))),'Fa');Aa=s(Fa,1,'Aa')
    if mode=='product':
        Fs=s(f2,strong,'Fs');F0=a(r['A0'],1,'F0');F1=a(r['A1'],1,'F1')
        out=s(p(p(p(F0,F1),Fa),Fs),1,'P13')
        degree=55
    else:
        out=a(a(a(z(r['A0']),z(r['A1'])),z(Aa)),z(As),'P13');degree=30
    variables=['j','F','alpha','f','i','T','X','Y','r','eta','zeta','u','gamma']
    return d.packet(variables,out,degree,'p13_'+mode,[r['A0'],r['A1'],Aa,As])
def make12():
    d=DAG();a,s,p,z=d.add,d.sub,d.mul,d.sq;r=prefix(d,6)
    f=a('t',1,'f');f2=z(f,'f2');rho=s(f2,1,'rho');Q=p(r['Delta'],rho,'Q')
    oneQ=s(1,Q,'oneQ');den=p(r['Delta'],z(r['c2']),'den')
    V=s(p(f2,s(p(r['c'],'T'),r['R'])),r['c'],'V');vn=a(V,'n','vn');vn2=z(vn,'vn2')
    h=s(s(vn2,p(Q,s(vn2,z(V)))),1,'h')
    bn=p(p(2,oneQ),vn,'bn');AN=a(p(den,h),p(oneQ,rho),'AN')
    N=s(z(AN),p(p(den,rho),z(bn)),'N')
    out=s(p(p(a(r['A0'],1),a(r['A1'],1)),a(N,1)),1,'P12')
    variables=['j','F','alpha','t','T','X','Y','r','eta','zeta','n','gamma']
    return d.packet(variables,out,78,'p12_adaptive_saturated',[r['A0'],r['A1'],N])
def main():
    packets=[('p13_product_degree55.json',make13('product')),('p13_sos_reference.json',make13('sos')),
             ('p12_adaptive_degree78.json',make12())]
    for name,p in packets:
        (ROOT/name).write_text(json.dumps(p,indent=2)+'\n')
        print(name,p['operations'],p['operation_breakdown'])
    # This legacy command requires the original repository layout. Importing
    # DAG and prefix for the portable release does not inspect ancestors.
    base=ROOT.parents[3]/'Computability/DiophantineConsistency/con-zfc-diophantine-forms'
    pins=['73-guard-reanchoring/positive/p13_degree30.json','73-guard-reanchoring/positive/PROOF.md',
          '69-cones-pell/positive/equation.json','69-cones-pell/positive/PROOF.md',
          '74-centered-pell-gaps/positive13/PROOF.md']
    (ROOT/'SOURCE_PINS.json').write_text(json.dumps({s:sha256((base/s).read_bytes()).hexdigest() for s in pins},indent=2)+'\n')
if __name__=='__main__':main()
