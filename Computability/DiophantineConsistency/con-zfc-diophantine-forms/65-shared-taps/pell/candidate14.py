"""Research circuit for a 14-positive-variable degree-30 equation.
No empirical solvability checks claim an unbounded theorem.
"""
import json
from pathlib import Path

class Circuit:
    def __init__(self): self.gates=[]; self.memo={}
    def op(self,op,a,b):
        if op in ('add','mul') and str(a)>str(b): a,b=b,a
        key=(op,a,b)
        if key not in self.memo:
            n='v'+str(len(self.gates)); self.memo[key]=n
            self.gates.append({'id':n,'op':op,'args':[a,b]})
        return self.memo[key]
    def add(self,a,b): return self.op('add',a,b)
    def sub(self,a,b): return self.op('sub',a,b)
    def mul(self,a,b): return self.op('mul',a,b)
    def sq(self,a): return self.mul(a,a)
    def sum(self,ls):
        z=ls[0]
        for a in ls[1:]: z=self.add(z,a)
        return z

def construct(shift=False,pack=False):
    d=Circuit(); add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    qm=mul('beta','J'); q=add(qm,1); qF=sub(q,'F'); C=sub(qF,'alpha')
    X=mul('w',q); E=mul(X,'Y'); k=add('eta','zeta'); kY=mul(k,'Y'); c=add(kY,'eta')
    a=add(E,'Y'); H=add(mul(4,a),3); Delta=add(sq(a),H); ell=mul(E,kY)
    q2=sq(q); q3=mul(q2,q); q6=sq(q3)
    G=add(mul(qm,qF),'alpha')
    R=add(mul(G,sub(q2,1)),mul(add('MC',mul(q,'MF')),'J'))
    M=mul(4,mul(q,'Y')); idx=sub(sub(k,R),1)
    b0=add(X,mul(a,c)); Dstar=add(mul(M,b0),mul(H,sub(mul(M,'gamma'),idx)))
    c2=sq(c); Nm=sub(sq(Dstar),mul(sq(M),add(mul(Delta,c2),1)))
    root0=add(mul(q3,add(ell,'r')),'Y')
    A0=sub(sq(root0),mul(q6,add(mul(ell,add(ell,k)),1)))
    f2=sq('f'); U=mul(Delta,sub(f2,1)); I=mul('i',c2); As=sub(sq(I),U)
    V=sub(mul(f2,sub(mul(c,'T'),R)),c)
    Aa=sub(sub(sq(add(V,'u')),mul(mul(U,'u'),add(add(V,V),'u'))),1)
    transport_base=mul(add('K0','w'),C); transport_z=mul('z',qm)
    if shift: At=sub(sub(transport_base,'F'),transport_z)
    else: At=sub(sub(add(transport_base,qF),transport_z),1)
    if pack:
        # At+1 is N_t; 1+Nm cannot be -1 modulo 4.
        coupled=sub(mul(add(At,1),add(Nm,1)),1)
        P=d.sum([sq(A0),sq(coupled),sq(Aa),sq(As)])
    else: P=d.sum([sq(A0),sq(Nm),sq(At),sq(Aa),sq(As)])
    live=set()
    byid={g['id']:g for g in d.gates}
    def visit(t):
        if isinstance(t,str) and t in byid and t not in live:
            live.add(t)
            for a in byid[t]['args']: visit(a)
    visit(P)
    gates=[g for g in d.gates if g['id'] in live]
    data={'variables':['J','F','alpha','z','f','i','T','w','Y','r','eta','zeta','u','gamma'],
          'fixed_ports':['beta','K0','MC','MF'],'gates':gates,'output':P,
          'registers':{'q':q,'X':X,'Y':'Y','E':E,'k':k,'c':c,'a':a,'H':H,'Delta':Delta,'ell':ell,'R':R,'M':M,'Dstar':Dstar,'Nm':Nm,'A0':A0,'U':U,'V':V,'Aa':Aa,'As':As,'At':At},
          'shifted_transport':shift,'packed_main_transport':pack}
    return data

if __name__=='__main__':
    for shift in [False,True]:
        for pack in [False,True]:
            d=construct(shift,pack)
            name=f'candidate14_{"shifted" if shift else "plain"}_{"packed" if pack else "sos"}'
            Path(__file__).with_name(name+'.json').write_text(json.dumps(d,indent=2)+'\n')
            print(name,len(d['gates']),{op:sum(g['op']==op for g in d['gates']) for op in ['add','sub','mul']})
