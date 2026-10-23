"""Fourteen-positive degree-26 circuit with simultaneous X,Y carriers."""
import json
from pathlib import Path
from candidate14 import Circuit

def construct(shift_x=True,shift_z=False):
    d=Circuit(); add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
    J=add(mul(3,'j'),1); qm=mul('beta',J)
    q=add(qm,1); qF=sub(q,'F'); C=sub(qF,'alpha'); q2=sq(q)
    X=add('x',q) if shift_x else 'x'
    E=mul(X,'Y'); k=add('eta','zeta'); kY=mul(k,'Y'); c=add(kY,'eta')
    a=add(E,'Y'); H=add(mul(4,a),3); Delta=add(sq(a),H); ell=mul(E,kY)
    q3=mul(q2,q); q6=sq(q3)
    G=add(mul(qm,qF),'alpha')
    R=add(mul(G,sub(q2,1)),mul(add('MC',mul(q,'MF')),J))
    S=mul(4,mul(q,'Y')); M=mul(q,S); idx=sub(sub(k,R),1)
    b0=add(X,mul(a,c)); Dstar=add(mul(M,b0),mul(H,add(sub(mul(M,'gamma'),idx),mul(S,X))))
    c2=sq(c); Nm=sub(sq(Dstar),mul(sq(M),add(mul(Delta,c2),1)))
    root0=add(mul(q3,add(ell,'r')),'Y')
    A0=sub(sq(root0),mul(q6,add(mul(ell,add(ell,k)),1)))
    f2=sq('f'); U=mul(Delta,sub(f2,1)); I=mul('i',c2); As=sub(sq(I),U)
    V=sub(mul(f2,sub(mul(c,'T'),R)),c)
    Aa=sub(sub(sq(add(V,'u')),mul(mul(U,'u'),add(add(V,V),'u'))),1)
    KC=mul('K0',C); zq=mul('z',qm); XC=mul(X,C)
    if shift_z: At=add(mul(q,sub(sub(KC,'F'),zq)),XC)
    else: At=sub(add(mul(q,sub(add(KC,qF),zq)),XC),q)
    P=d.sum([sq(A0),sq(Nm),sq(At),sq(Aa),sq(As)])
    live=set(); byid={g['id']:g for g in d.gates}
    def visit(t):
        if isinstance(t,str) and t in byid and t not in live:
            live.add(t)
            for a in byid[t]['args']: visit(a)
    visit(P)
    gates=[g for g in d.gates if g['id'] in live]
    data={'variables':['j','F','alpha','z','f','i','T','x','Y','r','eta','zeta','u','gamma'],
          'fixed_ports':['beta','K0','MC','MF'],
          'gates':gates,'output':P,
          'registers':{'q':q,'X':X,'Y':'Y','E':E,'k':k,'c':c,'a':a,'H':H,'Delta':Delta,'ell':ell,'R':R,'S':S,'M':M,'Dstar':Dstar,'Nm':Nm,'A0':A0,'U':U,'V':V,'Aa':Aa,'As':As,'At':At},
          'shifted_x':shift_x,'shifted_z':shift_z}
    return data

if __name__=='__main__':
    for shift_x in [False,True]:
        for shift_z in [False,True]:
            d=construct(shift_x,shift_z)
            name=f'carrier14_{"shiftx" if shift_x else "rawx"}_{"shiftz" if shift_z else "plainz"}'
            Path(__file__).with_name(name+'.json').write_text(json.dumps(d,indent=2)+'\n')
            print(name,len(d['gates']),{op:sum(g['op']==op for g in d['gates']) for op in ['add','sub','mul']})
