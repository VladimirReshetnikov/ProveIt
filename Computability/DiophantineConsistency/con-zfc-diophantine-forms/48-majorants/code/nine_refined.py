"""A sparse-source Jones tail with a sharper polynomial radical majorant.

The h-weight and scale-eight majorant are proved in report.pdf and
proofs/NINE_APPROXIMANT_REVIEW.md.
Every expression here is a polynomial; e is an explicit product, not a quotient.
"""

def finish(d,v,b,B,N,R,cap,certificate=False):
    c,add,mul,sub,pw,save=d.c,d.add,d.mul,d.sub,d.pow,d.save
    U=save('U',mul(pw(N,2),v['w']))
    Y=save('Y',mul(pw(N,2),v['s']))
    M=save('M',mul(R,Y))
    P=save('P',mul(c(2),pw(M,2),U))
    K=save('K',add(R,c(1),mul(v['h'],sub(P,c(1)))))
    A=save('A',mul(M,add(U,c(1))))
    B1=add(mul(c(2),R),c(1))
    W1=mul(b,v['w'])
    C=save('C',add(B1,W1,v['phi']))
    J=save('J',sub(mul(c(4),A),c(5)))
    Q=save('Q',sub(mul(c(3),W1,C),mul(c(2),sub(pw(W1,2),c(1)))))
    Am1=sub(pw(A,2),c(1))
    D=save('D',add(mul(Am1,pw(C,2)),c(1)))
    e=save('e',mul(v['i'],J,C))
    E=save('E',mul(e,D,C))
    F=save('F',add(mul(Am1,pw(E,2)),c(1)))
    G=save('G',add(A,mul(F,sub(add(mul(C,D),c(1)),A))))
    H=save('H',add(B1,mul(v['j'],C)))
    I=save('I',add(mul(sub(pw(G,2),c(1)),pw(H,2)),c(1)))
    a0=save('a0',add(sub(pw(mul(P,K),2),pw(K,2)),c(1)))
    a1=save('a1',mul(c(64),D,F,I))
    u=save('u',mul(J,F))
    vc=save('v',add(mul(Q,F),mul(J,sub(H,C))))
    m=save('m',sub(mul(sub(pw(K,2),mul(c(4),pw(sub(C,mul(K,Y)),2))),cap),mul(c(8),v['g'],pw(K,2))))
    S=save('Smajor',mul(e,sub(sub(mul(c(8),pw(D,2)),mul(c(4),D)),c(1))))
    GH=mul(G,H)
    V=save('Vmajor',mul(S,GH))
    Md=save('Mdiv',add(Q,H))
    Om=save('Omega',mul(u,m))
    E0=save('E0',sub(add(mul(u,add(v['n'],Md)),vc),mul(c(2),Om,Md)))
    Th=save('Theta',sub(E0,mul(Om,v['h'],V)))
    if certificate:
        gap=save('gapDF',sub(mul(pw(e,2),add(mul(c(8),D),c(1))),mul(c(64),D)))
        delta=save('deltaV',add(mul(gap,pw(GH,2)),mul(c(64),D,F,sub(pw(H,2),c(1)))))
        inn=save('inner',sub(add(sub(pw(E0,2),mul(c(2),E0,Om,v['h'],V)),mul(pw(Om,2),pw(v['h'],2),delta)),mul(pw(Om,2),a0)))
    else:
        inn=save('inner',sub(pw(Th,2),mul(pw(Om,2),add(a0,mul(pw(v['h'],2),a1)))))
    return sub(pw(inn,2),mul(c(4),pw(Om,4),pw(v['h'],2),a0,a1))
