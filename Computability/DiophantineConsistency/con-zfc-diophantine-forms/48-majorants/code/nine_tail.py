def finish(d,v,b,B,N,R,cap):
 c=d.c;add=d.add;mul=d.mul;sub=d.sub;pw=d.pow;save=d.save
 U=save('U',mul(pw(N,2),v['w']));Y=save('Y',mul(pw(N,2),v['s']));M=save('M',mul(R,Y))
 P=save('P',mul(c(2),pw(M,2),U));K=save('K',add(R,c(1),mul(v['h'],sub(P,c(1)))))
 A=save('A',mul(M,add(U,c(1))));B1=add(mul(c(2),R),c(1));W1=mul(b,v['w']);C=save('C',add(B1,W1,v['phi']));J=save('J',sub(mul(c(4),A),c(5)))
 Q=save('Q',sub(mul(c(3),W1,C),mul(c(2),sub(pw(W1,2),c(1)))))
 Am1=sub(pw(A,2),c(1));D=save('D',add(mul(Am1,pw(C,2)),c(1)));E=save('E',mul(v['i'],J,D,pw(C,2)));F=save('F',add(mul(Am1,pw(E,2)),c(1)))
 G=save('G',add(A,mul(F,sub(add(mul(C,D),c(1)),A))));H=save('H',add(B1,mul(v['j'],C)));I=save('I',add(mul(sub(pw(G,2),c(1)),pw(H,2)),c(1)))
 a0=save('a0',add(sub(pw(mul(P,K),2),pw(K,2)),c(1)));a1=save('a1',mul(D,F,I));u=save('u',mul(J,F));vc=save('v',add(mul(Q,F),mul(J,sub(H,C))))
 m=save('m',sub(mul(sub(pw(K,2),mul(c(4),pw(sub(C,mul(K,Y)),2))),cap),mul(c(8),v['g'],pw(K,2))))
 V0=save('V0',mul(P,K));MD=mul(A,C);MF=mul(A,E);MI=mul(G,H);V1=save('V1',mul(MD,MF,MI))
 Md=save('Mdiv',add(Q,H));Om=save('Omega',mul(u,m))
 E0=save('E0',sub(add(mul(u,add(v['n'],Md)),vc),mul(c(2),Om,Md)));Th=save('Theta',sub(E0,mul(Om,V0,V1)))
 inn=save('inner',sub(pw(Th,2),mul(pw(Om,2),add(a0,mul(pw(V0,2),a1)))))
 out=sub(pw(inn,2),mul(c(4),pw(Om,4),pw(V0,2),a0,a1))
 return out

def finish_certificate(d,v,b,B,N,R,cap):
 c=d.c;add=d.add;mul=d.mul;sub=d.sub;pw=d.pow;save=d.save
 U=save('U',mul(pw(N,2),v['w']));Y=save('Y',mul(pw(N,2),v['s']));M=save('M',mul(R,Y))
 P=save('P',mul(c(2),pw(M,2),U));K=save('K',add(R,c(1),mul(v['h'],sub(P,c(1)))))
 A=save('A',mul(M,add(U,c(1))));B1=add(mul(c(2),R),c(1));W1=mul(b,v['w']);C=save('C',add(B1,W1,v['phi']));J=save('J',sub(mul(c(4),A),c(5)))
 Q=save('Q',sub(mul(c(3),W1,C),mul(c(2),sub(pw(W1,2),c(1)))))
 Am1=sub(pw(A,2),c(1));D=save('D',add(mul(Am1,pw(C,2)),c(1)));E=save('E',mul(v['i'],J,D,pw(C,2)));F=save('F',add(mul(Am1,pw(E,2)),c(1)))
 G=save('G',add(A,mul(F,sub(add(mul(C,D),c(1)),A))));H=save('H',add(B1,mul(v['j'],C)));I=save('I',add(mul(sub(pw(G,2),c(1)),pw(H,2)),c(1)))
 a0=save('a0',add(sub(pw(mul(P,K),2),pw(K,2)),c(1)));a1=save('a1',mul(D,F,I));u=save('u',mul(J,F));vc=save('v',add(mul(Q,F),mul(J,sub(H,C))))
 m=save('m',sub(mul(sub(pw(K,2),mul(c(4),pw(sub(C,mul(K,Y)),2))),cap),mul(c(8),v['g'],pw(K,2))))
 V0=save('V0',mul(P,K));MD=mul(A,C);MF=mul(A,E);MI=mul(G,H);V1=save('V1',mul(MD,MF,MI))
 Md=save('Mdiv',add(Q,H));Om=save('Omega',mul(u,m))
 E0=save('E0',sub(add(mul(u,add(v['n'],Md)),vc),mul(c(2),Om,Md)));Th=save('Theta',sub(E0,mul(Om,V0,V1)))
 delta=save('deltaV',add(mul(sub(pw(C,2),c(1)),pw(MF,2),pw(MI,2)),mul(D,sub(pw(E,2),c(1)),pw(MI,2)),mul(D,F,sub(pw(H,2),c(1)))))
 inn=save('inner',sub(add(sub(pw(E0,2),mul(c(2),E0,Om,V0,V1)),mul(pw(Om,2),pw(V0,2),delta)),mul(pw(Om,2),a0)))

 out=sub(pw(inn,2),mul(c(4),pw(Om,4),pw(V0,2),a0,a1))
 return out
