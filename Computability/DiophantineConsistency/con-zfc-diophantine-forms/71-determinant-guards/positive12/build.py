import json
from pathlib import Path
from collections import Counter
from source.build12_upstream import DAG,VARS,PORTS

def build():
 d=DAG(); add,sub,mul,sq=d.add,d.sub,d.mul,d.sq
 J=add(mul(6,'j'),1,'J'); qm=mul('beta',J,'qm'); q=add(qm,1,'q')
 q2=sq(q,'q2'); q3=mul(q2,q,'q3')
 qF=sub(q,'F','qF'); C=sub(qF,'alpha','C')
 E=mul('X','Y','E'); k=add('eta','zeta','k'); kY=mul(k,'Y','kY'); c=add(kY,'eta','c'); c2=sq(c,'c2')
 a=add(E,'Y','a'); H=add(mul(4,a),3,'H'); Delta=add(sq(a),H,'Delta')
 ac=mul(a,c,'ac'); b0=add('X',ac,'b0'); ell=mul(E,kY,'ell')
 W=add(mul(qm,k),1,'W'); M0=mul(q3,qm,'M0')
 Bt=sub(mul(add(mul(q,'K0'),'X'),C),mul(q,'F'),'Bt')
 Z=sub(add(mul(M0,add(add(ell,k),'r')),mul(qm,'Y')),mul(mul(q3,W),Bt),'Z')
 rad0=add(mul(ell,add(ell,k)),1,'rad0')
 A0=sub(sq(Z),mul(sq(M0),rad0),'A0')
 G=add(mul(qm,qF),'alpha','G')
 R=add(mul(G,sub(q2,1)),mul(add('MC',mul(q,'MF')),J),'R')
 r0=sub(sub(k,R),1,'r0')
 S=mul(4,mul(q,'Y'),'S'); M=mul(q,S,'M')
 shift=sub(add(mul(M,'gamma'),mul(S,'X')),r0,'shift')
 Dstar=add(mul(M,b0),mul(H,shift),'Dstar')
 A1=sub(sq(Dstar),mul(sq(M),add(mul(Delta,c2),1)),'A1')
 I=mul('i',c2,'I'); I2=sq(I,'I2'); dI2=mul(Delta,I2,'dI2'); D=add(dI2,1,'D'); Q=mul(Delta,dI2,'Q'); dd=sub(Q,1,'dd')
 V=sub(mul(D,sub(mul(c,'T'),R)),c,'V')
 AA=add(a,2,'AA'); t=add(mul(AA,I),'n','t'); vt=add(V,t,'vt')
 normA=add(sub(mul(dd,add(sq(vt),D)),mul(Q,sq(V))),1,'normA')
 normB=mul(mul(2,dd),vt,'normB')
 N=sub(sq(normA),mul(sq(normB),D),'N')
 out=sub(mul(mul(add(1,A0),add(1,A1)),add(1,N)),1,'P12')
 rows,needed=d.live([out]);core,_=d.live([A0,A1,N]);
 return dict(name='adaptive_centered12',domain='strictly positive integers',witnesses=VARS,fixed_numerals=PORTS,source=rows,residuals=[A0,A1,N],output=out,operations=len(rows),system_operations=len(core),operation_breakdown=dict(Counter(row[1] for row in rows)),exact_degree=110,residual_degrees=[15,13,82],coefficient_binding='whole source44 compact tuple beta=2^590069-1; MF is already shifted')
if __name__=='__main__':
 p=build();Path(__file__).with_name('adaptive_centered12.json').write_text(json.dumps(p,indent=2)+'\n');print({k:v for k,v in p.items() if k!='source'})
