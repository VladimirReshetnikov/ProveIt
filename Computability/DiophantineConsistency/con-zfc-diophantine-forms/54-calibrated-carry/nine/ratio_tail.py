#!/usr/bin/env python3
"""Authored source-parametric nine-variable Jones tail.

The caller owns the source circuit.  `d` needs c,add,sub,mul,pow,save methods
with the round-7 Circuit interface; all inputs and outputs are node indices.
`v` maps the mixed-domain witnesses h,s,w,phi,i,j,n to their nodes. Source
nodes b,g are passed separately. No external code is imported or executed.
"""

def append_ratio_tail(d, *, R,N,b,g,cap,v,majorant='quotient2048',certificate=False):
 c=d.c;add=d.add;sub=d.sub;mul=d.mul;pw=d.pow;sv=d.save
 U=sv('U',mul(pw(N,2),v['w']));Y=sv('Y',mul(pw(N,2),v['s']));M=sv('M',mul(R,Y))
 P=sv('P',mul(c(2),pw(M,2),U));K=sv('K',add(R,c(1),mul(v['h'],sub(P,c(1)))))
 A=sv('A',mul(M,add(U,c(1))));Asq=pw(A,2);B1=sv('B1',add(mul(c(2),R),c(1)));W1=mul(b,v['w']);C=sv('C',add(B1,W1,v['phi']))
 J=sv('J',sub(mul(c(4),A),c(5)));Q=sv('Q',sub(mul(c(3),W1,C),mul(c(2),sub(pw(W1,2),c(1)))))
 am1=sub(Asq,c(1));D=sv('D',add(mul(am1,pw(C,2)),c(1)))
 k=sv('k',mul(v['i'],J,C));L=sv('L',mul(k,D));E=sv('E',mul(L,C));F=sv('F',add(mul(am1,pw(E,2)),c(1)))
 L0=sv('Lstar',sub(add(mul(C,D),c(1)),A))
 G=sv('G',add(A,mul(F,L0)));H=sv('H',add(C,mul(F,add(B1,mul(v['j'],C)))))
 GH=sv('GH',mul(G,H));I=sv('I',add(sub(pw(GH,2),pw(H,2)),c(1)))
 V0=sv('V0',mul(P,K));a0=sv('a0',add(sub(pw(V0,2),pw(K,2)),c(1)));a1=sv('a1',mul(D,F,I))
 m=sv('m',sub(mul(sub(pw(K,2),mul(c(4),pw(sub(C,mul(K,Y)),2))),cap),mul(c(8),g,pw(K,2))))
 B8=sv('B8',sub(sub(mul(c(8),pw(D,2)),mul(c(4),D)),c(1)))
 if majorant=='simple64':
  scale=64;T=sv('Tpair',mul(k,B8));V1=sv('V1',mul(T,GH))
  if certificate:
   defect=sv('Delta1',add(mul(sub(mul(add(mul(c(8),D),c(1)),pw(k,2)),mul(c(64),D)),pw(GH,2)),mul(c(64),D,F,sub(pw(H,2),c(1)))))
 elif majorant in ('support2048','quotient2048'):
  scale=2048**2;ksq=pw(k,2)
  # Algebraically identical to the four N_j quotient construction, with
  # shared products collected to avoid redundant gates.
  Nstar=sv('Nstar',add(mul(c(2),G),L0))
  T6=sv('T6',mul(k,add(sub(mul(c(128),B8,Nstar),mul(ksq,sub(mul(c(16),add(B8,D)),c(8)),L0)),mul(C,sub(mul(c(14),ksq),c(192))))))
  if majorant=='support2048':
   correction=add(mul(c(256),v['i'],add(ksq,c(2))),c(2048))
  else:
   qA=add(sub(mul(c(896),Asq),mul(c(4256),A)),c(8442))
   qB=sub(mul(c(576),A),c(2151))
   quotient=sv('quotient_correction',add(mul(C,sub(mul(C,qB),qA)),c(1024)))
   correction=add(mul(pw(v['i'],3),quotient),mul(c(288),v['i']),c(2048))
  T=sv('Tmajor',add(T6,correction));V1=sv('V1',mul(T,H))
  if certificate:
   # Independent exact expanded defect, never used in the operation-minimal
   # equation. It resolves all high-degree cancellation in the degree proof.
   import json
   from pathlib import Path
   if majorant!='quotient2048': raise ValueError('Use primary form for support2048 fallback')
   data=json.loads(Path(__file__).with_name('REFINED_DEFECT_POLYNOMIAL.json').read_text())
   deltaT=sv('DeltaT',add(*(mul(c(t['coefficient']),pw(A,t['powers'][0]),pw(C,t['powers'][1]),pw(v['i'],t['powers'][2])) for t in data['terms'])))
   defect=sv('Delta1',add(mul(pw(H,2),deltaT),mul(c(scale),D,F,sub(pw(H,2),c(1)))))
 else: raise ValueError(majorant)
 O=sv('Omega',mul(J,m));E0=sv('E0',add(mul(J,v['n']),Q));shift=add(V0,V1)
 theta=sv('Theta',sub(E0,mul(O,shift)))
 if certificate:
  inner=sv('inner',add(sub(pw(E0,2),mul(c(2),E0,O,shift)),mul(pw(O,2),add(sub(pw(K,2),c(1)),defect,mul(c(2),V0,V1)))))
 else:inner=sv('inner',sub(pw(theta,2),mul(pw(O,2),add(a0,mul(c(scale),a1)))))
 return sv('F9',sub(pw(inner,2),mul(c(4*scale),pw(O,4),a0,a1)))


def exact_degree(majorant, degree_R, degree_N, degree_cap):
 if majorant=='simple64':return 188*degree_R+400*degree_N+4*degree_cap+232
 if majorant=='support2048':return 158*degree_R+344*degree_N+4*degree_cap+204
 if majorant=='quotient2048':return 154*degree_R+328*degree_N+4*degree_cap+196
 raise ValueError(majorant)
