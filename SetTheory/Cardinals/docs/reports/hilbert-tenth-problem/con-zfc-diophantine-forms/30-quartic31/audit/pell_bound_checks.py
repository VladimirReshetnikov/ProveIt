if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""Fresh exact-integer diagnostics for the new separating inequalities."""
import json, random, math
from pathlib import Path
r=random.Random(9980712)
positive=signed=0
for j in range(600):
    q=r.choice([16,17,32,64,128]);X=q*r.randrange(1,20);Y=q**3*r.randrange(1,12);E=X*Y
    R=r.randrange(q*(q*q-1)+1,q**4-2);k=E+r.randrange(2,100000);eta=r.randrange(1,k)
    c=k*Y+eta;a=(X+1)*Y;H=4*a+3;delta=a*a+H;ell=E*k*Y
    A=1+ell*(ell+k);G=1+delta*c*c;i=r.randrange(1,10);T=r.randrange(1,20);I=i*c*c;D=1+delta*I*I;Q=delta*delta*I*I
    M=k*(I*I+T*T);v=c*T;b=c+R*D
    assert c<2*k*Y and a+2<2*E and D<(a+2)**2*I*I
    assert Y*Y>20*R and k*Y>8*E
    assert 16*v*v*D<M*M*k*k*Y**4 and 4*b<M*k*Y*Y
    gap=G-A-k*k*Y**4
    assert gap>0 and gap*gap>4*k*k*Y**4*A
    assert (Q-1)*A*M*M>2*Q*(D*v*v+b*b)
    positive+=1
for q in [16,17,32,128]:
 for wsquare in [0,1,4,25]:
  for scale in [-11,-3,-1,1,3,11]:
   for i in [-7,-1,1,5]:
    for T in [-9,-1,0,1,7]:
     X=wsquare*q;Y=scale*q**3;k=2+r.randrange(200);eta=r.randrange(1,k);R=r.randrange(q*(q*q-1)+1,q**4-2)
     c=k*Y+eta;a=(X+1)*Y;H=4*a+3;delta=a*a+H;ell=X*k*Y*Y;A=1+ell*(ell+k);G=1+delta*c*c
     I=i*c*c;D=1+delta*I*I;Q=delta*delta*I*I;v=c*T;b=c+R*D;W=v*v+D+2*b;P=H*W;K=P+1
     assert delta>R and 1<b<Q and W>0 and abs(P)>4
     assert math.gcd(K,H)==1
     assert K*K*G>P*P
     if X:
      assert 4*G<9*A and A>64
      S=4*P*P*A+P*P-K*K*G
      assert S>0 and S*S>16*P**4*A
     signed+=1
p=Path(__file__).resolve().parent/'pell_bound_checks.json'
p.write_text(json.dumps({'status':'PASS','positive_smaller_weight_cases':positive,'signed_sharp_multiplier_two_cases':signed,'method':'Exact integer inequalities, no floating-point square roots. Finite diagnostics only; companion audit supplies unbounded arguments.'},indent=2)+'\n')
print(positive,signed,'PASS')
