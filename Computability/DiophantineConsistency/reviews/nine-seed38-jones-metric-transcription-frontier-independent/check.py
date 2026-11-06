import hashlib,json,subprocess,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site
D=Path(__file__).resolve().parents[2];p=D/'research/nine-seed38-jones-metric-survey'
def sha(x):return hashlib.sha256(Path(x).read_bytes()).hexdigest()
assert sha(p/'check.py')=='dfac7692bf4f283063418c092799cf681d307abf46c80ea71bd0f496f9d2543e' and sha(p/'result.json')=='66dd437f22625371b2b0d9cdfb89458d2f16969c771bd8decfcd102a8f2c6239'
a=subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],timeout=30);assert hashlib.sha256(a).hexdigest()==sha(p/'result.json');survey=json.loads(a)
# Independently propagate affine bounds a*L+b for all L>=25. Each max is
# checked by slope and at the lower endpoint, so this verifies all nu>=1.
def add(*ps):return tuple(map(sum,zip(*ps)))
def power(p,n):return p[0]*n,p[1]*n
def plus(*ps):
 best=max(ps,key=lambda p:25*p[0]+p[1]);assert all(best[0]>=p[0] and 25*(best[0]-p[0])+best[1]-p[1]>=0 for p in ps),(best,ps);return best
zero=(0,0);one=(0,1);L=(1,0)
# rankCode: B=b^5, q=B^L, n=q^16, e<=5L, ell<=L,
# lambda<=5(4L-1). All z, y, x are closed after removeInput.
b=one;B=power(b,5);q=power(L,5);n=power(q,16);e=power(L,5);ell=L;lam=add(power(L,20),(0,-5));g=one;theta=B
R=plus(add(plus(g,add(e,power(q,3)),add(ell,power(q,5)),add(plus(add(plus(e,lam),power(plus(zero,B,g),4)),add(lam,B),add(lam,B,power(q,4))),power(q,7))),plus(power(n,2),n)),add(plus(power(q,3),add(b,ell),ell,add(theta,lam,power(q,3)),add(plus(B,zero),power(q,8))),plus(power(n,2),zero)))
G=add(b,L);h=s=w=phi=i=j=t=one
U=add(power(n,2),w);Y=add(power(n,2),s);M=add(R,Y);P=add(power(M,2),U);K=plus(R,zero,add(h,plus(P,zero)));A=add(M,plus(U,zero));Bp=plus(R,zero);W=add(b,w);C=plus(Bp,W,phi);J=plus(A,zero);Q=plus(add(W,C),plus(power(W,2),zero));Dd=plus(add(plus(power(A,2),zero),power(C,2)),zero);E=add(i,J,Dd,power(C,2));F=plus(add(plus(power(A,2),zero),power(E,2)),zero);Gp=plus(A,add(F,plus(add(C,Dd),zero,A)));H=plus(Bp,add(j,C));I=plus(add(plus(power(Gp,2),zero),power(H,2)),zero)
A0=plus(add(plus(power(P,2),zero),power(K,2)),zero);A1=add(Dd,F,I);V0=plus(power(A0,2),zero);V1=plus(power(A1,2),zero);divisor=power(add(J,F),2);dividend=power(plus(add(Q,F),add(J,plus(H,C))),2);margin=plus(add(power(K,2),G),add(power(plus(C,add(K,Y)),2),G),add(g,power(K,2)));Kc=add(divisor,plus(margin,zero));T=plus(add(divisor,t),dividend,add(Kc,plus(dividend,add(V0,V1))));result=plus(power(plus(power(T,2),add(power(Kc,2),A0),add(power(Kc,2),power(V0,2),A1)),2),add(power(T,2),power(Kc,2),A0))
assert result==(291404,860),result
nu=38;lv=5**(nu+1)
intermediates={'b':b,'B':B,'q':q,'N':n,'e':e,'ell':ell,'lam':lam,'g':g,'theta':theta,'R':R,'G':G,'h':h,'s':s,'w':w,'phi':phi,'i':i,'j':j,'t':t,'U':U,'Y':Y,'M':M,'P':P,'K':K,'A':A,'Bprime':Bp,'W':W,'C':C,'J':J,'Q':Q,'D0':Dd,'E':E,'F':F,'Gp':Gp,'H':H,'I':I,'A0':A0,'A1':A1,'V0':V0,'V1':V1,'divisor':divisor,'dividend':dividend,'margin':margin,'Kc':Kc,'T':T,'result':result}
for key,(slope,offset) in intermediates.items():assert int(survey['degree_bounds'][key])==slope*lv+offset,key
assert int(survey['candidate_bound'])==result[0]*lv+result[1] and survey['star_vectors_with_coordinate_sum_4']==123410 and int(survey['star_enumeration_vectors'])==5**40 and int(survey['lambda_range_terms'])==4*lv
print(json.dumps({'status':'PASS_MANUAL_TRANSCRIPTION_AND_EXTERNAL_BOUND','source_survey_sha256':sha(p/'check.py'),'reviewed_affine_degree_bound':list(result),'bound_formula':'291404 * 5^39 + 860','candidate_bound':survey['candidate_bound'],'range_scope':'Affine max choices validated for every L >= 25, including nu=38','scope':'Manual source comparison and symbolic arithmetic only; not a Lean theorem, no exact degree/noncancellation, no size or literal graph claim.'},indent=2,sort_keys=True))
