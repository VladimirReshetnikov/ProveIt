#!/usr/bin/env python3
"""Independent source and bounded component challenge of the complement obstruction."""
import argparse,hashlib,json,math
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={
'review_complete86_complement_port_math.py':'5bf5183c2e78826e42a836cc035cb0e126cf3fb450749f89282997d8dfc972e8',
'review_complete86_complement_port_math.json':'0b09bf02264908d760c163b11f03cfe6f671a6fd320926df6543cd82c271a2a6',
'review_complete86_complement_port_math.md':'f0cba6a4ad0b1f5488782ae943ac0da547a5903401c2f9a332db3a2fcf7df0b3',
'complete86_factored_first_root.py':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
'complete86_factored_first_root.json':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
'complete86_factored_first_root.md':'9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b',
'complete75_asymmetric_scale_tradeoffs.md':'3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2',
'complete75_normalized_strong87.md':'9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b',
'pell_kernel_half_binomial42.md':'0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992',
'../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md':'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d',
'../../1980/BASE_TWO_PELL_89_PROOF.md':'c5ab081eb26a4730c5b8f33042c4352553fead9c1a83dea3f836a25d5fed472a',
}
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
def need(ok,msg):
 if not ok:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
def digest(a):return hashlib.sha256(json.dumps(a,sort_keys=True,separators=(',',':')).encode()).hexdigest()
# Sparse polynomials in arbitrary named atoms; independent of the author helper.
def atom(x):return {():x}if type(x)is int and x else{}if type(x)is int else{(x,):1}
def add(a,b,sign=1):
 r=dict(a)
 for m,c in b.items():r[m]=r.get(m,0)+sign*c
 return {m:c for m,c in r.items()if c}
def mul(a,b):
 r={}
 for m,c in a.items():
  for n,d in b.items():k=tuple(sorted(m+n));r[k]=r.get(k,0)+c*d
 return {m:c for m,c in r.items()if c}
def sq(a):return mul(a,a)
def pell(A,n):
 # Linear recurrence, deliberately different from the author's power algorithm.
 c0,c1,s0,s1=1,A,0,1
 if n==0:return c0,s0
 for _ in range(1,n):c0,c1=c1,2*A*c1-c0;s0,s1=s1,2*A*s1-s0
 return c1,s1

def verify(root,artifacts):
 blobs={}
 for name,pin in PINS.items():
  base=artifacts if name.startswith('review_complete86_')else root
  b=(Path(base)/name).read_bytes();need(hashlib.sha256(b).hexdigest()==pin,'pin '+name);blobs[name]=b
 author=json.loads(blobs['review_complete86_complement_port_math.json']);parent=json.loads(blobs['complete86_factored_first_root.json'])['forms'][0]
 source=parent['source'];need(parent['normalized']is True and len(source)==86,'actual normalized parent')
 need([r for r in source if 'F'in r[2:]]==[['q_minus_F','-','q','F']],'private removed coordinate')
 expected=[[n,o,'u'if a=='q_minus_F'else a,'u'if b=='q_minus_F'else b]for n,o,a,b in source if n!='q_minus_F']
 need(expected==author['unsafe_child_source'],'literal entire85 source')
 free=['u'if x=='F'else x for x in parent['witnesses']]+['x']+parent['ledger']['fixed_numerals'];need(len(parent['witnesses'])==19,'witness count')
 ready=set(free);defs={}
 for n,o,a,b in expected:
  need(n not in ready and o in('+','-','*'),'exact row')
  need(all(type(x)is int or type(x)is str and x in ready for x in(a,b)),'closed operands');ready.add(n);defs[n]=(o,a,b)
 live=set();stack=['polynomial']
 while stack:
  x=stack.pop()
  if type(x)is int or x in live:continue
  live.add(x)
  if x in defs:stack.extend(defs[x][1:])
 need(set(defs)|set(free)<=live,'every paid gate and input live')
 for name,row in {
  'repunit':('*','Bm1','Jrep'),'q':('+','repunit',1),
  'wn2':('*','w','q'),'sn2':('*','s','n2'),'n2':('*','Lbig','q'),
  'R10b':('+','eta','zeta'),'R10a':('+','ksn2','eta'),'R12':('+','UM','sn2'),
  'gamma_sum':('+','rho','sigma'),'marked_rhs':('-','C_after_alpha','scaled_t'),
  'W':('-','marked_rhs','Z'),'odd_index':('+','scaled_t','inner_bits'),
 }.items():need(defs[name]==row,'literal coordinate definition '+name)
 need(len(expected)==85 and sum(r[1]=='*'for r in expected)==48,'full count')
 # Actual factor formulas at expanded source cuts, independently of receipt formulas.
 cuts={n:atom(s)for n,s in [('q','q'),('wn2','X'),('sn2','Y'),('R10b','k'),('R10a','c'),('R12','a'),('R14','D'),('A','Delta'),('marked_rhs','C'),('index_rhs','kappa'),('exponent_rhs','mu'),('r_lhs','R')]};cuts['repunit']=add(atom('q'),atom(1),-1)
 memo={}
 def expr(n):
  if type(n)is int:return atom(n)
  if n in cuts:return cuts[n]
  if n in memo:return memo[n]
  if n not in defs:return atom(n)
  o,a,b=defs[n];x=expr(a);y=expr(b);v=mul(x,y)if o=='*'else add(x,y,1 if o=='+'else -1);memo[n]=v;return v
 X,Y,k,c,D,Delta,mu,kappa,f,i,o,j,y,h,R,K,C,u,q,z,tau=[atom(n)for n in('X','Y','k','c','D','Delta','mu','kappa','f','i','o','j','y_aux','h','R','Kconstant','C','u','q','zplus','tau_root')]
 L=mul(mul(X,sq(Y)),k);V=add(mul(o,f),c,-1);t=mul(i,sq(c));T=mul(Delta,t);kd=add(k,mul(h,mul(X,Y)),-1)
 formulas=[add(sq(tau),mul(L,add(L,k)),-1),add(sq(D),mul(Delta,sq(c)),-1),add(sq(mu),mul(Delta,sq(kappa)),-1),add(mul(sq(T),add(sq(V),sq(y),-1)),sq(y)),add(kd,R,-1),add(add(mul(add(K,X),C),u),mul(z,add(q,atom(1),-1)),-1),add(sq(f),mul(Delta,sq(t)),-1),add(add(V,mul(j,c),-1),kd)]
 for n,v in zip(FACTORS,formulas):need(expr(n)==v,'actual whole factor '+n)
 cuts.update({n:atom(n)for n in FACTORS});memo.clear();want=atom(1)
 for n in FACTORS:want=mul(want,atom(n))
 need(expr('polynomial')==add(want,atom(1),-1),'complete unit finalizer')
 # Independent bounded arithmetic for the factorial existence lemma.
 factorials=[]
 for ell in range(4,15):
  t0=math.factorial(ell);odd=t0//(t0&-t0)
  need(pow(2,t0,odd)==1%odd,'odd factorial modulus')
  need(t0>=(t0&-t0).bit_length()-1 and all(t0%d==0 for d in range(1,ell+1)),'two-part and every fixed d')
  factorials.append([ell,t0,odd])
 # Different admissible mask pairs; these fixtures check only outer arithmetic.
 outer=[]
 for d,x,t0 in[(4,1,12),(4,2,24),(5,1,20),(5,2,120)]:
  B=1<<d;Q=1<<t0;J=(Q-1)//(B-1);e=2*d*x+3;W=1<<e;C0=W+1;A0=Q*(Q*Q-1)
  need(t0%d==0 and t0>e and A0%t0==0,'outer width')
  masks=[(a,b)for a in range(2,B-1,4)for b in range(4,B-1,8)if a.bit_count()+b.bit_count()==d]
  for mc,mf in masks:
   Tp=mc*J+1+Q*(mf*J-1);need(0<Tp<Q*Q-1 and Tp%4==3,'mask interval')
   for K0 in(1,83,1009):
    residue=pow(2,Tp%t0,Q-1);u0=(1-(K0+residue)*C0)%(Q-1);H0=8*t0+8;uu=u0+(Q-1)*((1<<H0)-1);M=A0*(Q-1);beta=M-A0*u0-Tp;RR=A0*uu+Tp
    need(0<beta<M<Q**4 and RR==M*(1<<H0)-beta,'long complement')
    need(RR.bit_count()==(M-1).bit_count()+H0-(beta-1).bit_count()>3*t0+2,'population')
    alpha=uu-W-2-2*d*x
    need(alpha>0 and uu>Q and RR>max(Q**4,e,3*t0,15) and RR%4==3,'strict outer positivity')
    need((Q*uu-1)*(Q*Q-1)+(mc+Q*(mf+B-1))*J==RR,'literal packed index')
    need(pow(2,RR,Q-1)==residue and ((K0+residue)*C0+uu-1)%(Q-1)==0,'transport integrality')
    outer.append(dict(d=d,x=x,t=t0,MC=mc,MF0=mf,K=K0,R_bits=RR.bit_length(),population=RR.bit_count(),threshold=3*t0+2,negative_F=True))
 # First/main/input canonical data, without the astronomic auxiliary extension.
 ratios=[]
 for R0 in(7,11,15,19,31):
  r=(R0-1)//2;xx=1<<R0;mm=sum(math.comb(2*r,r+j)*xx**j for j in range(r+1));yy=mm//2;aa=yy*(xx+1);AA=aa+2;DD=AA*AA-1;HH=4*aa+3;EE=xx*yy;PP=2*xx*yy*yy+1
  dd,cc=pell(AA,R0);tt,kk=pell(PP,r+1);kk*=2
  need(mm%2==0 and yy>=xx**r//2 and aa>8*r and 6*xx*yy*yy>aa,'explicit converse growth')
  need((yy&-yy).bit_length()-1==R0.bit_count()-2,'valuation')
  eta=cc-kk*yy;zeta=kk-eta;need(eta>0 and zeta>0,'both ratio slacks')
  hh,rem=divmod(kk-R0-1,EE);need(hh>0 and rem==0,'h positive integer')
  LL=xx*yy*yy*kk;need(tt*tt-LL*(LL+kk)==1 and dd*dd-DD*cc*cc==1,'first and main units')
  num=(xx+1)**(2*r);den=xx**r;need(0<4*(num-mm*den)<den,'strict lower binomial tail')
  need(0<(2*cc*den-kk*num)*(xx+1)<32*r*kk*den and 32*r<xx+1,'strict ratio error bound')
  gam,rem=divmod(dd-aa*cc-xx,HH);need(rem==0 and gam>0,'main gamma')
  for ee in(3,5):
   mu0,kappa0=pell(AA,ee);delta,rem=divmod(kappa0-ee,DD);rho,rem2=divmod(mu0-aa*kappa0-(1<<ee),HH)
   need(delta>0 and rem==0 and rho>0 and rem2==0 and gam>rho,'all input/gap quotients positive')
   need(mu0*mu0-DD*kappa0*kappa0==1,'input unit')
  ratios.append(dict(R=R0,X_bits=xx.bit_length(),Y_bits=yy.bit_length(),c_bits=cc.bit_length(),ratio_slacks_positive=True))
 # Odd-index polynomial identity: Q_r(1-C)=(-1)^r Psi_odd_r(C).
 # Both sides obey the same second-order recurrence; these checks validate
 # its base coefficients and further symbolic instances, not a finite proof.
 Bp=atom('C');Q0=atom(1);Q1=add(mul(atom(4),add(atom(1),Bp,-1)),atom(3),-1)
 P0=atom(1);P1=add(mul(atom(4),Bp),atom(1),-1);congruences=0
 for r in range(13):
  qpol=Q0 if r==0 else Q1;ppol=P0 if r==0 else P1
  need(qpol=={m:(-1)**r*c for m,c in ppol.items()},'odd-index transformed polynomial');congruences+=1
  if r>=1:
   Q0,Q1=Q1,add(mul(add(atom(2),mul(atom(4),Bp),-1),Q1),Q0,-1)
   P0,P1=P1,add(mul(add(mul(atom(4),Bp),atom(2),-1),P1),P0,-1)
 # Small generic canonical auxiliary components. They are not complete
 # compiler fixtures or the outer examples' auxiliary towers.
 aux=[]
 for AA in range(2,9):
  R0=3;D0,c0=pell(AA,R0);m=2*c0*R0;f0,psi=pell(AA,m);Delta0=AA*AA-1;i0,rem=divmod(psi,c0*c0);T0=Delta0*psi
  chi,y0=pell(T0,R0);V0,rem2=divmod(chi,T0);o0,rem3=divmod(V0+c0,f0);j0,rem4=divmod(V0+R0,c0)
  need(all(n>0 for n in(i0,T0,V0,o0,j0,y0))and rem==rem2==rem3==rem4==0,'all canonical auxiliary divisions')
  need(f0*f0-Delta0*(i0*c0*c0)**2==1 and T0*T0*(V0*V0-y0*y0)+y0*y0==1,'both canonical normalized units')
  need(V0==o0*f0-c0==j0*c0-R0,'two actual minus congruences')
  aux.append(dict(A=AA,R=R0,m=m,main_c=c0,f_bits=f0.bit_length(),auxiliary_bits=y0.bit_length()))
 return dict(status='PASS_INDEPENDENT_COMPLEMENT_OBSTRUCTION_REVIEW',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),pins=PINS,complete_source=dict(operations=85,M=48,A=37,witnesses=19,all_live=True,source=expected,actual_factor_identities=8,full_finalizer_identities=1),factorial_cases=factorials,outer_cases=outer,canonical_first_main_input_cases=ratios,odd_index_polynomial_cases=congruences,canonical_auxiliary_cases=aux,scope='Independent literal source and component checks plus companion all-parameter proof review. No full valid-width auxiliary tower is materialized; syntactic85 is disproved as a general universal replacement, not certified.')

def main():
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('--root',required=True,type=Path);a.add_argument('--artifacts',type=Path,default=Path(__file__).resolve().parent);a.add_argument('--output',type=Path);a.add_argument('--expect',type=Path);p=a.parse_args();r=verify(p.root,p.artifacts)
 if p.expect:need(exact(r,json.loads(p.expect.read_text())),'typed saved receipt')
 if p.output:p.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
 print(r['status'],len(r['outer_cases']),len(r['canonical_first_main_input_cases']),len(r['canonical_auxiliary_cases']))
if __name__=='__main__':main()
