"""Pinned source/component checks for the complement-port obstruction proof.

No complete huge Pell tower is materialized. General positivity is proved in
its companion note, using the source-specific canonical construction.
"""
import argparse,hashlib,json,math,random
from pathlib import Path
if not __debug__:raise RuntimeError('Run without -O')
PINS={'complete86_factored_first_root.py':'29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f','complete86_factored_first_root.json':'2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e','complete86_factored_first_root.md':'9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b','complete75_asymmetric_scale_tradeoffs.md':'3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2','complete75_normalized_strong87.md':'9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b','pell_kernel_half_binomial42.md':'0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992','../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md':'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d','../../1980/BASE_TWO_PELL_89_PROOF.md':'c5ab081eb26a4730c5b8f33042c4352553fead9c1a83dea3f836a25d5fed472a'}
FACTORS=['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']
def need(x,msg):
 if not x:raise ValueError(msg)
def exact(a,b):
 if type(a)is not type(b):return False
 if type(a)is dict:return a.keys()==b.keys()and all(exact(a[k],b[k])for k in a)
 if type(a)is list:return len(a)==len(b)and all(exact(x,y)for x,y in zip(a,b))
 return a==b
class P(dict):
 def __init__(self,x=0):
  if type(x)is int:super().__init__({():x}if x else{})
  elif type(x)is str:super().__init__({(x,):1})
  else:super().__init__(x)
 def __add__(self,x):
  r=dict(self)
  for m,c in P(x).items():r[m]=r.get(m,0)+c
  return P({m:c for m,c in r.items()if c})
 __radd__=__add__
 def __neg__(self):return P({m:-c for m,c in self.items()})
 def __sub__(self,x):return self+-P(x)
 def __rsub__(self,x):return P(x)+-self
 def __mul__(self,x):
  r={}
  for a,c in self.items():
   for b,d in P(x).items():m=tuple(sorted(a+b));r[m]=r.get(m,0)+c*d
  return P({m:c for m,c in r.items()if c})
 __rmul__=__mul__
 def __pow__(self,n):
  p=P(1)
  for _ in range(n):p=p*self
  return p

def run(rows,v):
 v=dict(v)
 for n,op,a,b in rows:
  x=a if type(a)is int else v[a];y=b if type(b)is int else v[b];v[n]=x+y if op=='+'else x-y if op=='-'else x*y
 return v

def pell(A,n):
 D=A*A-1;out=(1,0);base=(A,1)
 def mul(a,b):return(a[0]*b[0]+D*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
 while n:
  if n&1:out=mul(out,base)
  n//=2
  if n:base=mul(base,base)
 return out

def outer(d,x,t,K=83,b=3):
 need(d>=4 and t%d==0 and t>2*d*x+b,'Chosen width condition');B=2**d;q=2**t;J=(q-1)//(B-1);MC=B-2;MF0=4;MF=MF0+B-1
 need(t%(t&-t)==0 and q*(q-1)%t==0,'Exact phase divisibility');e=2*d*x+b;W=2**e;C=W+1;Tp=MC*J+1+q*(MF0*J-1);A=q*(q*q-1)
 need(0<Tp<q*q-1 and Tp%4==3 and A%t==0,'Compiler mask bounds/phase');v=pow(2,Tp%t,q-1);u0=(1-(K+v)*C)%(q-1);h0=8*t+8;u=u0+(q-1)*(2**h0-1);M=A*(q-1);beta=M-A*u0-Tp;R=A*u+Tp
 need(0<beta<M<2**(4*t)and R==M*2**h0-beta,'Exact long-complement form');need(R.bit_count()==(M-1).bit_count()+h0-(beta-1).bit_count()>3*t+2,'Exact population threshold')
 alpha=u-W-2-2*d*x;Z=1;need(alpha>0 and u>q and R>max(e,3*q+1,15,q**4),'Outside old positive-width domain')
 need(u-Z-alpha-2*d*x==C and C-Z==W,'Literal input fields')
 need((q*u-Z)*(q*q-1)+(MC+q*MF)*J==R,'Actual source packing');need(R%4==3 and pow(2,R,q-1)==v and((K+v)*C+u-1)%(q-1)==0,'Actual transport residue')
 return dict(d=d,x=x,t=t,Kconstant=K,inner_bits=b,q=q,Jrep=J,MC=MC,MF_source=MF,u=u,alpha=alpha,Z=Z,W=W,C=C,restored_F=q-u,R=R,R_mod_t=R%t,power_residue=v,popcount_R=R.bit_count(),required_population=3*t+2,Tprime=Tp,h0=h0,source_outer_constraints=True,scope='Exact outer fields/congruence; X=2^R and final Pell witnesses are defined symbolically in the proof.')

def verify(root):
 root=Path(root)
 for n,h in PINS.items():need(hashlib.sha256((root/n).read_bytes()).hexdigest()==h,'Pinned source '+n)
 parent=json.loads((root/'complete86_factored_first_root.json').read_text())['forms'][0];need(parent['normalized']is True,'Normalized parent');old=parent['source'];need(len(old)==86,'Actual86 source')
 need([r for r in old if 'F'in r[2:]]==[['q_minus_F','-','q','F']],'F sole literal consumer')
 rows=[[n,op,'u'if a=='q_minus_F'else a,'u'if b=='q_minus_F'else b]for n,op,a,b in old if n!='q_minus_F'];need(len(rows)==85 and sum(r[1]=='*'for r in rows)==48,'Syntactic85 count')
 free=['u'if n=='F'else n for n in parent['witnesses']]+['x']+parent['ledger']['fixed_numerals'];ready=set(free);live={parent['output']}
 for n,op,a,b in rows:need(n not in ready and all(type(v)is int or v in ready for v in(a,b)),'Closed literal child');ready.add(n)
 for n,op,a,b in reversed(rows):need(n in live,'Dead child gate');live.update(v for v in(a,b)if type(v)is str)
 need(set(free)<=live,'All supplied ports live');q,u=P('q'),P('u');need(q-(q-u)==u,'Exact sole affine cut')
 # After that proved local cut, identical operation tuples establish every
 # remaining expression and the complete final product, without sampling.
 need([[n,op,'u'if a=='q_minus_F'else a,'u'if b=='q_minus_F'else b]for n,op,a,b in old if n!='q_minus_F']==rows,'Entire downstream operation identity')
 by={r[0]:r[1:]for r in rows};cache={};cuts={n:P(v)for n,v in {'q':'q','repunit':'repunit','wn2':'X','sn2':'Y','R10b':'k','R10a':'c','R12':'a','R14':'D','A':'Delta','marked_rhs':'C','index_rhs':'kappa','exponent_rhs':'mu','r_lhs':'R'}.items()};cuts['repunit']=P('q')-1
 def expr(n):
  if type(n)is int:return P(n)
  if n in cuts:return cuts[n]
  if n in cache:return cache[n]
  if n not in by:return P(n)
  op,a,b=by[n];a,b=expr(a),expr(b);cache[n]=a*b if op=='*'else a+b if op=='+'else a-b;return cache[n]
 X,Y,k,c,Delta,D,mu,kappa,f,i,o,j,y,h,R,K,C,zplus=[P(n)for n in('X','Y','k','c','Delta','D','mu','kappa','f','i','o','j','y_aux','h','R','Kconstant','C','zplus')];L=X*Y**2*k;V=o*f-c;T=Delta*i*c**2
 manual=[P('tau_root')**2-L*(L+k),D**2-Delta*c**2,mu**2-Delta*kappa**2,T**2*(V**2-y**2)+y**2,k-h*X*Y-R,(K+X)*C+u-zplus*(q-1),f**2-Delta*(i*c**2)**2,V-j*c+k-h*X*Y]
 for n,p in zip(FACTORS,manual):need(expr(n)==p,'Actual source factor '+n)
 # Verify the full final product using independent abstract factor atoms.
 cuts.update({n:P(n)for n in FACTORS});cache.clear();want=P(1)
 for n in FACTORS:want*=P(n)
 need(expr(parent['output'])==want-1,'Actual complete eight-factor finalizer')
 rng=random.Random(85086);numeric=0
 for case in range(24):
  v={n:rng.randint(1,5)for n in free};v.update(Bm1=15,Kconstant=83,twice_cell_bits=8,inner_bits=3,MC=14,MF=19);qv=15*v['Jrep']+1
  if case%2==0:v['u']=qv+rng.randint(1,8)
  ov={n:x for n,x in v.items()if n!='u'};ov['F']=qv-v['u'];a=run(old,ov);b0=run(rows,v)
  need(all(a[n]==b0[n]for n in b0 if n in a)and a['q_minus_F']==v['u'],'Whole source affine pullback evaluation');numeric+=1
 factorials=[]
 for L0 in range(4,11):
  t=math.factorial(L0);two=t&-t;odd=t//two;need(pow(2,t,odd)==1%odd and t>=two.bit_length()-1,'Factorial phase divisibility');need(all(t%d==0 for d in range(1,L0+1)),'All fixed d dividing factorial')
  factorials.append(dict(L=L0,t=t,odd_part=odd,two_part=two))
 examples=[outer(*case)for case in [(4,1,12),(4,2,24),(5,1,20),(5,2,120),(6,1,24),(6,2,120),(7,1,840)]]
 components=[]
 for R0,q0 in[(15,1),(31,2),(63,2)]:
  r=(R0-1)//2;X0=2**R0;Mbin=sum(math.comb(2*r,r+j)*X0**j for j in range(r+1));Y0=Mbin//2;A0=(X0+1)*Y0+2;a=A0-2;Delta0=A0*A0-1;H=4*a+3;E=X0*Y0;P0=2*X0*Y0*Y0+1;D0,c0=pell(A0,R0);tau,k0=pell(P0,r+1);k0*=2
  need(Mbin%2==0 and Y0>=X0**r//2 and Y0%(q0**3)==0 and X0%(q0**3)==0,'Canonical scale integrality beyond old upper bound')
  need((Y0&-Y0).bit_length()-1==r.bit_count()-1,'Exact central valuation');eta=c0-k0*Y0;zeta=k0-eta;need(eta>0 and zeta>0,'Actual strict Pell ratio');hh,rem=divmod(k0-R0-1,E);need(rem==0 and hh>0,'Positive index quotient')
  L0=X0*Y0*Y0*k0;need(tau*tau-L0*(L0+k0)==1 and D0*D0-Delta0*c0*c0==1,'Actual first/main norms')
  num=(X0+1)**(2*r);den=X0**r;need(0<4*(num-Mbin*den)<den and 0<(2*c0*den-k0*num)*(X0+1)<32*r*k0*den,'Direct tail and ratio error inequalities')
  gamma,rem=divmod(D0-a*c0-X0,H);need(rem==0 and gamma>0,'Positive main gap')
  for ee in (3,5):
   mu0,kappa0=pell(A0,ee);delta,rem=divmod(kappa0-ee,Delta0);need(rem==0 and delta>0,'Positive exact input index quotient');rho,rem=divmod(mu0-a*kappa0-2**ee,H);need(rem==0 and rho>0 and gamma-rho>0,'Positive shared input/main quotient split')
   need((2**ee+a*kappa0+rho*H)**2-Delta0*(ee+delta*Delta0)**2==1,'Actual input norm with shared split')
  g0,g1=0,0
  for n in range(1,R0):g0,g1=g1,2*A0*g1-g0+2**(n-1)
  need(g1==gamma,'Gamma recurrence')
  components.append(dict(R=R0,q=q0,outside_old_upper_bound=R0>=q0**4,X_bits=X0.bit_length(),Y_bits=Y0.bit_length(),main_coefficient_bits=c0.bit_length(),exact_valuation=(Y0&-Y0).bit_length()-1,positive_ratio=True,positive_index_quotient=True,input_indices=[3,5],scope='First/main/input components only, not a complete compiler/Pell-auxiliary tuple.'))
 return dict(status='PASS_COMPLEMENT_PORT_SOURCE_AND_COMPONENT_OBSTRUCTION_CHECKS',pins=PINS,counts=dict(source_gates=85,M=48,A=37,affine_cut_identities=1,actual_factor_formulas=8,complete_finalizer_identities=1,whole_affine_evaluations=numeric,factorial_width_checks=len(factorials),outer_constructions=len(examples),canonical_first_main_cases=len(components),input_gap_cases=2*len(components)),unsafe_child_source=rows,unsafe_child_witnesses=['u'if n=='F'else n for n in parent['witnesses']],factor_formulas=[{'name':n,'coefficients':[[list(m),v]for m,v in sorted(p.items())]}for n,p in zip(FACTORS,manual)],factorials=factorials,outer_examples=examples,pell_components=components,scope='Proof note constructs full19-positive-witness zeros symbolically for every fixed valid compiler/input; finite helper checks literal source and bounded components only. No complete huge auxiliary Pell zero is materialized. Syntactic85 is not a universal bound; frozen86 remains unchanged.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();out=verify(a.root)
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'Typed saved receipt mismatch')
 a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'status':out['status'],'counts':out['counts']},sort_keys=True))
if __name__=='__main__':main()
