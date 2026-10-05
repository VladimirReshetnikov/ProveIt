"""Independent finite-series reconstruction of marked jets and Gaussian assembly."""
from pathlib import Path
from math import factorial
import json,sympy as s
root=Path(__file__).resolve().parent.parent
r=json.loads((root/'second_correction.json').read_text());e,X,Y=s.symbols('e X Y');rt=s.sqrt(5);N=6
parse=lambda x:s.sympify(x,locals={'e':e,'X':X,'Y':Y})
def simp(x):return s.Poly(s.expand(x),e,X,Y,extension=[rt,s.I]).as_expr()
def arr(f):return [simp(f).coeff(e,i) for i in range(N+1)]
def const(a):return [a]+[s.S.Zero]*N
def add(a,b):return [simp(x+y) for x,y in zip(a,b)]
def scale(a,b):return [simp(x*b) for x in a]
def mul(a,b):return [simp(sum(a[k]*b[j-k] for k in range(j+1))) for j in range(N+1)]
def exp(a):
 if a[0]!=0:raise RuntimeError('exponential constant')
 out=const(s.S.One)
 for j in range(1,N+1):out[j]=simp(sum(k*a[k]*out[j-k] for k in range(1,j+1))/j)
 return out
def power(a,p):
 if s.sympify(p).is_Integer and p>=0:
  out=const(s.S.One)
  for _ in range(int(p)):out=mul(out,a)
  return out
 u=scale(a,1/a[0]);u[0]-=1;out=const(1);v=const(1)
 for j in range(1,N+1):
  v=mul(v,u);out=add(out,scale(v,s.binomial(p,j)))
 return scale(out,a[0]**p)
def log_nonconstant(a):
 out=const(0)
 for j in range(1,N+1):out[j]=simp((j*a[j]-sum(k*out[k]*a[j-k] for k in range(1,j)))/(j*a[0]))
 return out
w=arr(parse(r['implicit_jet']));aa=arr(e*X);bb=arr(e*Y);theta=add(bb,scale(w,2))
EW,EWm=exp(w),exp(scale(w,-1));ET,ETm=exp(theta),exp(scale(theta,-1));EA=exp(aa)
F=add(add(EW,scale(EWm,-1)),scale(mul(EA,add(ET,scale(ETm,-1))),2))
if any(s.simplify(v)!=0 for v in F):raise RuntimeError('implicit residual')
P=add(add(EW,EWm),mul(EA,add(ET,ETm)))
phase=add(log_nonconstant(P),scale(aa,-s.Rational(1,2)))
for j in range(2,7):
 if s.simplify(phase[j]-parse(r['phase_jets'][str(j)]))!=0:raise RuntimeError(('phase',j))
# Algebraic critical amplitude, avoiding acosh and logarithmic Taylor expansion.
pw2=add(add(EW,EWm),scale(mul(EA,add(ET,ETm)),4))
c0=add(scale(add(ET,ETm),s.Rational(1,2)),scale(mul(exp(scale(aa,-1)),add(EW,EWm)),s.Rational(1,4)))
small=add(c0,scale(power(add(mul(c0,c0),const(-1)),s.Rational(1,2)),-1))
A=mul(mul(power(scale(P,s.Rational(1,4)),s.Rational(3,2)),exp(scale(aa,-1))),mul(scale(small,2/(3-rt)),power(scale(pw2,s.Rational(1,10)),-s.Rational(1,2))))
for j in range(1,5):
 if s.simplify(A[j]-parse(r['normalized_amplitude_jets'][str(j)]))!=0:raise RuntimeError(('amplitude',j))
# Marked transfer derivative, reconstructed from the independently derived R3.
N=2
cut=lambda a:a[:3]
P2=cut(P);ivP=power(P2,-1);v2=mul(cut(pw2),ivP)
v3=mul(add(add(cut(EW),scale(cut(EWm),-1)),scale(mul(cut(EA),add(cut(ET),scale(cut(ETm),-1))),8)),ivP)
v4=mul(add(add(cut(EW),cut(EWm)),scale(mul(cut(EA),add(cut(ET),cut(ETm))),16)),ivP)
zeta=scale(mul(cut(small),exp(scale(add(cut(w),cut(bb)),-1))),-1)
zP=add(add(zeta,scale(power(zeta,-1),-1)),scale(mul(cut(EA),add(mul(exp(cut(bb)),power(zeta,2)),scale(mul(exp(scale(cut(bb),-1)),power(zeta,-2)),-1))),2))
R3=const(s.Rational(3,2))
for term in [scale(mul(power(v3,2),power(v2,-3)),s.Rational(5,36)),scale(mul(v4,power(v2,-2)),-s.Rational(1,12)),scale(mul(v3,power(v2,-2)),-s.Rational(1,3)),scale(power(v2,-1),s.Rational(1,3)),mul(P2,power(zP,-1))]:R3=add(R3,term)
B1=add(const(s.Rational(3,8)),scale(R3,-s.Rational(3,2)))
for j in range(3):
 if s.simplify(B1[j]-parse(r['transfer_B1_jets'][str(j)]))!=0:raise RuntimeError(('transfer jet',j,s.simplify(B1[j]),parse(r['transfer_B1_jets'][str(j)]),s.simplify(B1[j]-parse(r['transfer_B1_jets'][str(j)])), 'values',v2[0],v3[0],v4[0],zeta[0],zP[0]))
# Equal-mark Puiseux coefficients by finite algebraic-root operations.
N=6
t=arr((1-e*e)/4);iv=power(t,-1);rad=power(add(const(9),scale(iv,4)),s.Rational(1,2))
vp=scale(add(rad,const(-1)),s.Rational(1,2));vm=scale(add(scale(rad,-1),const(-1)),s.Rational(1,2))
h=add(mul(vp,vp),const(-4));shifted=h[2:]+[s.S.Zero,s.S.Zero]
sq=power(shifted,s.Rational(1,2));z1=scale(add(vp,scale([s.S.Zero]+sq[:6],-1)),s.Rational(1,2))
z2=scale(add(vm,power(add(mul(vm,vm),const(-4)),s.Rational(1,2))),s.Rational(1,2))
Ef=scale(mul(mul(z1,z2),iv),-1)
B2=s.simplify(s.Rational(25,128)-s.Rational(45,16)*Ef[3]/Ef[1]+s.Rational(15,4)*Ef[5]/Ef[1])
if s.simplify(Ef[5]-parse(r['puiseux_e5']))!=0 or s.simplify(B2-parse(r['transfer_B2']))!=0:raise RuntimeError('equal-mark B2')

# Independently compose the finite Gaussian polynomial using convolution.
H={j-2:s.I**j*parse(r['phase_jets'][str(j)]) for j in range(3,7)}
Z={0:s.S.One}
for j in range(1,5):Z[j]=simp(sum(k*H[k]*Z[j-k] for k in range(1,j+1))/j)
amp={0:s.S.One}|{j:s.I**j*parse(r['normalized_amplitude_jets'][str(j)]) for j in range(1,5)}
T={0:s.S.One,1:s.S.Zero,2:parse(r['transfer_B1_jets']['0']),3:s.I*parse(r['transfer_B1_jets']['1']),4:-parse(r['transfer_B1_jets']['2'])+parse(r['transfer_B2'])}
def gauss(poly):
 value=0
 for (i,j),c in s.Poly(s.expand(poly),X,Y).terms():
  if i%2 or j%2:continue
  mi=s.factorial(i)/(2**(i//2)*s.factorial(i//2))*4**(i//2)
  mj=s.factorial(j)/(2**(j//2)*s.factorial(j//2))*10**(j//2)
  value+=c*mi*mj
 return s.simplify(value)
B=[]
for n in (2,4):B.append(gauss(sum(amp[i]*T[j]*Z[n-i-j] for i in range(n+1) for j in range(n-i+1))))
c2=s.simplify(B[1]/16-s.Rational(7,320)*B[0]+s.Rational(49,12800))
if s.simplify(c2-(s.Rational(36,25)-63*rt/125))!=0:raise RuntimeError('c2')
out={'passed':True,'fresh_implicit_residual_orders':6,'fresh_phase_jets':5,'fresh_algebraic_amplitude_jets':4,'fresh_transfer_B1_jets':3,'fresh_equal_mark_B2':True,'b1':str(B[0]),'b2':str(B[1]),'c2':str(c2),'method':'finite convolution recurrences and algebraic amplitude; independent Gaussian contraction'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
