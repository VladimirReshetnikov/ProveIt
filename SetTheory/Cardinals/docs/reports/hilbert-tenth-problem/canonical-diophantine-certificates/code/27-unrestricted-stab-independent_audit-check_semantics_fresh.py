#!/usr/bin/env python3
"""Fresh finite semantic challenges; no submitted code is executed or imported."""
import collections,itertools,json,math,pathlib,random,hashlib
OUT=pathlib.Path(__file__).resolve().parent
checks=collections.Counter()
def need(c,why):
 if not c:raise ValueError(why)
def G(b,n):return (b**n-1)//(b-1)
def pack(ds,b):return sum(x*b**i for i,x in enumerate(ds))
def spread(V,b,n,s):
 C=b**(s-1);E=C**n;P=b**n
 return (V*((E-1)//(C-1))) & ((b-1)*((E*P-1)//(b*C-1)))
def digits(V,b,n):
 a=[]
 for _ in range(n):a.append(V%b);V//=b
 need(V==0,'undeclared high digits');return a
# Sub: exact extracted digit, including U>M and M=0.
for M in range(41):
 ell=2**(M+1);exp=(ell+1)**M
 for U in range(46):
  pos=ell**U;digit=(exp//pos)%ell
  need(digit==(math.comb(M,U) if U<=M else 0),'binomial extraction')
  need(bool(digit%2)==((U&M)==U),'subset parity')
  checks['subset_extractions']+=1
# AND: exhaust all candidate W and both partition differences, rejecting omissions.
for X,Y in itertools.product(range(32),repeat=2):
 for W in range(min(X,Y)+1):
  A,C=X-W,Y-W;ok=(W&X)==W and (W&Y)==W and (A&(A+C))==A
  need(ok==(W==(X&Y)),'AND candidate');checks['and_candidates']+=1
for b in [2,4,8,16]:
 for n in range(1,4):
  for s in range(n+1,n+4):
   for V in range(b**n):
    ds=digits(V,b,n);need(spread(V,b,n,s)==sum(x*b**(s*i) for i,x in enumerate(ds)),'spread');checks['spread_cases']+=1
# Demonstrate why power-of-two bases cannot be casually removed from the lemma.
nonbinary_failure=None
for n in range(1,4):
 for V in range(3**n):
  expected=sum(x*3**((n+1)*i) for i,x in enumerate(digits(V,3,n)))
  if spread(V,3,n,n+1)!=expected:nonbinary_failure={'base':3,'length':n,'stride':n+1,'value':V,'actual':spread(V,3,n,n+1),'expected':expected};break
 if nonbinary_failure:break
need(nonbinary_failure is not None,'non-power-of-two challenge missing')
# All endpoint bit patterns independently challenge the exclusion condition.
for a,b,c in itertools.product(range(8),repeat=3):
 J=G(1024,3);planes=[pack([(v>>i)&1 for i in range(3)],1024) for v in [a,b,c]]
 valid=((planes[1]+planes[2])&J)==planes[1]+planes[2]
 ds=[((a>>i)&1)+2*((b>>i)&1)+4*((c>>i)&1) for i in range(3)]
 need(valid==all(x<=5 for x in ds),'stable digit exclusion');checks['stable_bitplane_cases']+=1
# Exact cap bit masks: permitted interval and first disallowed digit, every bit position.
for L in range(1,26):
 b=32**L;c=b//16-1
 need(c==(1<<(5*L-4))-1,'contiguous cap');need(20+6*c<b and 6*c+5<b,'carry bound')
 for U in [0,1,max(0,c-1),c,c+1,b-1,b,b+1]:need(((U&c)==U)==(0<=U<=c),'cap endpoints')
 for k in range(5*L+2):need((((1<<k)&c)==(1<<k))==(k<5*L-4),'cap bit');checks['cap_bits']+=1
 checks['carry_precisions']+=1
# Every 0/1/cap assignment on the eight interior vertices of 4^3.
b=1024;A=B=C=4;N=A*B*C;X=b**A;Y=b**(A*B)
coords=list(itertools.product(range(A),range(B),range(C)))
idx=lambda v:v[0]+A*v[1]+A*B*v[2]
powers=[b**i for i in range(N)];inside=[v for v in coords if all(0<z<3 for z in v)]
I=sum(powers[idx(v)] for v in inside);derived=b*X*Y*G(b,A-2)*G(X,B-2)*G(Y,C-2);need(I==derived,'interior mask')
dirs=[(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]
for amounts in itertools.product([0,1,63],repeat=8):
 u=dict(zip(inside,amounts));U=sum(t*powers[idx(v)] for v,t in u.items())
 need((U&(63*I))==U,'support cap')
 need(U%b==U%X==U%Y==0,'negative exact division')
 for step,factor,positive in [(dirs[0],b,True),(dirs[1],b,False),(dirs[2],X,True),(dirs[3],X,False),(dirs[4],Y,True),(dirs[5],Y,False)]:
  expected=sum(t*powers[idx(tuple(v[k]+step[k] for k in range(3)))] for v,t in u.items())
  need((U*factor if positive else U//factor)==expected,'neighbor stream')
 checks['all_interior_count_patterns']+=1
# Count streams actually hit shell slots but never exterior; removing shell causes wrap.
v=(3,1,1);bad=b*powers[idx(v)];wrapped=(0,2,1);need(bad==powers[idx(wrapped)],'wrap counterexample')
need((63*I & powers[idx(v)])==0,'shell exclusion')
# Attain both coefficient bounds at radix 32 and at genuine precision 2.
for radix in [32,1024]:
 cap=radix//16-1;need(20+sum([cap]*6)==3*radix//8+14,'max left');need(6*cap+5==3*radix//8-1,'max right');checks['attained_carry_extrema']+=1
# Independent tensor geometry with nonconstant, unequal tile/patch periods.
rng=random.Random(1602026)
geomcases=[(1,1,1,1,1,1),(2,3,1,3,1,2),(1,2,3,2,3,1),(2,2,2,2,1,2),(3,1,2,1,2,3)]
for p,q,r,d,e,f in geomcases:
 nt=p*q*r;nd=d*e*f;L=max(nt,nd)+1;b=32**L
 tx=max(2,math.ceil((q*r+1)/(2*d)),math.ceil((e*f+1)/(2*p)))
 ty=max(2,math.ceil((r+1)/(2*e)),math.ceil((f+1)/(2*q)));tz=2
 hx,hy,hz=p*d*tx,q*e*ty,r*f*tz;A,B,C=2*hx,2*hy,2*hz;AB=A*B
 td=[rng.randrange(6) for _ in range(nt)];dd=[rng.randrange(16) for _ in range(nd)]
 T,D=pack(td,32),pack(dd,32);Tb=spread(T,32,nt,L);Db=spread(D,32,nd,L)
 need(Tb==pack(td,b) and Db==pack(dd,b),'raw conversions')
 tr=spread(Tb,b**p,q*r,2*d*tx);te=spread(tr,b**(A*q),r,2*e*ty)
 H=te*G(b**p,2*d*tx)*G(b**(A*q),2*e*ty)*G(b**(AB*r),2*f*tz)
 dr=spread(Db,b**d,e*f,2*p*tx);de=spread(dr,b**(A*e),f,2*q*ty)
 Delta=de*b**(hx+A*hy+AB*hz)
 decodedH=digits(H,b,A*B*C);decodedD=digits(Delta,b,A*B*C)
 for z in range(C):
  for y in range(B):
   for x in range(A):
    j=x+A*y+AB*z;expect=td[(x%p)+p*(y%q)+p*q*(z%r)]
    need(decodedH[j]==expect,'tile physical phase')
    px,py,pz=x-hx,y-hy,z-hz
    expected=dd[px+d*py+d*e*pz] if 0<=px<d and 0<=py<e and 0<=pz<f else 0
    need(decodedD[j]==expected,'patch physical placement');checks['tensor_slots']+=1
 checks['tensor_geometries']+=1
# Exact finite legal simulations of mandatory repeated and nonleast separators.
def neighbors(v):return [tuple(v[k]+a[k] for k in range(3)) for a in dirs]
def run(initial,seq):
 h=collections.defaultdict(int,initial);u=collections.Counter()
 for v in seq:
  need(h[v]>=6,'illegal advertised sequence');h[v]-=6;u[v]+=1
  for w in neighbors(v):h[w]+=1
 need(all(0<=x<=5 for x in h.values()),'sequence not globally stable');return dict(h),dict(u)
o=(0,0,0);e1=(1,0,0)
H12,U12=run({o:12},[o,o]);need(U12[o]==2 and H12[o]==0 and all(H12[v]==2 for v in neighbors(o)),'height12 fixture')
H124,U124=run({o:12,e1:4},[o,o,e1]);need(U124=={o:2,e1:1},'[12,4] fixture')
initial={o:5,e1:5};u={o:1,e1:1};affected=set(initial)|set(u)
for v in u:affected.update(neighbors(v))
nonleast={v:initial.get(v,0)-6*u.get(v,0)+sum(u.get(w,0) for w in neighbors(v)) for v in affected}
need(all(0<=x<=5 for x in nonleast.values()),'nonleast supersolution');need(all(x<6 for x in initial.values()),'nonleast true odometer zero')
# Conservation challenge on uniform height 5 plus a chip, for fresh arbitrary finite u.
for trial in range(100):
 u={v:rng.randrange(8) for v in itertools.product(range(-1,2),repeat=3)};S=set(u)|{o}
 for v in u:S.update(neighbors(v))
 difference={v:(v==o)-6*u.get(v,0)+sum(u.get(w,0) for w in neighbors(v)) for v in S}
 need(sum(difference.values())==1,'uniform five conservation');need(any(x>0 for x in difference.values()),'uniform five rejected');checks['uniform_five_supersolution_challenges']+=1
receipt={'status':'PASS','checks':dict(checks),'non_power_of_two_counterexample':nonbinary_failure,'row_wrap_without_shell':{'source':[3,1,1],'packed_destination':[0,2,1]},'height12_true_counts':{'origin':U12[o]},'height12_neighbor4_true_counts':{'origin':U124[o],'neighbor':U124[e1]},'nonleast_five_five':{'true_counts':[0,0],'accepted_supersolution_counts':[1,1]},'uniform_five_plus_chip':'No finite support stabilizing supersolution: global excess remains one','limits':'Finite corroboration only; no complete Pell witness or theorem prover execution','submitted_programs_executed':False}
(OUT/'fresh-semantics-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(json.dumps(receipt,indent=2,sort_keys=True))
