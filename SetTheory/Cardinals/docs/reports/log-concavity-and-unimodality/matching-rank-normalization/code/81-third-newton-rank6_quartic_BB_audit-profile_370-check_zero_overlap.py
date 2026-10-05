import sympy as s,time,json,sys,hashlib
from pathlib import Path
from math import comb
p,m,u,q,h,g,z=s.symbols('p m u q h g z');X,W,Y,T=s.symbols('X W Y T')
HERE=Path(__file__).resolve().parent
S=s.sympify((HERE/'schur.txt').read_text());num,den=s.fraction(S)
mode=sys.argv[1]
if mode=='h':base=s.Poly(s.cancel(num.subs(q,p*h/m)*m*m),p,m,u,h,g,z)
elif mode=='zero':base=s.Poly(num.subs(q,0),p,m,u,h,g,z)
else:raise ValueError(mode)
ring=s.polys.rings.ring((X,W,Y,T),s.QQ)[0]
x,w,y,t=ring.gens
uu=x+1;zz=w+1;mm=uu+zz+y
pp=uu*(zz+y)+uu*(uu-1)*t/2
hh=zz*mm-zz*(zz+1)/2;gg=uu*zz
values={p:pp,m:mm,u:uu,h:hh,g:gg,z:zz}
powers={v:[ring.one]+[values[v]**i for i in range(1,base.degree(v)+1)] for v in base.gens}
out=ring.zero;start=time.time()
for ex,coef in base.terms():
 term=ring.ground_new(coef)
 for v,e in zip(base.gens,ex):term*=powers[v][e]
 out+=term
print('expanded',len(out),'seconds',time.time()-start,flush=True)
deg=max(e[-1] for e in out)
rows=[];stream=hashlib.sha256();positive=0;total=0;negative=0
for k in range(deg+1):
 b={}
 for ex,coef in out.items():
  j=ex[-1]
  if j<=k:
   key=ex[:-1];b[key]=b.get(key,0)+coef*s.Rational(comb(k,j),comb(deg,j))
 neg=[(e,c) for e,c in b.items() if c<0]
 rows.append((k,len(b),len(neg)));print(rows[-1],flush=True)
 total+=len(b);negative+=len(neg)
 for ex,coef in sorted(b.items()):
  if coef:
   coefficient=s.Rational(coef)
   stream.update(f'{k}:{ex}:{coefficient.p}/{coefficient.q}\n'.encode('ascii'))
   positive+=int(bool(coef>0))
record={'status':'pass' if not negative else 'fail','mode':mode,'expanded_terms':len(out),
        'coefficients_including_zeros':total,'positive_coefficients':positive,
        'negative_coefficients':negative,'rows':rows,'coefficient_sha256':stream.hexdigest(),
        'scalar_sha256':hashlib.sha256((HERE/'schur.txt').read_bytes()).hexdigest(),
        'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'seconds':time.time()-start}
(HERE/('certificate_zero_overlap_'+mode+'.json')).write_text(json.dumps(record,indent=2)+'\n')
if negative:raise ArithmeticError(('negative Bernstein coefficient',mode,negative))
