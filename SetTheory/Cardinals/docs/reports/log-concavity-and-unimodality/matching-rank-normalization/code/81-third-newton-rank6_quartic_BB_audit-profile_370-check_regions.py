import sympy as s,time,json,sys,hashlib
from pathlib import Path
from math import comb
p,m,u,q,h,g,z=s.symbols('p m u q h g z')
V,W,X,Y,T,C=s.symbols('V W X Y T C')
mode=sys.argv[1]
HERE=Path(__file__).resolve().parent
S=s.sympify((HERE/'schur.txt').read_text());num,den=s.fraction(S)
if mode=='zero': expr=num.subs(q,0);gens=(V,W,X,Y,T)
elif mode=='g':expr=s.cancel(num.subs(q,p*g/u)*u*u);gens=(V,W,X,Y,T)
elif mode=='h':expr=s.cancel(num.subs(q,p*h/m)*m*m);gens=(V,W,X,C,T)
else:raise ValueError(mode)
base=s.Poly(expr,p,m,u,h,g,z)
ring=s.polys.rings.ring(gens,s.QQ)[0]
vv,ww,xx,yy,tt=ring.gens;vv+=1
uu=vv+xx;zz=vv+ww;rv=vv*(vv+1)
if mode=='zero':
 den0=ring.one;mn=uu+ww+yy
elif mode=='g':
 den0=rv; yn=ww*(uu*(2*vv+ww+1)-rv)+rv*yy
 mn=(uu+ww)*rv+yn
else:
 den0=rv; yn=ww*(uu*(2*vv+ww+1)-rv)*yy
 mn=(uu+ww)*rv+yn
pn=uu*(mn-uu*den0)+uu*(uu-1)*tt*den0/2
hn=zz*mn-zz*(zz+1)*den0/2
GG=uu*zz-vv*(vv+1)/2
vals={p:pn,m:mn,u:uu,h:hn,g:GG,z:zz}
weight={p:1,m:1,h:1,u:0,g:0,z:0}
deg=max(sum(e*weight[v] for v,e in zip(base.gens,ex)) for ex in base.monoms()) if mode!='zero' else 0
if mode=='zero':weight={v:0 for v in base.gens}
pows={v:[ring.one]+[vals[v]**i for i in range(1,base.degree(v)+1)] for v in base.gens}
denpows=[den0**i for i in range(deg+1)]
out=ring.zero;start=time.time()
for ex,coef in base.terms():
 term=ring.ground_new(coef)*denpows[deg-sum(e*weight[v] for v,e in zip(base.gens,ex))]
 for v,e in zip(base.gens,ex):term*=pows[v][e]
 out+=term
print(mode,'expanded',len(out),'seconds',time.time()-start,flush=True)
# Bernstein transform in the final bounded T, and also C for h case.
axes=[len(gens)-1]+([len(gens)-2] if mode=='h' else [])
polys={(0,):out}
for axis in axes:
 degree=max(ex[axis] for pol in polys.values() for ex in pol)
 new={}
 for key,pol in polys.items():
  for k in range(degree+1):
   dst={}
   for ex,coef in pol.items():
    j=ex[axis]
    if j<=k:
     ee=tuple(0 if a==axis else e for a,e in enumerate(ex))
     dst[ee]=dst.get(ee,0)+coef*s.Rational(comb(k,j),comb(degree,j))
   new[key+(k,)]=dst
 polys=new
 print(mode,'bernstein axis',axis,'degree',degree,'rows',len(polys),flush=True)
neg=[];terms=0;stream=hashlib.sha256();positive_terms=0
for key,poly in polys.items():
 terms+=len(poly)
 bad=[(e,str(c)) for e,c in poly.items() if c<0]
 if bad:neg.append((key,len(bad),bad[:2]))
 for ex,coef in sorted(poly.items()):
  if coef:
   coefficient=s.Rational(coef)
   stream.update(f'{key}:{ex}:{coefficient.p}/{coefficient.q}\n'.encode('ascii'))
   positive_terms+=int(bool(coef>0))
print(mode,'total coefficients',terms,'negative rows',len(neg),'examples',neg[:8],flush=True)
record={'status':'pass' if not neg else 'fail','mode':mode,'expanded_terms':len(out),
        'coefficients_including_zeros':terms,'positive_coefficients':positive_terms,
        'negative_rows':neg,'coefficient_sha256':stream.hexdigest(),
        'scalar_sha256':hashlib.sha256((HERE/'schur.txt').read_bytes()).hexdigest(),
        'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'seconds':time.time()-start}
(HERE/('certificate_'+mode+'.json')).write_text(json.dumps(record,indent=2)+'\n')
if neg:raise ArithmeticError(('negative Bernstein coefficients',mode,neg[:3]))
