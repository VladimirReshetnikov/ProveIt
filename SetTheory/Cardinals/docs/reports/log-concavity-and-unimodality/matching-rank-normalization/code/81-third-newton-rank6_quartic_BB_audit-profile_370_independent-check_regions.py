"""Independent endpoint reconstruction: weighted Horner composition and joint Bernstein conversion."""
from pathlib import Path
from math import comb
import sympy as s,sys,json,time,hashlib
from sympy.polys.rings import ring
from sympy.polys.domains import QQ
HERE=Path(__file__).resolve().parent;SOURCE=HERE.parent/'profile_370';mode=sys.argv[1];start=time.time()
p,m,u,q,h,g,z,R=s.symbols('p m u q h g z R')
text=(SOURCE/'schur.txt').read_text();N,D=s.fraction(s.sympify(text));parts=s.Poly(N,q)
if mode in ('zero','zero0'):G=parts.coeff_monomial(1)
elif mode in ('h','h0'):G=m*m*parts.coeff_monomial(1)+m*p*h*parts.coeff_monomial(q)+p*p*h*h*parts.coeff_monomial(q*q)
elif mode=='g':G=u*u*parts.coeff_monomial(1)+u*p*g*parts.coeff_monomial(q)+p*p*g*g*parts.coeff_monomial(q*q)
else:raise RuntimeError('mode')
# Six formal variables plus a homogenizing denominator. This calculation
# does not substitute a rational expression or use the producer's powers.
formal=(p,m,h,g,z,u);base=s.Poly(G,*formal);weighted=(1,1,1,0,0,0)
if mode in ('h','g'):power=max(sum(i*j for i,j in zip(e,weighted)) for e in base.monoms())
else:power=0;weighted=(0,)*6
if mode in ('zero0','h0'):
 rr,*gens=ring('X,W,Y,T',QQ);X,W,Y,T=gens;U=X+1;Z=W+1;M=U+Z+Y;den=rr.one
 P=U*(M-U)+U*(U-1)*T/2;H=Z*M-Z*(Z+1)/2;GG=U*Z;val=(P,M,H,GG,Z,U,den);bounded=(3,)
else:
 rr,*gens=ring('V,W,X,Y,T' if mode!='h' else 'V,W,X,C,T',QQ);V,W,X,Y,T=gens;V+=1;U=V+X;Z=V+W;den=rr.one if mode=='zero' else V*(V+1)
 if mode=='zero':M=U+W+Y
 elif mode=='g':M=(U+W+Y)*den+W*(U*(2*V+W+1)-den)
 else:M=(U+W)*den+W*(U*(2*V+W+1)-den)*Y
 P=U*(M-U*den)+U*(U-1)*T*den/2;H=Z*M-Z*(Z+1)*den/2;GG=U*Z-V*(V+1)/2
 val=(P,M,H,GG,Z,U,den);bounded=(4,3) if mode=='h' else (4,)
terms={e+(power-sum(i*j for i,j in zip(e,weighted)),):QQ.from_sympy(c) for e,c in base.terms()}
# Horner order: group first in p, then m,h,g,z,u and the denominator.
powers={}
def pw(j,e):
 key=j,e
 if key not in powers:powers[key]=val[j]**e
 return powers[key]
def compose(tab,j=0):
 if j==7:return rr.ground_new(next(iter(tab.values())))
 groups={}
 for e,c in tab.items():groups.setdefault(e[j],{})[e]=c
 keys=sorted(groups,reverse=True);out=compose(groups[keys[0]],j+1);previous=keys[0]
 for exponent in keys[1:]:out=out*pw(j,previous-exponent)+compose(groups[exponent],j+1);previous=exponent
 return out*pw(j,previous)
out=compose(terms);print(mode,'Horner expanded',len(out),'seconds',time.time()-start,flush=True)
degrees=tuple(max(e[a] for e in out) for a in bounded);tables={}
# Convert all bounded axes simultaneously, keeping the exact monomial
# indices rather than repeatedly mutating intermediate coefficient tables.
from itertools import product
for e,co in out.items():
 for target in product(*(range(e[axis],degree+1) for axis,degree in zip(bounded,degrees))):
  coef=co
  for axis,degree,k0 in zip(bounded,degrees,target):coef*=QQ(comb(k0,e[axis]),comb(degree,e[axis]))
  index=tuple(0 if j in bounded else v for j,v in enumerate(e));tab=tables.setdefault(target,{});tab[index]=tab.get(index,QQ.zero)+coef
stream=hashlib.sha256();positive=0;stored=0
for key,tab in sorted(tables.items()):
 for e,co in sorted(tab.items()):
  stored+=1
  if co<0:raise RuntimeError(('negative',mode,key,e,str(co)))
  if not co:continue
  positive+=1
  if mode.endswith('0'):line=f'{key[0]}:{e[:-1]}:{co.numerator}/{co.denominator}\n'
  else:line=f'{(0,)+key}:{e}:{co.numerator}/{co.denominator}\n'
  stream.update(line.encode('ascii'))
name={'h0':'zero_overlap_h','zero0':'zero_overlap_zero'}.get(mode,mode);cert=SOURCE/f'certificate_{name}.json';expected=json.loads(cert.read_text()) if cert.exists() else None
if expected is not None:
 if expected['coefficient_sha256']!=stream.hexdigest():raise RuntimeError(('hash mismatch',mode,expected['coefficient_sha256'],stream.hexdigest()))
 if expected['positive_coefficients']!=positive:raise RuntimeError('positive count mismatch')
result={'all_pass':True,'mode':mode,'expanded_terms':len(out),'denominator_power':power,'Bernstein_degrees':degrees,'positive_coefficients':positive,'coefficient_sha256':stream.hexdigest(),'matched_primary_hash':expected is not None,'scalar_sha256':hashlib.sha256(text.encode()).hexdigest(),'seconds':time.time()-start};(HERE/f'check_{mode}.json').write_text(json.dumps(result,indent=2)+'\n');print(result,flush=True)
