"""Exact birational identities for the defect-four quartic.

This verifies the reduction and maps. It does NOT classify integral points.
"""
import sympy as s
from pathlib import Path
import json
K,Z,U,V=s.symbols('K Z U V')
f=150*K**4-120*K**2-30*K+196
X=(28*(Z+14)-30*K)/K**2
Y=((X**2-117600)*K+30*X)/28
shortU=X-40
E=V**2-U**3+122400*U-9415000
num=s.together(E.subs({U:shortU,V:Y})).as_numer_denom()[0]
if s.rem(num,Z**2-f,Z)!=0:raise RuntimeError('forward identity')
XX=U+40; D=XX**2-117600
backK=(28*V-30*XX)/D
backZ=(XX*backK**2+30*backK-392)/28
num=s.together(backZ**2-(150*backK**4-120*backK**2-30*backK+196)).as_numer_denom()[0]
if s.rem(num,E,V)!=0:raise RuntimeError('inverse identity')
for expr,expected in [(backK.subs({U:shortU,V:Y}),K),(backZ.subs({U:shortU,V:Y}),Z)]:
 num=s.together(expr-expected).as_numer_denom()[0]
 if s.rem(num,Z**2-f,Z)!=0:raise RuntimeError('composition')
T_X=s.Rational(23745,196);T_U=T_X-40;T_V=15*T_X/14
if E.subs({U:T_U,V:T_V})!=0:raise RuntimeError('exceptional point')
if s.simplify(backK.subs({U:T_U,V:T_V}))!=0 or s.simplify(backZ.subs({U:T_U,V:T_V}))!=-14:raise RuntimeError('exceptional inverse')
checks=[]
for kk,zz in [(-1,16),(0,14),(1,14),(6,436)]:
 for sign in [-1,1]:
  point={'K':kk,'Z':sign*zz}
  if kk:
   point.update(U=str(s.factor(shortU.subs({K:kk,Z:sign*zz}))),V=str(s.factor(Y.subs({K:kk,Z:sign*zz}))))
  elif sign==1:point['image']='point at infinity'
  else:point.update(U=str(T_U),V=str(T_V))
  checks.append(point)
result={'quartic':'Z^2=150K^4-120K^2-30K+196','quartic_discriminant':str(s.discriminant(f,K)),
        'Weierstrass':'V^2=U^3-122400U+9415000',
        'elliptic_discriminant':str(-16*(4*(-122400)**3+27*9415000**2)),
        'all_symbolic_identities_passed':True,'small_points':checks,
        'scope':'verified reduction and birational maps only; no integral-point completeness claim'}
Path(__file__).with_name('birational_model.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
