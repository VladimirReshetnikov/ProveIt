#!/usr/bin/env python3
"""Emit/audit 32 positive variables, 23 quadratics, and 50-integer variant.

Python standard library only. This checks exact algebra and degree; the
inherited Pell/compiler theorems are mathematical proof dependencies.
"""
from pathlib import Path
import json
from sparse_poly import Poly

ROOT=Path(__file__).resolve().parent
names='J F alpha z f h i s w tau eta zeta y gamma o j N E P c a X D C2 G L F2 V g I Baux Delta'.split()
globals().update({name:Poly.var(name) for name in names})
beta,K0,MC,MF=(Poly.var(name) for name in ('beta','K0','MC','MF'))
q=beta*J+1
k=eta+zeta
H=4*a+3
C=q-F-alpha
R=k-1-h*E
eqs=[
 (L,q*q-1), (N,q*(L+1)), (X,w*q), (a,E+s*N), (E,X*(a-E)),
 (c,k*(a-E)+eta), (P,E*(c-eta)+k), (tau*tau,P*(P-k)+1),
 (D,X+a*c+gamma*H), (Delta,a*a+H), (C2,c*c), (D*D,Delta*C2+1),
 (G,(q-1)*(q-F)+alpha), (R,L*G+(MC+q*MF)*J),
 ((K0+w)*C,F+z*(q-1)), (F2,f*f), (V,o*f-c), (V,j*c-R),
 (g,y*y-V*V), (I,i*C2), (Baux,I*I), (Baux,Delta*(F2-1)),
 (y*y,Baux*g+1),
]
res=[l-r for l,r in eqs]
degrees=[r.degree(names) for r in res]
assert len(names)==32 and len(eqs)==23 and max(degrees)==2
assert set().union(*(r.symbols for r in res))==set(names)|{'beta','K0','MC','MF'}
assert res[7].terms[(("tau",2),)]==1
assert all('tau' not in r.symbols for n,r in enumerate(res) if n!=7)

# First norm lowering identity.
Y0,X0,k0,tau0=(Poly.var(name) for name in ('Y0','X0','k0','tau0'))
P0=X0*Y0*(k0*Y0)+k0
assert tau0**2-P0*(P0-k0)-1==tau0**2-X0*Y0**2*(X0*Y0**2+1)*k0**2-1

# Exact restoration identities, with c*j kept as numerator.
T0,R0,c0,f0,o0=(Poly.var(name) for name in ('T0','R0','c0','f0','o0'))
auxV=c0*(T0*f0-1)-R0*f0**2
rest_o=c0*T0-R0*f0
rest_j_num=c0*T0*f0-c0-R0*(f0**2-1)
assert auxV==rest_o*f0-c0
assert auxV+R0==rest_j_num
assert f0*(o0*f0+R0)-o0*(f0**2-1)==o0+R0*f0
assert (o0+R0*f0)*f0-c0-R0*f0**2==o0*f0-c0

A0,b0,V1,y1=(Poly.var(name) for name in ('A0','b0','V1','y1'))
assert (b0*(V1**2-y1**2)+y1**2)-(A0*(V1**2-y1**2)+y1**2)==(b0-A0)*(V1**2-y1**2)

# Only these nine original quantities require positive domains for soundness.
guarded='J F alpha z i s w eta zeta'.split()
integer_names=[]
sub={}
for name in names:
 if name in guarded:
  nms=[name+'_'+str(t) for t in range(1,4)]
  us=[Poly.var(n) for n in nms]
  integer_names+=nms
  sub[name]=1+us[0]**2+us[1]**2+us[2]*(us[2]+1)
 else:
  integer_names.append(name)
integer_res=[r.substitute(sub) for r in res]
integer_degrees=[r.degree(integer_names) for r in integer_res]
assert len(guarded)==9 and len(integer_names)==50 and max(integer_degrees)==4
packet={
 'title':'32 positive unknowns, 23 quadratic equations, one quartic',
 'repository_pin':'3b201cdea32d2c816f5f3d20734051f25fd3ef14',
 'coefficient_recipe':'compiler/cross_constants.json: the same four fixed cross-compiler numerals; MF is shifted source port. The coherent original 06-blank67 tuple also works.',
 'constants':['beta=B-1','K0','MC','MF'],
 'variables':names,'domain':'strictly positive integers',
 'affine_abbreviations':{'q':'beta*J+1','k':'eta+zeta','H':'4*a+3','C':'q-F-alpha'},
 'quadratic_abbreviation':{'R':'eta+zeta-1-h*E'},
 'equations':[f'{l} = {r}' for l,r in eqs],
 'residuals':[str(r) for r in res],
 'residual_degrees':degrees,
 'single_polynomial':'sum(r*r for r in the 23 literal residuals)',
 'single_polynomial_exact_degree':4,
 'nonnegative_version':'replace each variable x by n_x+1',
 'integer_variant':{
  'positive_guarded_variables':guarded,
  'positive_substitution':'Pos(u,v,w)=1+u^2+v^2+w*(w+1)',
  'variables':integer_names,'variable_count':50,
  'residuals':[str(r) for r in integer_res],
  'max_residual_degree':4,'sum_of_squares_exact_degree':8,
  'soundness':'signed auxiliary rank proof and signed main-root lemma; not a tuplewise positive projection',
 },
 'formal_status':'ordinary proof uses inherited compiler/Pell lemmas; not kernel checked',
}
(ROOT/'quartic32.json').write_text(json.dumps(packet,indent=2)+'\n')
(ROOT/'quartic32_checks.json').write_text(json.dumps({
 'variables':len(names),'equations':len(eqs),'residual_degrees':degrees,
 'quartic_degree_certificate':'coefficient of tau^4 in the sum of squares is 1',
 'integer_variables':len(integer_names),'integer_residual_degrees':integer_degrees,
 'integer_degree_certificate':'residual 1 has nonzero degree-four leading part -beta^2*(J_1^2+J_2^2+J_3^2)^2',
 'first_norm_identity':True,'quotient_restoration_identities':True,
 'auxiliary_coefficient_identity':True,
 'scope':'symbolic arithmetic and counts only; no compiler/Pell theorem formal verification',
},indent=2)+'\n')
print('PASS: 32 positive variables / 23 quadratic equations / degree 4; 50 integer variables / degree 8.')

