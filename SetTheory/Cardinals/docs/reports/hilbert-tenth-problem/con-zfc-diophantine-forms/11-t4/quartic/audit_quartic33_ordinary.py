"""Independent quadratic lift of the ordinary-strong six-equation hybrid."""
import json
from pathlib import Path
import sympy as S
HERE=Path(__file__).resolve().parent
names='J F alpha z f h i o s w tau eta zeta y gamma N E P c a X D C2 G L R F2 V0 V g I B Delta'.split()
v=dict(zip(names,S.symbols(' '.join(names))))
beta,K,MC,MF=S.symbols('beta K MC MF')
q=beta*v['J']+1
k=v['eta']+v['zeta']
loc=dict(v,beta=beta,K=K,MC=MC,MF=MF,q=q,k=k)
equations=[
('L','q**2-1'),('N','(L+1)*q'),('X','w*q'),('a','E+N*s'),
('E','X*(a-E)'),('c','eta+(a-E)*k'),('P','E*(c-eta)+k'),
('tau**2','P*(P-k)+1'),('D','X+a*c+gamma*(4*a+3)'),
('Delta','a**2+4*a+3'),('C2','c**2'),('D**2-1','C2*Delta'),
('k','E*h+R+1'),('G','(q-1)*(q-F)+alpha'),
('R','G*L+J*(MC+q*MF)'),
('(K+w)*(q-F-alpha)+q-F-z*(q-1)','1'),
('F2','f**2'),('V0','o*f-1'),('V','c*V0-R*F2'),
('g','y**2-V**2'),('I','C2*i'),('B','I**2'),
('B','Delta*(F2-1)'),('y**2-B*g','1')]
res=[S.expand(S.sympify(l,locals=loc)-S.sympify(r,locals=loc)) for l,r in equations]
degrees=[S.Poly(r,*v.values()).total_degree() for r in res]
assert len(names)==len(set(names))==33 and len(res)==24 and max(degrees)==2
assert S.expand(sum(r*r for r in res)).coeff(v['tau'],4)==1

# Eliminate the added coordinates explicitly, leaving exactly the six core residuals.
J,F,alpha,z,f,h,i,o,s,w,tau,eta,zeta,y,gamma=[v[n] for n in names[:15]]
X=w*q; Y=s*q**3; E=X*Y; k=eta+zeta; c=k*Y+eta; a=E+Y
Delta=a*a+4*a+3; D=X+a*c+gamma*(4*a+3)
G=(q-1)*(q-F)+alpha; R=G*(q*q-1)+J*(MC+q*MF)
V=c*(o*f-1)-R*f*f; I=i*c*c; B=I*I
mapping={v[n]:val for n,val in {
 'L':q*q-1,'N':q**3,'X':X,'a':a,'E':E,'c':c,'P':E*(c-eta)+k,
 'D':D,'Delta':Delta,'C2':c*c,'G':G,'R':R,'F2':f*f,'V0':o*f-1,
 'V':V,'g':y*y-V*V,'I':I,'B':B}.items()}
active=[7,11,12,15,22,23]
expected=[tau*tau-(E*k*Y)*(E*k*Y+k)-1,D*D-Delta*c*c-1,
 k-E*h-R-1,(K+w)*(q-F-alpha)+q-F-z*(q-1)-1,
 I*I-Delta*(f*f-1),B*(V*V-y*y)+y*y-1]
for idx,r in enumerate(res):
  got=r.subs(mapping, simultaneous=True)
  want=expected[active.index(idx)] if idx in active else 0
  assert S.Poly(got-want,*[v[n] for n in names[:15]]).is_zero
payload={
 'description':'24 explicit quadratic equations in 33 positive integer unknowns; lift of the inputless ordinary-strong hybrid.',
 'source_commit':'3b201cdea32d2c816f5f3d20734051f25fd3ef14',
 'selected_coefficient_recipe':'../bridge/T4_CONSTANTS.json',
  'coefficient_contract':'Use a fully proved compatible raw-blank or input-erasing Start-only compiler, with beta=B-1, K=DC+B*DR, MC=native low mask, MF=native high mask+B-1. Authenticated raw-blank fallback is packet06. Numerical mask inequalities alone do not prove the compiler contract.',
 'variable_domain':'strictly positive integers','variables':names,'variable_count':33,'equation_count':24,
 'linear_abbreviations':{'q':'beta*J+1','k':'eta+zeta'},
 'equations':[l+' = '+r for l,r in equations],
 'residuals':list(map(str,res)),'residual_degrees':degrees,
 'single_equation':'sum(residual**2 for residual in residuals) = 0','single_equation_exact_degree':4,
 'proof':'quartic33_ordinary_proof.md',
 'claim_limits':'Equivalent to the ordinary-strong core, which has the relaxed Pell-rank lemma as a substantive dependency. Not same-tuple equivalent to normalized strong.'
}
(HERE/'quartic33_ordinary.json').write_text(json.dumps(payload,indent=2)+'\n')
receipt={'variables':33,'equations':24,'max_residual_degree':2,'exact_sos_degree':4,
 'tau_fourth_coefficient':1,'all_24_substitution_identities':'passed',
 'positive_lift':'requires derived V>1, f>1 and G>0; proved in hybrid core argument, summarized in companion proof',
 'received_source_code_executed':False}
(HERE/'quartic33_ordinary_audit.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
