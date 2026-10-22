"""Independent bounded diagnostics and exact symbolic polynomial identities.

This is newly written review code. It does not execute upstream code, enumerate
the astronomical coefficient recipe, or test any putative ZFC refutation.
The accompanying review states the mathematical argument and audit boundary.
"""
from pathlib import Path
import json
import sympy as S

ROOT = Path(__file__).resolve().parents[1]
PACKET = json.loads((ROOT/'comparison/hybrid_system61.json').read_text())
names = PACKET['witnesses']
ports = {n:S.Symbol(n) for n in names + PACKET['fixed_numerals']}
J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma = [ports[n] for n in names]
beta,K,MC,MF = [ports[n] for n in PACKET['fixed_numerals']]
q=beta*J+1; C=q-F-alpha; X=w*q; Y=s*q**3; E=X*Y
k=eta+zeta; c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H
D=X+a*c+gamma*H; G=(q-1)*(q-F)+alpha
R=G*(q*q-1)+(MC+q*MF)*J; L=E*k*Y
V=c*(T*f-1)-R*f*f; Baux=Delta*(f*f-1); I=i*c*c
factors=[tau*tau-L*(L+k), D*D-Delta*c*c,
         Baux*(V*V-y*y)+y*y, k-h*E-R,
         (K+w)*C+q-F-z*(q-1), 1+I*I-Baux]
env=dict(ports)
def at(x): return env[x] if isinstance(x,str) else S.Integer(x)
for name,op,left,right in PACKET['source']:
    left,right=at(left),at(right)
    env[name]=left+right if op=='+' else left-right if op=='-' else left*right
symbolic_checks=[]
for j,(left,right) in enumerate(PACKET['comparisons']):
    assert S.expand(at(left)-at(right)-(factors[j]-1)) == 0
    symbolic_checks.append(True)
gens=[ports[n] for n in names]
positive={'Jrep','F','alpha','transport_quotient','i','s','w','eta','zeta'}
weights=[2 if n in positive else 1 for n in names]
degrees=[]; weighted=[]; terms=[]
for factor in factors:
    poly=S.Poly(S.expand(factor), *gens)
    degrees.append(poly.total_degree())
    weighted.append(max(sum(e*w for e,w in zip(exps,weights)) for exps,coef in poly.terms()))
    terms.append(len(poly.terms()))
assert degrees==[22,18,28,7,2,22]
assert weighted==[44,35,50,13,4,44]
assert sum(degrees)==99 and sum(weighted)==190

def pell(A,n):
    x,y=1,0
    for _ in range(n):x,y=A*x+(A*A-1)*y,x+A*y
    return x,y
stepdown_cases=0
for A in range(2,9):
    for m in range(1,17):
        modulus=pell(A,m)[0]
        for n in range(6*m+1):
            cn=pell(A,n)[0]
            for kindex in range(1,m+1):
                ck=pell(A,kindex)[0]
                if (cn-ck)%modulus==0 or (cn+ck)%modulus==0:
                    assert (n-kindex)%(2*m)==0 or (n+kindex)%(2*m)==0
                stepdown_cases+=1

# A necessary warning: the isolated relaxed norm has extraneous rational
# Pell coefficients. Its large-index hypothesis cannot be omitted.
A0,p0,c0,i0,f0=7,1,1,12,2
assert pell(A0,p0)[1]==c0
assert (i0*c0*c0)**2==(A0*A0-1)*(f0*f0-1)
assert f0<A0 and not c0>A0*(A0*A0-1)**2

x,y0=S.symbols('X Y')
aa=y0*(x+1)+2; pp=2*x*y0*y0+1
ratio_margin=S.expand(x*(2*aa-1)**2-2*pp*(x+1)**2)
assert S.expand(ratio_margin-(12*x*y0*(x+1)+9*x-2*(x+1)**2))==0
u,v=S.symbols('u v')
positive_margin=S.Poly(ratio_margin.subs({x:u+1,y0:v+1}),u,v)
assert all(coef>0 for monom,coef in positive_margin.terms())

result={
 'exact_symbolic_residual_identities':symbolic_checks,
 'factor_degrees':degrees, 'factor_weighted_degrees':weighted,
 'factor_expanded_monomial_counts':terms,
 'positive_product_degree':sum(degrees),
 'signed33_product_degree':sum(weighted),
 'signed33_sos_degree':2*max(weighted),
 'signed_chi_stepdown_bounded_cases':stepdown_cases,
 'rational_Pell_counterexample_without_size_bound':{'A':7,'p':1,'c':1,'i':12,'f':2},
 'exact_ratio_margin':str(ratio_margin),
 'ratio_margin_after_X_uplus1_Y_vplus1':str(positive_margin.as_expr()),
 'scope':'Symbolic identities prove the displayed finite polynomial identities; bounded Pell diagnostics are not proofs of universal Pell statements. This script does not verify the compiler, coefficient recipe, or K215 logical endpoint.'
}
(Path(__file__).parent/'INDEPENDENT_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
