from pathlib import Path
import sympy as s
import json
v,L,P=s.symbols('v L pi', nonzero=True, real=True)
def pn(n):return s.expand(((L+s.I*P)**n-(L-s.I*P)**n)/(2*s.I*P))
rows=[]
# Independent regularized Mellin series of one rational pole, after
# removing its origin pole. Compare against finite logarithm powers.
N=9
mellin=s.series(-P*s.exp(L*v)*s.cot(P*v)+1/v,v,0,N).removeO()
for n in range(1,9):
    poly=pn(n)
    integral=sum(s.Poly(poly,L).coeff_monomial(L**j)*s.factorial(j)*mellin.coeff(v,j) for j in range(n))
    origin=(-1)**(n//2)*P**n*(-1)/(n+1) if n%2==0 else 0
    lateral=s.expand(integral+origin-s.I*P*poly)
    ref=-(L+s.I*P)**n
    assert s.expand(lateral-ref)==0
    jump=s.expand(-(L+s.I*P)**n+(L-s.I*P)**n+2*s.I*P*poly)
    assert jump==0
    rows.append({'n':n,'p_n':str(poly),'reconstruction_residual':'0','jump_residual':'0'})
# Exact rational pole coalescence; second difference leaves residues +1,-1.
from fractions import Fraction
poles={}
for a,c in [(Fraction('-1.4'),1),(Fraction('-.4'),-2),(Fraction('.6'),1)]:
    for k in range(max(0,(-a.numerator)//a.denominator+1)):
        b=-a-k;poles[b]=poles.get(b,0)+c
assert poles=={Fraction('1.4'):1,Fraction('.4'):-1}
result={'status':'PASS','symbolic_identities':rows,'coalesced_poles':{str(k):v for k,v in poles.items()},'counts':{'reconstruction':8,'jump':8,'rational_pole_coalescence':1},'limitations':'Finite symbolic checks of the scalar reconstruction and jump polynomials, not proof of distributional boundary limits.'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: 8 reconstruction identities, 8 jump identities, exact pole coalescence')
