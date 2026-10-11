"""Finite exact checks and reusable coefficient tables for the article.

These check algebra, not the analytic contour and continuation theorems.
No numerical value is used to accept a symbolic identity.
"""
from functools import lru_cache
from pathlib import Path
import json
import sympy as sp
from power_algebra import (power_data, harmonic_symbols, word_coefficients,
                           regularized, reduce_small, g, zz, v)

ROOT = Path(__file__).resolve().parents[1]
checks = []

def check(name, condition):
    if not bool(condition):
        raise AssertionError(name)
    checks.append(name)

@lru_cache(None)
def finite_word(n, word):
    if not word:
        return sp.Integer(1)
    return sum(sp.Rational(1, m**word[0])*finite_word(m-1,word[1:])
               for m in range(1,n+1))

records = []
for k in range(2,9):
    a = power_data(k)
    hs = harmonic_symbols(k)
    # Independent evaluation by actual finite nested sums tests conversion
    # of harmonic products, including multiplicities and all diagonal terms.
    constants = {g:sp.Rational(3,7), **{zz[r]:sp.Rational(r+2,r+1)
                                         for r in range(2,k+1)}}
    for n in (2,4,7):
        substitution = {v:sp.Rational(1,n),**constants,
                        **{hs[r-1]:sum(sp.Rational(1,j**r)
                           for j in range(1,n)) for r in range(1,k+1)}}
        for label, polynomial, words in (
                ('J',a['jpolynomial'],a['jwords']),
                ('D',a['delta'][1],a['derivative_words'])):
            lhs = sp.expand(polynomial).subs(substitution)
            rhs = sum(c.subs(constants)*sp.Rational(1,n**w[0])*
                      finite_word(n-1,w[1:]) for w,c in words.items())
            check(f'finite_word_{label}_k{k}_n{n}',sp.simplify(lhs-rhs)==0)
    # The coefficient difference is checked through the separate binomial
    # recurrence from psi(-n+e)=psi(1-n+e)+1/(n-e).
    for j in range(1,k+1):
        recurrence = 0
        for ell in range(1,k-j+1):
            lower = power_data(k-ell)
            for h in range(j,k-ell+1):
                recurrence += (sp.binomial(k,ell)*
                    sp.binomial(ell+h-j-1,h-j)*lower['p'][h]*v**(ell+h-j))
        check(f'difference_recurrence_k{k}_j{j}',
              sp.expand(recurrence-a['delta'][j])==0)
    records.append({
        'power':k,
        'symbols':'g=Euler gamma; zr=zeta(r); hr=H_(n-1)^(r); v=1/n',
        'principal_part_coefficients_at_n_minus_1':{
            str(j):str(a['p'][j]) for j in a['p']},
        'J_words':{','.join(map(str,w)):str(c) for w,c in a['jwords'].items()},
        'D_words':{','.join(map(str,w)):str(c) for w,c in a['derivative_words'].items()},
    })

expected_J={2:0,3:3*zz[2],4:12*zz[3]-12*g*zz[2],
            5:30*g*g*zz[2]-60*g*zz[3]+sp.Rational(35,3)*zz[4]}
for k in range(2,6):
    a=power_data(k)
    j=reduce_small(sum(c*regularized(w) for w,c in a['jwords'].items()))
    check(f'J_reduction_k{k}',sp.expand(j-expected_J[k])==0)
    # An independent finite-stuffle regularization verifies the same
    # constant that is obtained analytically from the large circle.
    c={2:-2*zz[2],3:0,4:18*zz[4],5:0}[k]
    check(f'contour_constant_stuffle_k{k}',
          sp.expand(reduce_small(a['elementary'])-j-c)==0)

d5=power_data(5)['derivative_words']
expected_D5={(1,1,1,1):-120,(1,1,1):120*g,
 (1,1):60*(zz[2]-g*g),(1,):20*(g**3-3*g*zz[2]+zz[3]),
 (1,3):20,(2,2):10,(3,1):20,(2,):10*zz[2],(3,):-20*g}
check('fifth_derivative_word_support',set(d5)==set(expected_D5))
for word,c in expected_D5.items():
    check('fifth_derivative_'+str(word),sp.expand(d5[word]-c)==0)

# The formal fifth-order direction cannot be changed by lower raw powers.
for k in range(2,5):
    a=power_data(k)
    check(f'no_mixed_weight_four_in_Q{k}',
          all(a['derivative_words'].get(w,0)==0
              for w in ((1,3),(2,2),(3,1))))

# Exact proof-level check of the audited Tornheim denominator identity.
x,y=sp.symbols('x y')
check('Tornheim_partial_fraction',
      sp.cancel(1/(x*y*(x+y))-(1/x**2)*(1/y-1/(x+y)))==0)

# Closed residue polynomial checked against the independently generated
# pole coefficients after taking their harmonic asymptotic constants.
L=sp.Symbol('L',real=True)
for k in range(1,9):
    a=power_data(k)
    hs=harmonic_symbols(k)
    substitution={hs[0]:L+g,**{hs[r-1]:zz[r] for r in range(2,k+1)}}
    asymptotic=sp.expand(a['p'][1].subs(substitution,simultaneous=True))
    asymptotic=asymptotic.subs({zz[r]:sp.zeta(r) for r in range(2,k+1)})
    closed=-((L+sp.I*sp.pi)**k-(L-sp.I*sp.pi)**k)/(2*sp.I*sp.pi)
    check(f'closed_residue_k{k}',sp.simplify(asymptotic-closed)==0)

# Verify the scalar cancellation from the generated spectral word data.
gamma1,eta,theta,chi,D13,D22,D31,zp2,zp3=sp.symbols(
    'gamma1 eta theta chi D13 D22 D31 zp2 zp3')
jets={(1,):-gamma1,(1,1):eta,(1,1,1):theta,(1,1,1,1):chi,
      (1,3):D13,(2,2):D22,(3,1):D31,(2,):zp2,(3,):zp3}
moments={}
for k in range(2,6):
    a=power_data(k)
    j=reduce_small(sum(c*regularized(w) for w,c in a['jwords'].items()))
    contour={2:-2*zz[2],3:0,4:18*zz[4],5:0}[k]
    moments[k]=contour+j+sum(c*jets[w] for w,c in a['derivative_words'].items())
canonical=(moments[5]+5*g*moments[4]+
           10*(g*g+zz[2])*moments[3]+
           10*(g**3+3*g*zz[2]+zz[3])*moments[2])
expected=(-120*chi+10*(2*D13+D22+2*D31)+10*zz[2]*zp2+
          sp.Rational(260,3)*zz[4]-60*g*zz[4]-
          20*g**3*zz[2]-20*zz[2]*zz[3])
check('canonical_fifth_full_formula',
      sp.expand(reduce_small(canonical-expected))==0)

result={'status':'pass','exact_assertions':len(checks),'checks':checks,
        'scope':'finite algebra only; analytic proofs are in the article',
        'sympy_version':sp.__version__}
(ROOT/'data'/'power_coefficients.json').write_text(json.dumps(records,indent=2)+'\n')
(ROOT/'data'/'exact_checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='checks'},indent=2))
