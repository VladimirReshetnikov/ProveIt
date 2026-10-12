"""Independent finite-entry replay of the order-ten eventual rank bound.

The proof of dominance is given in contribution_note.tex; this script checks
the finite polynomial constants and the terminal integer comparison. It does
not extrapolate a numerical sample to establish the infinite theorem.
"""
from pathlib import Path
from fractions import Fraction
import json
import math
import sympy as sp
from completion_certificate import contraction, falling


def main():
    a = 5
    b = sp.Symbol('b')
    variables = sp.symbols('U1:10')
    n = [b-a+i for i in range(a)]
    R = [2*b-2*a+2+2*ell for ell in range(a)]
    J = sp.prod((2*z+1)*(2*z+2) for z in n)
    E = sp.prod(R[ell]+r for i in range(a) for ell in range(a)
                for r in range(1,max(0,2*i-4*ell-1)+1))
    D = math.factorial(10)*J*E
    F,A = contraction(a,b,variables)
    degrees,norms=[],[]
    for entry in A:
        poly = sp.Poly(sp.cancel(D*entry),b,*variables,domain=sp.ZZ)
        degrees.append(max(e[0] for e,c in poly.terms()))
        norms.append(sum(abs(int(c)) for e,c in poly.terms()))
    norm = max(norms)
    assert norm==602847821074996042728613866361551228764160
    assert norm<10**42
    assert max(degrees)==46
    K = math.factorial(5)*norm**5
    assert K<10**213
    kappa = Fraction(math.factorial(5)*math.factorial(10)**5,
                     math.prod(math.factorial(2*i+2) for i in range(5)))
    points = [Fraction(1,j*j) for j in range(1,6)]
    V = math.prod((points[j]-points[i])**2
                  for i in range(5) for j in range(i+1,5))
    assert kappa==14932726824960000000 and kappa>10**19
    assert V==Fraction(2401,36864000000000000) and V>Fraction(1,10**14)
    C = Fraction(K*2**142,kappa*4**5*V*math.factorial(5)**18)
    assert C<10**251<10**256
    base = 1920
    numerator = 10**256*base**64*960**(2*base)
    denominator = math.factorial(2*base-18)
    assert numerator < denominator
    exponent = ((denominator-1)//numerator).bit_length()-1
    assert 2**exponent*numerator<denominator
    ratio = Fraction(base+1,base)**64*Fraction(960**2,(2*base-16)*(2*base-17))
    assert ratio<Fraction(3,4)
    result={
        'a':5,'b_threshold':1920,'tail_order_threshold':3840,
        'scaled_entry_degrees':degrees,'scaled_entry_norms':norms,
        'max_degree':46,'max_norm':norm,
        'kappa':str(kappa),'V':str(V),'C':str(C),
        'simple_C_upper_bound':'10^256',
        'base_comparison':f'2^{exponent} * 10^256 * 1920^64 * 960^3840 < 3822!',
        'ratio_at_base_below_three_quarters':True,
        'all_checks_exact':True,
    }
    path=Path(__file__).with_name('eventual_ten_verification.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['max_degree','max_norm','base_comparison','all_checks_exact']},indent=2))


if __name__=='__main__':
    main()
