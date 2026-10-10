#!/usr/bin/env python3
"""Reusable exact coefficients for the accompanying ProveIt article.

Requires SymPy.  No floating point, numerical recognition, or PSLQ is used.
The finite CLI checks are implementation diagnostics, not mathematical proofs.

Public conventions:
* gamma_coefficients(a, K) returns (C_0(a), ..., C_K(a)), where
  sum C_k(a)y**k = Gamma(a)Gamma(1-y)/Gamma(a-y).
* harmonic_sum_from_partial_fractions uses elementary E_{n,r}, NOT r!E_{n,r},
  and sums from n=0.  A term (c,a,p) denotes c/(n+a)**p.
* contact_polynomial(n,k,L) uses the article's fixed local cutoff coordinate.
* base_closure(m,n) uses z=1-s,w=1-t and formal gamma_j(c), gamma_j(1-c).
* choi_mixed(r,t) uses Choi's E_r(n)=r!E_{n,r}, sums from n=1 by default,
  and has an explicit include_n0 option.

Base and Choi outputs retain formal zeta_k atoms.  They denote zeta(k),
not algebraically independent numbers; exact even-zeta relations may be
substituted afterward.  For example, expr.subs(zeta_symbol(2), pi**2/6).
Unspecified symbolic shifts in rational kernels carry the condition Re(a)>0.

Run: python exact_coefficients.py --output-dir ../data
"""

from __future__ import annotations

import argparse
import json
from functools import lru_cache
from pathlib import Path

import sympy as sp


def _index(value, name):
    if isinstance(value, bool) or not isinstance(value, (int, sp.Integer)):
        raise TypeError(f'{name} must be an exact nonnegative integer')
    value = int(value)
    if value < 0:
        raise ValueError(f'{name} must be nonnegative')
    return value


def _exact(value):
    value = sp.sympify(value)
    if not isinstance(value, sp.Expr):
        raise TypeError('An exact scalar expression is required')
    if value.has(sp.Float):
        raise TypeError('Floating-point inputs are forbidden; use Rational or exact expressions')
    return value


def zeta_symbol(k):
    """The formal atom zeta_k, denoting the actual positive-integer zeta value."""
    k = _index(k, 'zeta index')
    if k < 2:
        raise ValueError('Only integer zeta values with index >= 2 are used')
    return sp.Symbol(f'zeta_{k}')


c = sp.Symbol('c', real=True)
_z, _w = sp.symbols('_z _w')
_a = sp.Dummy('a', positive=True)


def stieltjes_symbol(j, argument=c):
    """Formal generalized Stieltjes atom gamma_j(argument)."""
    return sp.Function(f'gamma_{_index(j, "Stieltjes index")}')(_exact(argument))


def gamma_coefficients(a, max_depth):
    """Return C_0,...,C_K by k C_k = sum_{j=1}^k A_j C_{k-j}.

    A_1=EulerGamma+psi(a), A_j=zeta(j)-zeta(j,a) for j>=2.
    The result is expressed in polygammas and exact ordinary zeta values.
    Nonpositive integer a is rejected; elsewhere the formula is meromorphic.
    """
    a, max_depth = _exact(a), _index(max_depth, 'max_depth')
    if a.is_integer is True and a.is_nonpositive is True:
        raise ValueError('a must not be a nonpositive integer')
    return _gamma_coefficients(a, max_depth)


@lru_cache(maxsize=None)
def _gamma_coefficients(a, max_depth):
    atoms = [sp.S.Zero, sp.EulerGamma + sp.polygamma(0, a)]
    atoms.extend(sp.zeta(j) - (-1)**j * sp.polygamma(j-1, a) / sp.factorial(j-1)
                 for j in range(2, max_depth+1))
    coeffs = [sp.S.One]
    for k in range(1, max_depth+1):
        coeffs.append(sp.expand(sum(atoms[j]*coeffs[k-j] for j in range(1,k+1))/k))
    return tuple(coeffs)


def harmonic_sum_from_partial_fractions(depth, terms):
    """Reduce sum_{n>=0} E_{n,depth} sum_(d,a,p) d/(n+a)^p exactly.

    terms is an iterable of (coefficient, shift, positive_integer_power).
    The sum of all coefficients at power one MUST simplify identically to
    zero.  This enforces the O(n^-2) hypothesis, not a regularization.
    Known shifts with Re(a)<=0 are rejected.  Unspecified symbolic shifts
    are accepted subject to the theorem's condition Re(a)>0.
    """
    depth = _index(depth, 'depth')
    parsed = []
    for term in terms:
        if not isinstance(term, (tuple, list)) or len(term) != 3:
            raise TypeError('Each partial-fraction term must be a triple (coefficient, shift, power)')
        coef, shift, power = _exact(term[0]), _exact(term[1]), _index(term[2], 'power')
        if power == 0:
            raise ValueError('Partial-fraction powers must be positive')
        if coef == 0:
            continue
        if sp.re(shift).is_positive is False:
            raise ValueError(f'The harmonic theorem requires Re(shift)>0; got {shift}')
        parsed.append((coef, shift, power))
    residue = sp.simplify(sum(coef for coef, _, p in parsed if p == 1))
    if residue != 0:
        raise ValueError(f'Total simple-pole residue must be identically zero; got {residue}')
    C = gamma_coefficients(_a, depth+1)[depth+1]
    result = sp.S.Zero
    for coef, shift, power in parsed:
        if power == 1:
            result -= coef*C.subs(_a, shift)
        else:
            result += ((-1)**power*coef/sp.factorial(power-1)
                       * sp.diff(C, _a, power-1).subs(_a, shift))
    return sp.simplify(sp.expand(result))


def contact_polynomial(n, k, L):
    """Return n![z^(n+1)] exp(Lz) product_{j=1}^k(1-z/j)."""
    n, k, L = _index(n, 'n'), _index(k, 'k'), _exact(L)
    # Truncated multiplication retains only coefficients needed by the answer.
    e = [sp.S.One] + [sp.S.Zero]*(n+1)
    for j in range(1, k+1):
        for degree in range(min(j,n+1), 0, -1):
            e[degree] -= e[degree-1]/j
    return sp.expand(sp.factorial(n)*sum(
        e[j]*L**(n+1-j)/sp.factorial(n+1-j)
        for j in range(min(k,n+1)+1)))


def _homogeneous_exp(log_parts):
    """Exact homogeneous recurrence for exp(sum_{j>=1} log_parts[j])."""
    out = [sp.S.One]
    for degree in range(1, len(log_parts)):
        out.append(sp.expand(sum(j*log_parts[j]*out[degree-j]
                                 for j in range(1,degree+1))/degree))
    return tuple(out)


@lru_cache(maxsize=None)
def _base_V(max_degree):
    # U=Gamma(1+z)Gamma(1-z-w)/Gamma(1-w); V=(U-1)/(z(z+w)).
    log_parts = [sp.S.Zero, sp.S.Zero]
    log_parts.extend(zeta_symbol(j)/j*((-1)**j*_z**j+(_z+_w)**j-_w**j)
                     for j in range(2,max_degree+3))
    U = _homogeneous_exp(log_parts)
    divisor = sp.Poly(_z*(_z+_w), _z, _w, domain='EX')
    out = []
    for degree in range(max_degree+1):
        quotient, remainder = sp.div(sp.Poly(U[degree+2],_z,_w,domain='EX'), divisor)
        if not remainder.is_zero:
            raise ArithmeticError('The removable Gamma quotient failed exact polynomial divisibility')
        out.append(sp.expand(quotient.as_expr()))
    return tuple(out)


def _coeff(expr, m, n):
    return sp.Poly(sp.expand(expr), _z, _w, domain='EX').coeff_monomial(_z**m*_w**n)


def base_closure(m, n):
    """Exact J_mn(c) in formal gamma_j(c), gamma_j(1-c), and zeta_k.

    The actual finite-part identity is for 0<c<1.  This uses the
    holomorphic J generator of the article with z=1-s,w=1-t.
    Only U degrees <= m+n+2 are generated, and the apparent division by
    z(z+w) is performed as exact polynomial division with zero remainder.
    """
    m, n = _index(m, 'm'), _index(n, 'n')
    M, factor = m+n, sp.factorial(m)*sp.factorial(n)
    V = _base_V(M)
    swap = lambda expr: expr.xreplace({_z:_w, _w:_z})
    result = (stieltjes_symbol(M+1,c)/(m+1)
              + stieltjes_symbol(M+1,1-c)/(n+1)
              - factor*_coeff(V[M]+swap(V[M]),m,n))
    for j in range(M):
        piece = (_z+_w)**(j+1)*V[M-1-j]
        result += factor/sp.factorial(j)*(
            stieltjes_symbol(j,c)*_coeff(piece,m,n)
            + stieltjes_symbol(j,1-c)*_coeff(swap(piece),m,n))
    return sp.expand(result)


def choi_mixed(r, t, *, include_n0=False):
    """Sum E_r(n)E_t(n)/((n+1)(n+2)), n>=1 unless include_n0=True.

    E_r(n)=r![u^r] product_{j=1}^n(1+u/j).  The Gamma quotient is
    Gamma(1-u-v)/(Gamma(2-u)Gamma(2-v)); multiply its coefficient by r!t!.
    At r=t=0 the return value is 1/2 by default, or 1 with include_n0=True.
    """
    r, t = _index(r, 'r'), _index(t, 't')
    if not isinstance(include_n0, bool):
        raise TypeError('include_n0 must be a bool')
    parts = [sp.S.Zero]
    for j in range(1, r+t+1):
        part = (_z**j+_w**j)/j
        if j >= 2:
            part += zeta_symbol(j)/j*((_z+_w)**j-_z**j-_w**j)
        parts.append(sp.expand(part))
    value = sp.factorial(r)*sp.factorial(t)*_coeff(_homogeneous_exp(parts)[r+t],r,t)
    if r == t == 0 and not include_n0:
        value -= sp.Rational(1,2)
    return sp.expand(value)


def six_cone_zero_sum():
    """Unreduced rational S(0,0,0), for three nonzero distinct phase atoms."""
    phases = sp.symbols('x_1 x_2 x_3', nonzero=True)
    li0 = lambda x: x/(1-x)
    value = sp.S.Zero
    for k in range(3):
        i,j = [index for index in range(3) if index != k]
        X,Y = phases[i]/phases[k],phases[j]/phases[k]
        value += li0(X)*li0(Y)+li0(1/X)*li0(1/Y)
    return value


def diagnostic_checks():
    """Finite exact samples.  Proofs and analytic hypotheses are in the article."""
    checks = []
    def equal(name, actual, expected):
        residual = sp.simplify(sp.expand(actual-expected))
        checks.append({'name': name, 'passed': residual == 0, 'exact_residual': str(residual)})
        if residual != 0:
            raise AssertionError(f'{name}: {residual}')
    for k in range(7):
        equal(f'C_{k}(1)',gamma_coefficients(1,6)[k],sp.S.One if k==0 else sp.S.Zero)
        equal(f'C_{k}(2)',gamma_coefficients(2,6)[k],sp.S.One)
        equal(f'C_{k}(3)',gamma_coefficients(3,6)[k],2-sp.Rational(1,2)**k)
    L = sp.Symbol('L')
    for k in range(5):
        H,H2 = sp.harmonic(k),sp.harmonic(k,2)
        equal(f'b_0,{k}',contact_polynomial(0,k,L),L-H)
        equal(f'b_1,{k}',contact_polynomial(1,k,L),L**2/2-H*L+(H**2-H2)/2)
    for r in range(5):
        equal(f'harmonic telescope depth {r}',harmonic_sum_from_partial_fractions(r,[(1,1,1),(-1,2,1)]),sp.S.One)
        equal(f'harmonic height-one depth {r}',harmonic_sum_from_partial_fractions(r,[(1,1,2)]),sp.zeta(r+2))
        equal(f'contact unscaled k=0, n={r}',contact_polynomial(r,0,L),L**(r+1)/(r+1))
    a = lambda j: stieltjes_symbol(j,c)
    b = lambda j: stieltjes_symbol(j,1-c)
    Z2,Z3,Z4 = [zeta_symbol(j) for j in (2,3,4)]
    equal('J00',base_closure(0,0),a(1)+b(1)-2*Z2)
    equal('J01',base_closure(0,1),a(2)+b(2)/2+Z2*(a(0)+b(0))-Z3)
    equal('J11',base_closure(1,1),(a(3)+b(3))/2+2*Z2*(a(1)+b(1))+Z3*(a(0)+b(0))-Z2**2-Z4)
    for m in range(3):
        for n in range(3):
            expr,M = base_closure(m,n),m+n
            exchange = {atom:replacement for j in range(M+2) for atom,replacement in ((a(j),b(j)),(b(j),a(j)))}
            equal(f'J symmetry {m},{n}',expr.xreplace(exchange),base_closure(n,m))
            equal(f'J top c {m},{n}',expr.coeff(a(M+1)),sp.Rational(1,m+1))
            equal(f'J top 1-c {m},{n}',expr.coeff(b(M+1)),sp.Rational(1,n+1))
            equal(f'J missing order c {m},{n}',expr.coeff(a(M)),sp.S.Zero)
            equal(f'J missing order 1-c {m},{n}',expr.coeff(b(M)),sp.S.Zero)
    equal('six-cone rational identity S(0)=2',sp.cancel(six_cone_zero_sum()),sp.Integer(2))
    equal('Choi zero indices n>=1',choi_mixed(0,0),sp.Rational(1,2))
    equal('Choi zero indices n>=0',choi_mixed(0,0,include_n0=True),sp.S.One)
    equal('Choi both depths two',choi_mixed(2,2),2*Z2**2+4*Z2+8*Z3+6*Z4+4)
    for r in range(6):
        equal(f'Choi H_n E_{r}',choi_mixed(r,1),sp.factorial(r)*(1+sum(zeta_symbol(j) for j in range(2,r+2))))
        if r:
            equal(f'Choi pure E_{r}',choi_mixed(r,0),sp.factorial(r))
    for r in range(4):
        for t in range(4):
            equal(f'Choi symmetry {r},{t}',choi_mixed(r,t),choi_mixed(t,r))
    for name,call,exception in [
        ('reject nonzero simple residue',lambda:harmonic_sum_from_partial_fractions(1,[(1,1,1)]),ValueError),
        ('reject zero shift',lambda:harmonic_sum_from_partial_fractions(1,[(1,0,2)]),ValueError),
        ('reject floating input',lambda:contact_polynomial(0,0,0.1),TypeError),
    ]:
        try:
            call()
        except exception:
            checks.append({'name':name,'passed':True,'expected_exception':exception.__name__})
        else:
            raise AssertionError(name)
    return checks


def sample_tables():
    a,L = sp.symbols('a L', positive=True)
    rows = []
    for k,value in enumerate(gamma_coefficients(a,4)):
        rows.append((f'C_{k}(a)',f'C_{{{k}}}(a)',value))
    for n in range(3):
        for k in range(4):
            rows.append((f'b_{{{n},{k}}}(L)',f'b_{{{n},{k}}}(L)',contact_polynomial(n,k,L)))
    for m,n in [(0,0),(0,1),(1,1),(2,0),(2,1)]:
        rows.append((f'J_{{{m},{n}}}(c)',f'J_{{{m},{n}}}(c)',base_closure(m,n)))
    for r,t in [(0,0),(1,0),(1,1),(2,1),(2,2),(3,2)]:
        rows.append((f'Choi M_{{{r},{t}}} (n>=1)',f'M_{{{r},{t}}}',choi_mixed(r,t)))
    for r in range(4):
        value = harmonic_sum_from_partial_fractions(r,[(1,a,2)])
        rows.append((f'Z_{r}(2,a)',f'Z_{{{r}}}(2,a)',value))
    rows.append(('six-cone S(0)','S(0,0,0)',sp.cancel(six_cone_zero_sum())))
    return rows


def _latex_equation(label, expr, width=135):
    """Break only at top-level additions, so generated input remains readable."""
    # Short presentation notation only; the API and JSON retain true polygammas.
    expr = expr.xreplace({atom:sp.Function(f'psi_{atom.args[0]}')(atom.args[1])
                          for atom in expr.atoms(sp.polygamma)})
    lines,current = [],''
    for index,term in enumerate(expr.as_ordered_terms()):
        negative = term.could_extract_minus_sign()
        atom = sp.latex(-term if negative else term)
        sign = '- ' if negative else ('' if index == 0 else '+ ')
        piece = sign+atom
        if current and len(current)+len(piece)>width:
            lines.append(current)
            current = piece
        else:
            current += (' ' if current else '')+piece
    lines.append(current)
    body = label+' &={} '+lines[0]
    for line in lines[1:]:
        body += '\\\\\n&{} '+line
    return '\\[\n\\begin{aligned}\n'+body+'\n\\end{aligned}\n\\]'


def main():
    parser = argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    checks,rows = diagnostic_checks(),sample_tables()
    args.output_dir.mkdir(parents=True,exist_ok=True)
    report = {'scope':'Finite exact implementation diagnostics, not proofs of the all-order theorems.',
              'sympy_version':sp.__version__,'arithmetic':'Exact symbolic and rational arithmetic; no numerical recognition.',
              'conventions':{'zeta_k':'Formal atom denoting zeta(k); no independence assertion.',
                             'J':'z=1-s,w=1-t; gamma_j(c) and gamma_j(1-c) are formal Stieltjes atoms.',
                             'harmonic':'Elementary E_{n,r}; summation starts at n=0.',
                             'Choi':'E_r(n)=r!E_{n,r}; table summation starts at n=1.'},
              'checks':checks,'all_passed':all(row['passed'] for row in checks),
              'six_cone_identity':{'assumptions':'x_1,x_2,x_3 are nonzero and pairwise distinct.',
                                   'rational_expression':str(six_cone_zero_sum()),
                                   'exact_reduced_value':str(sp.cancel(six_cone_zero_sum()))},
              'samples':[{'label':label,'expression':str(expr),'latex':sp.latex(expr)} for label,_,expr in rows]}
    (args.output_dir/'exact_coefficients_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    header = ('EXACT COEFFICIENT SAMPLES\nFinite diagnostics are not proofs.\n'
              'zeta_k denotes zeta(k); gamma_j(c) denotes a generalized Stieltjes constant.\n'
              'Choi M sums from n=1 with E_r=r! times the elementary harmonic coefficient.\n\n')
    (args.output_dir/'exact_coefficients_tables.txt').write_text(header+'\n\n'.join(f'{label} = {expr}' for label,_,expr in rows)+'\n')
    tex = ['% Generated by exact_coefficients.py; requires amsmath. This is an input fragment.',
           r'\section*{Exact coefficient samples}',
           r'Finite implementation checks are diagnostics, not proofs of the all-order identities.',
           r'Here $\zeta_k=\zeta(k)$; the $\gamma_j$ are generalized Stieltjes constants.',
           r'For compactness, $\psi_j(a)=\psi^{(j)}(a)$, including $\psi_0(a)=\psi(a)$.',
           r'The Choi sums $M_{r,t}$ start at $n=1$ and use $E_r(n)=r!E_{n,r}$.']
    for _,label,expr in rows:
        tex.append(_latex_equation(label,expr))
    (args.output_dir/'exact_coefficients_tables.tex').write_text('\n'.join(tex)+'\n')
    print(f'PASS: {len(checks)} exact diagnostic checks; wrote JSON, TeX, and plaintext tables to {args.output_dir}')


if __name__ == '__main__':
    main()
