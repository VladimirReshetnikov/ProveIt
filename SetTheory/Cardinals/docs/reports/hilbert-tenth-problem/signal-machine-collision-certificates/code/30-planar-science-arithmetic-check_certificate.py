#!/usr/bin/env python3
"""Fresh exact arithmetic checks for PROOF.md; no external/upstream imports."""
from fractions import Fraction as Q
from math import gcd, lcm
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def coefficients(p, q, n):
    c, d = 1, 0
    for _ in range(n):
        c, d = -q*q*d, c+p*d
    return c, d


def companion_step(p, q, xy):
    x, y = xy
    return -y, x+Q(p, q)*y


def primitive(xy):
    b = lcm(xy[0].denominator, xy[1].denominator)
    u, v = int(xy[0]*b), int(xy[1]*b)
    assert gcd(gcd(u, v), b) == 1
    return u, v, b


def decompose(b, q):
    m = 0
    while b % q == 0:
        b //= q
        m += 1
    return m, b


def outer_match(p, q, xy):
    u, v, b = primitive(xy)
    m, r = decompose(b, q)
    c, d = coefficients(p, q, m+1)
    zero = (u-b)**2+v*v
    positive = (r-1)**2+(q*u-c)**2+(v-d)**2
    return zero == 0 or positive == 0


def matmul(a, b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2))
                       for j in range(2)) for i in range(2))


def matvec(a, x):
    return tuple(sum(a[i][j]*x[j] for j in range(2)) for i in range(2))


def inverse(a):
    d = a[0][0]*a[1][1]-a[0][1]*a[1][0]
    assert d
    return ((a[1][1]/d, -a[0][1]/d), (-a[1][0]/d, a[0][0]/d))


def arithmetic_checks():
    counts = dict(trace_pairs=0, power_cases=0, factor_cases=0,
                  conjugacy_cases=0, grid_nonmatches=0,
                  extraction_search_cases=0, strict_gate_cases=0)
    q_examples = set()
    for q in range(2, 33):
        for p in range(-2*q+1, 2*q):
            if gcd(p, q) != 1:
                continue
            counts['trace_pairs'] += 1
            q_examples.add(q)
            xy = (Q(1), Q(0))
            orbit = set()
            for n in range(25):
                orbit.add(xy)
                u, v, b = primitive(xy)
                expected_b = 1 if n == 0 else q**(n-1)
                assert b == expected_b
                assert outer_match(p, q, xy)
                if n:
                    c, d = coefficients(p, q, n)
                    assert c % q == 0
                    assert xy == (Q(c//q, b), Q(d, b))
                    assert gcd(d, q) == 1
                    P = q**(n-1)
                    H = 2*q*q*P
                    R = 4*H+abs(p)+1
                    modulus = R*R-p*R+q*q
                    assert abs(c) <= H and abs(d) <= H
                    assert R >= 2 and 2*H < R
                    assert modulus > 2*H*(1+R)
                    assert (pow(R, n, modulus)-c-R*d) % modulus == 0
                counts['power_cases'] += 1
                xy = companion_step(p, q, xy)
            for b in range(1, 257):
                m, r = decompose(b, q)
                k, s = divmod(r, q)
                assert b == q**m*r and 0 < s < q
                assert k >= 0 and q-s > 0
                counts['factor_cases'] += 1
            # Exact finite independent search: for this grid any possible hit
            # has denominator <=6, so the denominator theorem limits n<=3.
            for x, y in [(Q(0), Q(0)), (Q(-1), Q(0)),
                         (Q(1, 2), Q(1, 3)), (Q(2), Q(3)),
                         (Q(1), Q(1)), (Q(0), Q(-1))]:
                assert outer_match(p, q, (x, y)) == ((x, y) in orbit)
                counts['grid_nonmatches'] += 1
    # Check both strict-acceptance gates on and off the invariant ellipse.
    for p, q in [(1, 2), (-3, 2), (5, 6), (-11, 12), (31, 16)]:
        trace = Q(p, q)
        forward = (Q(1), Q(0))
        for n in range(1, 21):
            forward = (trace*forward[0]+forward[1], -forward[0])
            assert not outer_match(p, q, forward)
            for scale in [Q(1, 2), Q(1), Q(2)]:
                point = tuple(scale*c for c in forward)
                u, v, b = primitive(point)
                deficit = 2*q*b*b-2*q*u*u-2*p*u*v-2*q*v*v
                if scale < 1:
                    assert deficit > 0
                elif scale == 1:
                    assert deficit == 0
                else:
                    assert deficit < 0
                if deficit >= 0:
                    m, r = decompose(b, q)
                    c, d = coefficients(p, q, m+1)
                    gate0 = deficit**2+(u-b)**2+v*v
                    gate1 = deficit**2+(r-1)**2+(q*u-c)**2+(v-d)**2
                    assert gate0 > 0 and gate1 > 0
                counts['strict_gate_cases'] += 1
        for slope in [Q(0), Q(1), Q(-1), Q(2), Q(1, 2)]:
            step = -(2+trace*slope)/(1+trace*slope+slope*slope)
            point = (1+step, slope*step)
            u, v, b = primitive(point)
            assert 2*q*b*b-2*q*u*u-2*p*u*v-2*q*v*v == 0
            # Any possible backward hit has exponent at most 1+bit_length(b).
            xi = (Q(1), Q(0))
            hits = set()
            for _ in range(b.bit_length()+2):
                hits.add(xi)
                xi = companion_step(p, q, xi)
            assert outer_match(p, q, point) == (point in hits)
            counts['strict_gate_cases'] += 1
    # Rational similarities exercise contacts not equal to a coordinate axis.
    for p, q in [(1, 2), (-3, 2), (5, 6), (-11, 12), (31, 16)]:
        companion = ((Q(0), Q(-1)), (Q(1), Q(p, q)))
        for s in [((Q(2), Q(1)), (Q(1), Q(1))),
                  ((Q(1, 3), Q(-2, 5)), (Q(3, 7), Q(4))),
                  ((Q(-1), Q(0)), (Q(2, 9), Q(3, 2)))]:
            si = inverse(s)
            bmat = matmul(matmul(s, companion), si)
            contact = matvec(s, (Q(1), Q(0)))
            assert matvec(bmat, contact) == matvec(s, (Q(0), Q(1)))
            x = contact
            xi = (Q(1), Q(0))
            for n in range(17):
                assert matvec(si, x) == xi
                assert outer_match(p, q, matvec(si, x))
                counts['conjugacy_cases'] += 1
                x = matvec(bmat, x)
                xi = companion_step(p, q, xi)
    # Search every bounded C and solve the congruence for D by a small
    # exhaustive loop, only at small exponents so this is genuinely finite.
    for p, q, m in [(1, 2, 0), (-1, 2, 1), (1, 3, 0), (-5, 3, 0)]:
        P = q**m
        H = 2*q*q*P
        R = 4*H+abs(p)+1
        modulus = R*R-p*R+q*q
        residue = pow(R, m+1, modulus)
        found = [(c, d) for c in range(-H, H+1)
                 for d in range(-H, H+1)
                 if (residue-c-R*d) % modulus == 0]
        assert found == [coefficients(p, q, m+1)]
        counts['extraction_search_cases'] += 1
    counts['q_examples'] = sorted(q_examples)
    return counts


class Poly:
    """Small integer sparse polynomial, monomials as sorted variable tuples."""
    def __init__(self, value=0):
        if isinstance(value, Poly):
            self.terms = dict(value.terms)
        elif isinstance(value, dict):
            self.terms = {k:v for k,v in value.items() if v}
        else:
            self.terms = {():int(value)} if value else {}
    @classmethod
    def variable(cls, name):
        return cls({(name,):1})
    def __add__(self, other):
        terms = dict(self.terms)
        for key, value in Poly(other).terms.items():
            terms[key] = terms.get(key, 0)+value
        return Poly(terms)
    __radd__ = __add__
    def __neg__(self):
        return Poly({key:-value for key,value in self.terms.items()})
    def __sub__(self, other):
        return self+-Poly(other)
    def __rsub__(self, other):
        return Poly(other)+-self
    def __mul__(self, other):
        terms = {}
        for ka, va in self.terms.items():
            for kb, vb in Poly(other).terms.items():
                key = tuple(sorted(ka+kb))
                terms[key] = terms.get(key, 0)+va*vb
        return Poly(terms)
    __rmul__ = __mul__
    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        out = Poly(1)
        for _ in range(exponent):
            out = out*self
        return out
    def degree(self):
        return max(map(len, self.terms), default=-1)


class Schema:
    def __init__(self):
        self.inputs, self.witnesses, self.residuals = [], [], []
    def pos(self, name):
        assert name not in self.inputs+self.witnesses
        self.witnesses.append(name)
        return Poly.variable(name)
    def inp(self, name):
        assert name not in self.inputs+self.witnesses
        self.inputs.append(name)
        return Poly.variable(name)
    def nat(self, name):
        return self.pos(name+'_plus')-1
    def signed(self, name):
        return self.pos(name+'_positive')-self.pos(name+'_negative')
    def equation(self, name, residual):
        self.residuals.append((name, Poly(residual)))
    def power(self, prefix, base, exponent):
        names = 'out w M g x y u v s t qb qv J'.split()
        out,w,M,g,x,y,u,v,s,t,qb,qv,J = [self.pos(prefix+n) for n in names]
        alpha, beta = self.pos(prefix+'alpha_plus')+1, self.pos(prefix+'beta_plus')+1
        names = 'dwb dwk dyk a1 a2 s1 s2 t1 t2 r1 r2'.split()
        dwb,dwk,dyk,a1,a2,s1,s2,t1,t2,r1,r2 = [self.nat(prefix+n) for n in names]
        k0, m0 = exponent+1, base*out
        residuals = [
            x*x-1-(alpha*alpha-1)*y*y,
            u*u-1-(alpha*alpha-1)*v*v,
            s*s-1-(beta*beta-1)*t*t,
            beta-1-4*y*qb,
            beta+u*a1-alpha-u*a2,
            v-y*y*qv,
            s+u*s1-x-u*s2,
            t+4*y*t1-k0-4*y*t2,
            y-k0-dyk,
            w-base-dwb,
            w-k0-dwk,
            M-m0-J,
            alpha*alpha-1-((w+1)**2-1)*(w*g)**2,
            2*alpha*base-M-(base*base+1),
            x+M*r1-y*(alpha-base)-m0-M*r2,
        ]
        for index, residual in enumerate(residuals, 1):
            self.equation(prefix+str(index), residual)
        return out


def symbolic_checks():
    schema = Schema()
    p, q = -5, 6
    a1,a2,a3,a4,N = [schema.inp('input_'+str(i)) for i in range(1, 6)]
    X,Y = a1-a2,a3-a4
    d = schema.nat('radius')
    delta = 2*q*N*N-2*q*X*X-2*p*X*Y-2*q*Y*Y
    schema.equation('radius', delta-d)
    m,k,LC,HC,LD,HD = [schema.nat('contact_'+n) for n in 'm k LC HC LD HD'.split()]
    h,b,r,s,t,J0,J1 = [schema.pos('contact_'+n) for n in 'h b r s t J0 J1'.split()]
    u,v,e1,e2,e3,C,D,kappa = [schema.signed('contact_'+n) for n in 'u v e1 e2 e3 C D kappa'.split()]
    P = schema.power('power1_', Poly(q), m)
    H = 2*q*q*P
    R = 4*H+abs(p)+1
    T = schema.power('power2_', R, m+1)
    outer = [X-h*u, Y-h*v, N-h*b, e1*u+e2*v+e3*b-1,
             b-P*r, r-q*k-s, s+t-q,
             C+H-LC, H-C-HC, D+H-LD, H-D-HD,
             T-C-R*D-kappa*(R*R-p*R+q*q),
             d*d+(u-b)**2+v*v-J0,
             d*d+(r-1)**2+(q*u-C)**2+(v-D)**2-J1]
    for index, residual in enumerate(outer, 1):
        schema.equation('outer_'+str(index), residual)
    F = sum((residual*residual for _,residual in schema.residuals), Poly(0))
    assert len(schema.inputs) == 5
    assert len(schema.witnesses) == 82
    assert len(schema.residuals) == 45
    assert max(residual.degree() for name,residual in schema.residuals if name.startswith('outer')) == 3
    assert max(residual.degree() for name,residual in schema.residuals) == 6
    assert F.degree() == 12
    top_coefs = {}
    for prefix in ['power1_', 'power2_']:
        monomial = tuple(sorted([prefix+'w']*8+[prefix+'g']*4))
        top_coefs[prefix] = F.terms.get(monomial, 0)
        assert top_coefs[prefix] == 1
    result = {
        'trace': f'{p}/{q}', 'positive_inputs': len(schema.inputs),
        'positive_witnesses': len(schema.witnesses),
        'residual_equations': len(schema.residuals),
        'outer_max_degree': 3, 'residual_max_degree': 6,
        'sum_of_squares_degree': F.degree(),
        'expanded_sum_of_squares_terms': len(F.terms),
        'power_w8g4_coefficients': top_coefs,
        'witness_names': schema.witnesses,
        'equation_degrees': {name:res.degree() for name,res in schema.residuals},
    }
    return result


def main():
    result = {
        'scope': 'Fresh finite exact arithmetic and full positive-adapted schema checks; no upstream code executed; no general Pell witness construction.',
        'arithmetic': arithmetic_checks(),
        'symbolic': symbolic_checks(),
        'all_assertions_passed': True,
    }
    (ROOT/'CHECKS.json').write_text(json.dumps(result, indent=2)+'\n')
    pins = {}
    for path in [ROOT/'PROOF.md', ROOT/'check_certificate.py',
                 Path('/workspace/shared/five-signal-rotation-family59-20261004/PROOF.md'),
                 Path('/workspace/shared/five-signal-rotation-family59-20261004/inert_sources/pell-source.lean')]:
        pins[str(path)] = hashlib.sha256(path.read_bytes()).hexdigest()
    (ROOT/'SOURCE_PINS.json').write_text(json.dumps(pins, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'symbolic'}, indent=2))
    print(json.dumps({k:v for k,v in result['symbolic'].items()
                      if k not in ('witness_names','equation_degrees')}, indent=2))


if __name__ == '__main__':
    main()
