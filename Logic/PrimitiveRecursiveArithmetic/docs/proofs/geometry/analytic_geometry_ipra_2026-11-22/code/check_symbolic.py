#!/usr/bin/env python3
"""Independent symbolic checks of the packet's polynomial mathematics.

The restricted reader below consumes only the arithmetic statement bodies of
ObjectCertificates.lean. SymPy expands their scalar polynomial differences.
It neither executes the generator nor uses Lean's ipra_ring reflection code.
It is NOT a Lean parser, typechecker, kernel, or validation of proof terms.
Additional handwritten checks use vector/matrix formulas and polynomial
constraints to audit formulas from the human-readable chapters.
"""
from pathlib import Path
import hashlib
import json
import re
import sympy as sp

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'lean' / 'ObjectCertificates.lean'


def norm2(*xs):
    return sum(x*x for x in xs)


HELPERS = {
    'N2': (2, lambda x, y: norm2(x, y)),
    'D2': (4, lambda x, y, u, v: x*u+y*v),
    'W2': (4, lambda x, y, u, v: x*v-y*u),
    'N3': (3, lambda x, y, z: norm2(x, y, z)),
    'D3': (6, lambda x, y, z, u, v, w: x*u+y*v+z*w),
    'Q2': (5, lambda a, b, c, x, y: a*x*x+b*x*y+c*y*y),
    'F2': (8, lambda a, b, c, d, e, f, x, y:
           a*x*x+b*x*y+c*y*y+d*x+e*y+f),
}

# Audit correspondence of the finitely many helper meanings before using the
# restricted reader. Whitespace is immaterial; any changed formula is rejected.
EXPECTED_HELPER_BODIES = {
    'N2': 'x.sq + y.sq',
    'D2': 'x * u + y * v',
    'W2': 'x * v - y * u',
    'N3': 'x.sq + y.sq + z.sq',
    'D3': 'x*u + y*v + z*w',
    'Q2': 'a*x*x + b*x*y + c*y*y',
    'F2': 'Q2 a b c x y + d*x + e*y + f',
}


class ArithmeticReader:
    """Only +, -, *, .sq, .eq, conjunction, helper calls, and variables."""
    token_re = re.compile(r"ZT\.natLit|\.eq|\.sq|[A-Za-z_][A-Za-z_0-9']*|\d+|[()+*\-]|⋏")
    precedence = {'⋏': 10, '+': 40, '-': 40, '*': 50}

    def __init__(self, text, variables, env=None):
        self.tokens = []
        end = 0
        for m in self.token_re.finditer(text):
            if text[end:m.start()].strip():
                raise ValueError('Unsupported syntax: ' + repr(text[end:m.start()]))
            self.tokens.append(m.group())
            end = m.end()
        if text[end:].strip():
            raise ValueError('Unsupported trailing syntax: ' + text[end:])
        self.i = 0
        self.variables = variables
        self.env = {} if env is None else dict(env)

    def pop(self):
        out = self.tokens[self.i]
        self.i += 1
        return out

    def peek(self):
        return self.tokens[self.i] if self.i < len(self.tokens) else None

    def atom(self):
        token = self.pop()
        if token == '(':
            value = self.expr()
            assert self.pop() == ')'
        elif token == 'v':
            value = self.variables[int(self.pop())]
        elif token == 'ZT.natLit':
            value = sp.Integer(self.pop())
        elif token in HELPERS:
            arity, fn = HELPERS[token]
            value = fn(*(self.atom() for _ in range(arity)))
        elif token in self.env:
            value = self.env[token]
        elif token.isdigit():
            value = sp.Integer(token)
        else:
            raise ValueError('Unknown atom: ' + token)
        while self.peek() in ('.sq', '.eq'):
            op = self.pop()
            if op == '.sq':
                value = value**2
            else:
                value = [value - self.atom()]
        return value

    def expr(self, minimum=0):
        left = self.atom()
        while self.peek() in self.precedence and self.precedence[self.peek()] >= minimum:
            op = self.pop()
            right = self.expr(self.precedence[op] + 1)
            if op == '⋏':
                assert isinstance(left, list) and isinstance(right, list)
                left = left + right
            elif op == '+':
                left = left + right
            elif op == '-':
                left = left - right
            else:
                left = left * right
        return left

    def read(self):
        result = self.expr()
        assert self.i == len(self.tokens), self.tokens[self.i:]
        return result


def read_body(body, variables):
    env = {}
    body = body.lstrip()
    while body.startswith('let '):
        match = re.match(r"let ([A-Za-z_][A-Za-z_0-9']*) := ([^\n]+)\n", body)
        if match is None:
            raise ValueError('Unsupported let declaration')
        name, rhs = match.groups()
        env[name] = ArithmeticReader(rhs, variables, env).read()
        body = body[match.end():].lstrip()
    result = ArithmeticReader(body, variables, env).read()
    assert isinstance(result, list)
    return result


def expanded_zero(expr):
    expanded = sp.expand(expr)
    if expanded != 0:
        raise AssertionError('Nonzero polynomial: ' + str(expanded))
    return True


def check_candidates(source):
    for name, expected in EXPECTED_HELPER_BODIES.items():
        match = re.search(r'^def ' + name + r' .*? := (.+)$', source, re.M)
        assert match is not None
        assert re.sub(r'\s+', '', match.group(1)) == re.sub(r'\s+', '', expected)
    pattern = re.compile(
        r'def (\w+) \{n : ℕ\} \(v : Fin (\d+) → ZT n\) : Fm PTm n :=\n'
        r'(.*?)\n\ntheorem \1_open', re.S)
    records = []
    for match in pattern.finditer(source):
        name, arity, body = match.groups()
        variables = sp.symbols('v0:' + arity)
        residuals = read_body(body, variables)
        for residual in residuals:
            expanded_zero(residual)
        records.append({'name': name, 'parameters': int(arity),
                        'scalar_polynomial_equalities': len(residuals),
                        'status': 'zero polynomial residual'})
    expected_names = [row['name'] for row in json.loads(
        (ROOT / 'lean' / 'certificate_index.json').read_text())]
    assert [row['name'] for row in records] == expected_names
    assert len(records) == 24
    return records


def supplemental_checks():
    records = []

    def record(name, residuals, constraints=None, symbols=None):
        if not isinstance(residuals, (tuple, list)):
            residuals = [residuals]
        for expression in residuals:
            numerator = sp.together(expression).as_numer_denom()[0]
            if constraints:
                numerator = sp.reduced(sp.expand(numerator), constraints,
                                       *symbols)[1]
            expanded_zero(numerator)
        records.append({'name': name, 'scalar_checks': len(residuals),
                        'method': ('expanded numerator modulo stated polynomial constraints'
                                   if constraints else 'expanded polynomial numerator'),
                        'status': 'zero residual'})

    A, B, C, r = sp.symbols('A B C r')
    disc = (A-C)**2+B**2
    matrix = sp.Matrix([[A, B/2], [B/2, C]])
    lam = (A+C+r)/2
    ev = sp.Matrix([B, 2*(lam-A)])
    record('principal_axis_eigenvector', list(matrix*ev-lam*ev),
           [r*r-disc], [r, A, B, C])
    record('principal_axes_discriminant', (A+C)**2-4*matrix.det()-disc)

    a, b, c, x, y = sp.symbols('a b c x y')
    for sign in (-1, 1):
        # Independently substitute the Cartesian curve equations into the
        # squared focal distance residuals, retaining sign obligations for
        # the human proof rather than asserting them in this algebra checker.
        ellipse_residual = ((x+sign*c)**2+y*y-(a+sign*c*x/a)**2)
        ellipse_residual = sp.expand(ellipse_residual).subs(y*y, b*b*(1-x*x/(a*a)))
        ellipse_residual = sp.expand(ellipse_residual).subs(c*c, a*a-b*b)
        record('ellipse_focus_square_' + str(sign), ellipse_residual)
        hyperbola_residual = ((x+sign*c)**2+y*y-(c*x/a+sign*a)**2)
        hyperbola_residual = sp.expand(hyperbola_residual).subs(y*y, b*b*(x*x/(a*a)-1))
        hyperbola_residual = sp.expand(hyperbola_residual).subs(c*c, a*a+b*b)
        record('hyperbola_focus_square_' + str(sign), hyperbola_residual)

    dm, dp = a+c*x/a, a-c*x/a
    optical = sp.Matrix([(x+c)/dm+(x-c)/dp, y/dm+y/dp])
    normal = (2*a*b*b/(dm*dp))*sp.Matrix([x/a**2, y/b**2])
    record('ellipse_optical_normal', list(optical-normal),
           [c*c-a*a+b*b], [c, a, b, x, y])

    p = sp.symbols('p')
    n = sp.Matrix([-2*p, y])
    incoming = sp.Matrix([-1, 0])
    reflected = incoming-2*(incoming.dot(n))/n.dot(n)*n
    target = sp.Matrix([p-x, -y])/(x+p)
    record('parabola_optical_reflection', list(reflected-target),
           [y*y-4*p*x], [y, p, x])

    u = sp.Matrix(sp.symbols('u0:3'))
    v = sp.Matrix(sp.symbols('w0:3'))
    w = sp.Matrix(sp.symbols('d0:3'))
    k = u.cross(v)
    K = k.dot(k)
    c0, d0 = sp.symbols('c0 d0')
    intersection_numerator = c0*v.cross(k)+d0*k.cross(u)
    record('two_plane_intersection_numerators',
           [u.dot(intersection_numerator)-c0*K,
            v.dot(intersection_numerator)-d0*K])
    aa, bb, cc = u.dot(u), u.dot(v), v.dot(v)
    t_numerator = cc*u.dot(w)-bb*v.dot(w)
    s_numerator = bb*u.dot(w)-aa*v.dot(w)
    joining_numerator = K*w+s_numerator*v-t_numerator*u
    record('skew_line_minimizer_vector', list(joining_numerator-w.dot(k)*k))

    sphere_center = sp.Matrix(sp.symbols('o0:3'))
    point = sp.Matrix(sp.symbols('x0:3'))
    # Normal projection identity after clearing S(u)^2.
    S = u.dot(u)
    offset = u.dot(point)-c0
    h_num = S*point-offset*u
    record('normal_projection_plane_membership', u.dot(h_num)-c0*S)
    residual_num = S*point-h_num
    record('normal_projection_distance', residual_num.dot(residual_num)-offset**2*S)

    # Quadratic Taylor identity in arbitrary three coordinates.
    q00, q01, q02, q11, q12, q22 = sp.symbols('q00 q01 q02 q11 q12 q22')
    Q = sp.Matrix([[q00, q01, q02], [q01, q11, q12], [q02, q12, q22]])
    linear = sp.Matrix(sp.symbols('l0:3'))
    f = sp.symbols('f')

    def quad(z):
        return (z.T*Q*z)[0]+linear.dot(z)+f

    record('quadric_second_order_expansion',
           quad(u+v)-quad(u)-(2*Q*u+linear).dot(v)-(v.T*Q*v)[0])
    return records


def main():
    source = SOURCE.read_text()
    candidates = check_candidates(source)
    supplements = supplemental_checks()
    report = {
        'status': 'passed',
        'checker': 'SymPy ' + sp.__version__,
        'method': 'Independent symbolic polynomial expansion; no numeric sampling',
        'source': str(SOURCE.relative_to(ROOT)),
        'source_sha256': hashlib.sha256(source.encode()).hexdigest(),
        'candidate_identity_families': len(candidates),
        'candidate_scalar_equalities': sum(x['scalar_polynomial_equalities'] for x in candidates),
        'candidate_results': candidates,
        'supplemental_formula_families': len(supplements),
        'supplemental_scalar_equalities': sum(x['scalar_checks'] for x in supplements),
        'supplemental_results': supplements,
        'limitations': [
            'Does not execute, compile, typecheck, or validate any Lean proof term.',
            'Restricted statement reader implements only the listed arithmetic syntax.',
            'Polynomial checks do not establish positivity, denominator guards, '
            'constructive branch correctness, or iPRA derivability; the human proofs address these.',
            'SymPy computation is an independent algebra check, not a proof-assistant certificate.'
        ]
    }
    output = ROOT / 'artifacts' / 'symbolic_checks.json'
    output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: report[key] for key in ('status', 'checker',
          'candidate_identity_families', 'candidate_scalar_equalities',
          'supplemental_formula_families', 'supplemental_scalar_equalities')}, indent=2))


if __name__ == '__main__':
    main()
