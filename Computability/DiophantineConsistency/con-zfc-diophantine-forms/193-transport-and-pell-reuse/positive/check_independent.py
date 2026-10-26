#!/usr/bin/env python3
"""Independent exact review of whole190.json; imports no producer.

Authenticates unchanged parent rows, verifies the new center in a free
integer polynomial ring, proves its exact degree by the entire leading
form, and checks actual dependence on each independent input modulo a prime.
The unbounded arithmetic proof is separate; this program does not prove or
decide consistency, search for a zero, or replay the native calibration.
"""
from collections import Counter
from copy import deepcopy
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PARENT_SHA = '6af0c97120fefba17920dbb517facc1d1ee403ad8388c8dee9523ee2e94b2449'
DIM = 7


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Poly:
    def __init__(self, data=0):
        if isinstance(data, Poly):
            self.d = data.d
        elif isinstance(data, int):
            self.d = {(0,) * DIM: data} if data else {}
        else:
            self.d = {m: c for m, c in data.items() if c}

    def __add__(self, other):
        other = Poly(other)
        out = self.d.copy()
        for m, c in other.d.items():
            out[m] = out.get(m, 0) + c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.d.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        other = Poly(other)
        out = {}
        for a, c in self.d.items():
            for b, d in other.d.items():
                m = tuple(x + y for x, y in zip(a, b))
                out[m] = out.get(m, 0) + c * d
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, power):
        require(isinstance(power, int) and power >= 0, 'Invalid fixed power')
        ans, base = Poly(1), self
        while power:
            if power & 1:
                ans = ans * base
            base = base * base
            power //= 2
        return ans

    def __eq__(self, other):
        return self.d == Poly(other).d

    def degree(self, weights):
        return max((sum(x * y for x, y in zip(m, weights))
                    for m in self.d), default=-1)

    def top(self, weights):
        degree = self.degree(weights)
        return Poly({m: c for m, c in self.d.items()
                     if sum(x * y for x, y in zip(m, weights)) == degree})

    def substitute(self, images):
        powers = {}
        result = Poly(0)
        for m, c in self.d.items():
            term = Poly(c)
            for j, exponent in enumerate(m):
                if exponent:
                    key = (j, exponent)
                    if key not in powers:
                        powers[key] = images[j] ** exponent
                    term = term * powers[key]
            result = result + term
        return result


def var(index):
    m = [0] * DIM
    m[index] = 1
    return Poly({tuple(m): 1})


def quotient_A(polynomial, power):
    return Poly({(m[0] - power,) + m[1:]: c
                 for m, c in polynomial.d.items() if m[0] >= power})


def half(polynomial):
    require(all(c % 2 == 0 for c in polynomial.d.values()),
            'The formal half-quotient is not integral')
    return Poly({m: c // 2 for m, c in polynomial.d.items()})


def verify_graph(equation, parent):
    for key in ('domain', 'witnesses', 'fixed_numerals', 'output'):
        require(equation[key] == parent[key], 'Altered source interface: ' + key)
    require(len(equation['witnesses']) == 10, 'Expected ten inputs')
    rows = equation['source']
    require(len(rows) == equation['operations'] == 118, 'Wrong operation count')
    require(dict(Counter(r[1] for r in rows)) == equation['operation_breakdown'],
            'Wrong operation breakdown')
    known = set(equation['witnesses'] + equation['fixed_numerals'])
    by_name = {}
    for name, op, left, right in rows:
        require(name not in known and op in '+-*', 'Non-DAG or bad operator')
        for arg in (left, right):
            require(isinstance(arg, int) or arg in known, 'Unknown operand')
        known.add(name)
        by_name[name] = [name, op, left, right]
    live = {equation['output']}
    for name, op, left, right in reversed(rows):
        if name in live:
            live.update(a for a in (left, right) if isinstance(a, str))
    require(set(by_name) <= live, 'A reported operation is dead')
    require(set(equation['witnesses'] + equation['fixed_numerals']) <= live,
            'An input or fixed port is structurally dead')
    allowed_change = {'center', 'RG'}
    removed = {'L', 'LBt'}
    for row in parent['source']:
        name = row[0]
        if name in removed:
            require(name not in by_name, 'Old transport gate survived')
        elif name not in allowed_change:
            require(by_name.get(name) == row, 'Altered inherited row: ' + name)
    require(by_name['center'] == ['center', '-', 'n', 'new_Omega'],
            'Wrong folded carrier')
    require(by_name['RG'] == ['RG', '*', 'M2', 'new_scaledG'],
            'Wrong norm scaling')
    parent_names = {r[0] for r in parent['source']}
    require(all(name in parent_names or name.startswith('new_') for name in by_name),
            'Unclassified introduced row')

    # Seven free symbols A,y0,k,U,b,c,B. Evaluate the ACTUAL new graph.
    A, y0, k, U, b, c, B = [var(j) for j in range(DIM)]
    v = y0 * (A - y0 - 1)
    ell = k * v
    E = 1 + k ** 2 * v * (v + 1)
    Delta = A ** 2 - 1
    G = E * (1 + Delta * U ** 2 * E)
    V = (1 + 2 * Delta * U ** 2 * E) * b - c
    F = E * V
    omega = U * (4 * A * F - 2 * quotient_A(F, 1)
                 - half(quotient_A(F, 3)))
    folded = omega + A * U ** 3 * b ** 2 * B
    values = dict(Am1=A-1, k=k, qY=y0, V0kk=ell+k, U=U,
                  cTR=b, c=c, Dtau=E, V=V, Bt=B, Dg=G)
    new_names = []
    for name, op, left, right in rows:
        if not name.startswith('new_'):
            continue
        new_names.append(name)
        def get(arg):
            return Poly(arg) if isinstance(arg, int) else values[arg]
        x, y = get(left), get(right)
        values[name] = x+y if op == '+' else x-y if op == '-' else x*y
    require(len(new_names) == 33, 'Wrong number of introduced rows')
    require(values['new_Omega'] == folded, 'False polynomial center identity')
    require(values['new_scaledG'] == 16*G, 'False scaled norm identity')
    weights = (4, 2, 1, 5, 4, 2, 2)
    defect = folded ** 2 - 16 * G * V ** 2
    unfolded_defect = omega ** 2 - 16 * G * V ** 2
    expected_top = (8*A**8*y0**8*k**8*U**6*b**2
                    -48*A**6*y0**12*k**8*U**6*b**2)
    require(folded.degree(weights) == 59, 'Center degree is not 59')
    require(defect.degree(weights) == 94, 'Defect degree is not 94')
    require(defect.top(weights) == expected_top, 'Incomplete degree-94 form')
    require(len(unfolded_defect.d) == 594 and len(omega.d) == 84,
            'Wrong unfolded center/defect support')
    require(unfolded_defect.degree(weights) == 94
            and unfolded_defect.top(weights) == expected_top,
            'Wrong unfolded degree certificate')

    # Independent substitution of actual full leading forms, using q0=beta*J.
    q0, w, s, i, eta, zeta, Fcoord = [var(j) for j in range(DIM)]
    k0 = eta + zeta
    A0, y00 = q0**2*w*s, q0*s
    U0 = i*k0**2*s**2
    b0 = -q0**3*(q0-Fcoord)
    E0 = k0**2*q0**6*w**2*s**4
    G0 = A0**2*U0**2*E0**2
    Q0 = 4*A0**4*U0**2*G0
    M0 = 24*q0**10*w*s
    # This complete degree-94 form is independent of B, so substitute zero
    # in that unused slot rather than inventing an image for its leading form.
    ptop = Q0*M0**2*expected_top.substitute(
        [A0, y00, k0, U0, b0, k0*s, Poly(0)])
    claimed = (9*2**11*q0**74*w**18*s**52*i**10*k0**32
               *(q0-Fcoord)**2*(w**2-6*s**2))
    require(ptop == claimed and ptop.degree((1,)*DIM) == 190,
            'Wrong complete degree-190 homogeneous component')
    require(len(ptop.d) == 198, 'Wrong leading support')
    # The remaining terms have strictly smaller degrees: the carrier with
    # n alone has degree <=14, so its cross term is <=72+12+59+14=157.
    # The term M^2*defect has degree118; Q lifts it to190. The final
    # correction has degree <=142. These are symbolic weighted bounds.
    return {'operations': len(rows), 'operation_breakdown': equation['operation_breakdown'],
            'new_rows': len(new_names), 'center_terms': len(omega.d),
            'folded_center_terms': len(folded.d), 'defect_terms': len(defect.d),
            'unfolded_defect_terms': len(unfolded_defect.d),
            'defect_weighted_degree': 94, 'exact_degree': 190,
            'complete_leading_form_terms': len(ptop.d)}


def load_coefficients(equation):
    constants = {}
    for name, desc in equation['coefficient_binding']['ports'].items():
        path = ROOT / equation['coefficient_binding']['path'] / desc['file']
        compressed = path.read_bytes()
        require(hashlib.sha256(compressed).hexdigest() == desc['gzip_sha256'],
                'Changed compressed numerical payload: ' + name)
        raw = gzip.decompress(compressed)
        require(hashlib.sha256(raw).hexdigest() == desc['raw_sha256'],
                'Changed numerical payload: ' + name)
        constants[name] = int.from_bytes(raw, 'little')
        require(constants[name].bit_length() == desc['bits'], 'Wrong bit count')
    require(constants['beta'] == (1 << 590069)-1, 'Wrong fixed beta')
    return constants


def dependence_certificate(equation, constants):
    modulus = 1000000007
    count = len(equation['witnesses'])
    found = {}
    fixtures = []
    for shift in (2, 5, 11):
        inputs = [shift+j for j in range(count)]
        values = {name: (number % modulus, [0]*count)
                  for name, number in constants.items()}
        for j, (name, number) in enumerate(zip(equation['witnesses'], inputs)):
            gradient = [0]*count
            gradient[j] = 1
            values[name] = (number, gradient)
        for name, op, left, right in equation['source']:
            def get(arg):
                return (arg % modulus, [0]*count) if isinstance(arg, int) else values[arg]
            x, dx = get(left)
            y, dy = get(right)
            if op == '+':
                z, dz = x+y, [a+b for a,b in zip(dx,dy)]
            elif op == '-':
                z, dz = x-y, [a-b for a,b in zip(dx,dy)]
            else:
                z, dz = x*y, [a*y+x*b for a,b in zip(dx,dy)]
            values[name] = (z % modulus, [a % modulus for a in dz])
        value, gradient = values[equation['output']]
        fixtures.append({'inputs': inputs, 'value': value, 'gradient': gradient})
        for name, derivative in zip(equation['witnesses'], gradient):
            if derivative:
                found[name] = {'fixture': len(fixtures)-1, 'derivative': derivative}
        if len(found) == count:
            break
    require(len(found) == count, 'No exact modular dependence certificate for an input')
    return {'modulus': modulus, 'fixtures': fixtures, 'nonzero_derivatives': found}


def main():
    parent_bytes = (ROOT/'parent87.json').read_bytes()
    require(hashlib.sha256(parent_bytes).hexdigest() == PARENT_SHA, 'Changed frozen parent')
    parent = json.loads(parent_bytes)
    equation = json.loads((ROOT/'whole190.json').read_text())
    result = verify_graph(equation, parent)
    coefficients = load_coefficients(equation)
    result['actual_input_dependence'] = dependence_certificate(equation, coefficients)
    corruptions = [('new_ScShift', '+'), ('new_S', '+'), ('RG', '+')]
    rejected = []
    for name, operator in corruptions:
        corrupted = deepcopy(equation)
        for row in corrupted['source']:
            if row[0] == name:
                row[1] = operator
        corrupted['operation_breakdown'] = dict(Counter(r[1] for r in corrupted['source']))
        try:
            verify_graph(corrupted, parent)
        except (ValueError, KeyError):
            rejected.append(name)
        else:
            raise ValueError('Accepted deliberately corrupted graph: ' + name)
    result['deliberate_corruptions_rejected'] = rejected
    result['equation_sha256'] = hashlib.sha256((ROOT/'whole190.json').read_bytes()).hexdigest()
    result['scope'] = 'Finite exact algebra and input-dependence checks; unbounded proofs are separate.'
    output = ROOT/'INDEPENDENT_CHECK.json'
    output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'actual_input_dependence'}, indent=2))


if __name__ == '__main__':
    main()
