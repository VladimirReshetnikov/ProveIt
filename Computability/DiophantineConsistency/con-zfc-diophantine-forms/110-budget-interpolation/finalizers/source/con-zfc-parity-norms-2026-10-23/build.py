#!/usr/bin/env python3
"""Build two 16-integer polynomials by an odd-carrier norm merger.

Pure Python; no proof-search or network call. The parent packet and all six
fixed integer payloads are copied unchanged from the pinned incoming archive.
"""
import ast
import gzip
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PRIME = 1_000_000_007


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_ports():
    binding = json.loads((ROOT / 'coefficients/BINDING.json').read_text())
    ports = {}
    for name, item in binding['ports'].items():
        raw = gzip.decompress((ROOT / 'coefficients' / item['file']).read_bytes())
        require(hashlib.sha256(raw).hexdigest() == item['sha256_raw'], name)
        ports[name] = int.from_bytes(raw, 'little')
        require(ports[name].bit_length() == item['bits'], name + ' bits')
    return ports


def expr(text, env):
    def visit(node):
        if isinstance(node, ast.Name):
            return env[node.id]
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return node.value
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -visit(node.operand)
        if isinstance(node, ast.BinOp):
            a, b = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add):
                return a + b
            if isinstance(node.op, ast.Sub):
                return a - b
            if isinstance(node.op, ast.Mult):
                return a * b
            if isinstance(node.op, ast.Pow):
                require(isinstance(b, int) and b >= 0, 'nonconstant power')
                return a ** b
        raise ValueError(ast.dump(node))
    return visit(ast.parse(text, mode='eval').body)


class Uni:
    """Exact polynomials over F_p, represented by all coefficients."""
    def __init__(self, coeffs):
        self.c = [int(x) % PRIME for x in coeffs]
        while len(self.c) > 1 and self.c[-1] == 0:
            self.c.pop()

    @staticmethod
    def lift(value):
        return value if isinstance(value, Uni) else Uni([value])

    def __add__(self, other):
        other = self.lift(other)
        n = max(len(self.c), len(other.c))
        return Uni([(self.c[i] if i < len(self.c) else 0) +
                    (other.c[i] if i < len(other.c) else 0) for i in range(n)])
    __radd__ = __add__

    def __neg__(self):
        return Uni([-x for x in self.c])

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) + -self

    def __mul__(self, other):
        other = self.lift(other)
        out = [0] * (len(self.c) + len(other.c) - 1)
        for i, a in enumerate(self.c):
            for j, b in enumerate(other.c):
                out[i+j] = (out[i+j] + a*b) % PRIME
        return Uni(out)
    __rmul__ = __mul__

    def __pow__(self, n):
        require(isinstance(n, int) and n >= 0, 'power')
        out, base = Uni([1]), self
        while n:
            if n & 1:
                out = out * base
            n >>= 1
            if n:
                base = base * base
        return out


class Deg:
    """Safe degree upper bounds; constants have degree zero."""
    def __init__(self, d):
        self.d = d

    @staticmethod
    def lift(x):
        return x if isinstance(x, Deg) else Deg(0)

    def __add__(self, other):
        return Deg(max(self.d, self.lift(other).d))
    __radd__ = __add__
    __sub__ = __add__
    __rsub__ = __add__

    def __neg__(self):
        return self

    def __mul__(self, other):
        return Deg(self.d + self.lift(other).d)
    __rmul__ = __mul__

    def __pow__(self, n):
        require(isinstance(n, int) and n >= 0, 'degree power')
        return Deg(self.d * n)


def evaluate(packet, inputs, ports):
    env = dict(ports)
    env.update(inputs)
    for name, value in packet['polynomial_abbreviations']:
        env[name] = expr(value, env)
    return [expr(value, env) for value in packet['factored_residuals']]


def packet(parent, finalizer, centered=False):
    variables = [x for x in parent['variables'] if x not in ('tau', 'y_gap')]
    variables.append('t_parity')
    abbreviations = parent['polynomial_abbreviations'] + [
        ['z0', 'q*(3*w3+1)*Y**2'],
        ['A4', 'q*(3*w3+1)*Y**2*(X*Y**2+1)*k**2'],
        ['A', '4*A4+1'],
        ['Q', 'I**2'],
        ['delta', 'Q-1'],
        ['r_aux', 'Q*V**2-1'],
    ]
    if centered:
        abbreviations += [
            ['H16', 't_parity*(t_parity+1)+4*z0*k*t_parity+2*z0*k-z0*k**2'],
            ['norm16', '(delta*H16-r_aux)**2-A*delta*r_aux'],
        ]
    else:
        abbreviations += [['norm16', '(delta*(t_parity*(t_parity+1)-A4)-r_aux)**2-A*delta*r_aux']]
    rows = [parent['factored_residuals'][1],
            parent['factored_residuals'][2],
            parent['factored_residuals'][4], 'norm16']
    return {
        'name': ('centered16_' if centered else 'parity16_') + finalizer,
        'domain': 'unrestricted integers',
        'variables': variables,
        'variable_count': len(variables),
        'fixed_numerals': parent['fixed_numerals'],
        'coefficient_binding': 'coefficients/BINDING.json',
        'polynomial_abbreviations': abbreviations,
        'factored_residuals': rows,
        'residual_count': len(rows),
        'finalizer': finalizer,
        'single_polynomial': ('sum(r_i**2 for r_i in residuals)' if finalizer == 'sos'
                              else 'product(1+4*r_i for r_i in residuals)-1'),
        'source_parent': 'parent/degree88_17.json',
        'parent_sha256': hashlib.sha256((ROOT / 'parent/degree88_17.json').read_bytes()).hexdigest(),
        'restoration': {
            'x': '4*z0*k+2*t_parity+1' if centered else '2*t_parity+1',
            'tau_root': '(delta*(x*x+A)-4*r_aux)/(2*x*delta)',
            'aux_root': '(x-tau_root)/2',
            'tau': '2*tau_root-2*P+k',
            'y_gap': 'aux_root-V',
        },
        'restoration_note': 'These rational expressions are proved integral on the zero set; x and delta are proved nonzero.',
        'proof_status': 'Ordinary universal proof relative to the explicitly retained native/Pell/refutation source calibration; no new kernel certificate.',
    }


def packet15(parent, finalizer):
    variables = [x for x in parent['variables'] if x not in ('tau', 'y_gap', 'pair_pos3')]
    variables.append('t_parity')
    abbreviations = parent['polynomial_abbreviations'] + [
        ['A4', 'q*(3*w3+1)*Y**2*(X*Y**2+1)*k**2'],
        ['A', '4*A4+1'],
        ['Q', 'I**2'],
        ['delta', 'Q-1'],
        ['r_aux', 'Q*V**2-1'],
        ['Caux', 'delta*r_aux'],
        ['b_guard', 'G*Zeta-(pair_root**2-G-Zeta+1)**2-1-pair_pos1**2-pair_pos2**2'],
        ['B_guard', '4*b_guard+1'],
        ['x_parity', '2*t_parity+1'],
        ['U15', 't_parity*(t_parity+1)-A4-B_guard+4*Caux'],
        ['M15', 'U15**2+4*x_parity**2*Caux-A*B_guard'],
        ['norm15', 'M15**2-16*x_parity**2*U15**2*Caux'],
    ]
    rows = [parent['factored_residuals'][1], parent['factored_residuals'][2], 'norm15']
    return {
        'name': 'parity15_' + finalizer,
        'domain': 'unrestricted integers',
        'variables': variables,
        'variable_count': len(variables),
        'fixed_numerals': parent['fixed_numerals'],
        'coefficient_binding': 'coefficients/BINDING.json',
        'polynomial_abbreviations': abbreviations,
        'factored_residuals': rows,
        'residual_count': len(rows),
        'finalizer': finalizer,
        'single_polynomial': ('sum(r_i**2 for r_i in residuals)' if finalizer == 'sos'
                              else 'product(1+4*r_i for r_i in residuals)-1'),
        'source_parent': 'parent/degree88_17.json',
        'parent_sha256': hashlib.sha256((ROOT / 'parent/degree88_17.json').read_bytes()).hexdigest(),
        'radical_equation': '2*t_parity+1 = epsilon1*sqrt(A)+2*epsilon2*sqrt(B_guard)+4*epsilon3*sqrt(Caux)',
        'radical_note': 'This describes the norm proof only; no radicals occur in the literal polynomial.',
        'restoration': {
            'tau': '2*tau_root-2*P+k',
            'y_gap': 'aux_root-V',
            'pair_pos3': '(guard_root-1)/2',
        },
        'restoration_note': 'The norm and the squareclass parity argument force A and B_guard to be odd integer squares and Caux to be an integer square; aux_root=sqrt(Caux)/delta is rational and proved integral by the retained consecutive-Pell denominator lemma (Q=0 handled directly).',
        'proof_status': 'Ordinary universal proof relative to the named native/Pell/refutation calibration and rational Pell integrality lemma; no new kernel certificate.',
    }


def main():
    parent = json.loads((ROOT / 'parent/degree88_17.json').read_text())
    ports = read_ports()
    cert = {'prime': PRIME, 'source_parent_sha256': hashlib.sha256((ROOT / 'parent/degree88_17.json').read_bytes()).hexdigest(), 'equations': {}}
    packets = [packet(parent, f, c) for c in (False, True) for f in ('sos', 'unit_product')]
    packets += [packet15(parent, f) for f in ('sos', 'unit_product')]
    for p in packets:
        finalizer = p['finalizer']
        variables = p['variables']
        require(len(variables) == p['variable_count'] and len(set(variables)) == len(variables), 'variable list')
        upper = evaluate(p, {v: Deg(1) for v in variables}, ports)
        slopes = {v: (i+2)**2+1 for i, v in enumerate(variables)}
        rows = evaluate(p, {v: Uni([0, slopes[v]]) for v in variables}, {k: v % PRIME for k, v in ports.items()})
        require([len(row.c)-1 for row in rows] == [r.d for r in upper], 'degree specialization')
        if finalizer == 'sos':
            value = sum((r*r for r in rows), Uni([0]))
            degree = 2*max(r.d for r in upper)
        else:
            value = Uni([1])
            for r in rows:
                value = value*(1+4*r)
            value = value-1
            degree = sum(r.d for r in upper)
        require(len(value.c)-1 == degree and value.c[-1] != 0, 'exact final degree')
        p['exact_degree'] = degree
        p['degree_certificate'] = {
            'method': 'safe multivariate degree bound plus exact univariate specialization modulo a prime',
            'prime': PRIME,
            'slopes': slopes,
            'residual_degree_bounds': [r.d for r in upper],
            'residual_leading_coefficients_mod_prime': [r.c[-1] for r in rows],
            'final_degree': degree,
            'final_leading_coefficient_mod_prime': value.c[-1],
        }
        (ROOT / (p['name']+'.json')).write_text(json.dumps(p, indent=2, sort_keys=True)+'\n')
        cert['equations'][p['name']] = p['degree_certificate']
    (ROOT / 'DEGREE_CERTIFICATES.json').write_text(json.dumps(cert, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k: {'degree': v['final_degree'], 'residual_degrees': v['residual_degree_bounds']} for k,v in cert['equations'].items()}, indent=2))


if __name__ == '__main__':
    main()
