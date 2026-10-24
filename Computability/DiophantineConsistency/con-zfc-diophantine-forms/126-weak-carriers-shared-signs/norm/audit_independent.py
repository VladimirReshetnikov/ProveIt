#!/usr/bin/env python3
"""Independent finite algebra audit; Python standard library only.

This file imports neither the producer nor its DAG implementation.  It checks
exact local free-ring identities, the complete three-root norm, coefficient
bytes, topology/liveness, attained leading forms, and targeted corruptions.
It does not mechanize the unbounded arithmetic/calibration proof.
"""
from __future__ import annotations

import argparse
import copy
import gzip
import hashlib
import itertools
import json
import math
import random
from collections import Counter
from functools import lru_cache
from pathlib import Path


ROOT = Path(__file__).resolve().parent
VARIABLES = ['j', 'C', 'z', 'h', 'r', 'v', 'w', 'T', 'c', 'n', 's']
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
EXPECTED_HASHES = {
    'beta': '6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
    'K0': '18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
    'MC': '3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
    'MF': '78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722',
    'cone_A': '66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615',
    'cone_B': '42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401',
}
EXPECTED = {
    ('cubic', False): (120, 488), ('cubic', True): (123, 464),
    ('mixed', False): (126, 456), ('mixed', True): (129, 416),
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


class Poly:
    """Sparse commutative Z-polynomial, with literal symbol-name monomials."""
    def __init__(self, terms=0):
        if isinstance(terms, Poly):
            self.t = terms.t
        elif isinstance(terms, int):
            self.t = {(): terms} if terms else {}
        else:
            self.t = {tuple(k): v for k, v in terms.items() if v}

    @staticmethod
    def symbol(name):
        return Poly({(name,): 1})

    def __add__(self, other):
        out = dict(self.t)
        for key, val in Poly(other).t.items():
            out[key] = out.get(key, 0) + val
            if not out[key]:
                del out[key]
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({key: -val for key, val in self.t.items()})

    def __sub__(self, other):
        return self + -Poly(other)

    def __rsub__(self, other):
        return Poly(other) + -self

    def __mul__(self, other):
        out = {}
        for left, a in self.t.items():
            for right, b in Poly(other).t.items():
                key = tuple(sorted(left + right))
                out[key] = out.get(key, 0) + a * b
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, 'bad power')
        result, base = Poly(1), self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent >>= 1
            if exponent:
                base = base * base
        return result

    def __eq__(self, other):
        return self.t == Poly(other).t


def symbolic_specification(emit, ref, inputs, ports, chart, centered):
    """Independent transcription of every declared mathematical register."""
    x, p = inputs, ports
    emit('J', 6*x['j']+1)
    emit('qm', p['beta']*ref('J'))
    emit('q', ref('qm')+1)
    emit('q2', ref('q')**2)
    emit('W', 12*x['w']+4)
    emit('X', ref('q')*ref('W'))
    emit('Y', ref('q')*x['v'] if chart == 'mixed'
         else (2*x['v']+1)*ref('q2')*ref('q'))
    emit('E', ref('X')*ref('Y'))
    emit('a', ref('E')+ref('Y'))
    emit('H', 4*ref('a')+3)
    emit('Delta', ref('a')**2+ref('H'))
    emit('F', (p['K0']+ref('W'))*x['C']-x['z']*ref('qm'))
    emit('R', (ref('q')*(ref('q')-ref('F'))-x['C'])*(ref('q2')-1)
         +(p['MC']+ref('q')*p['MF'])*ref('J'))
    emit('k', ref('R')+1+x['h']*ref('E'))
    emit('c', x['c'])
    emit('eta', x['c']-ref('Y')*ref('k'))
    emit('error', (p['cone_A']*ref('F')-ref('q'))**2
         +(p['cone_B']*x['C']-ref('q'))**2)
    emit('budget', ref('k')**2*(ref('q2')-ref('error'))
         -4*ref('q2')*ref('eta')**2)
    emit('ell', ref('E')*ref('Y'))
    emit('L', ref('ell')*ref('k'))
    emit('Dt', 1+ref('L')*(ref('L')+ref('k')))
    emit('Dguard', 3*ref('budget')-4)
    emit('Dg', 1+ref('Dguard')*ref('Dt')*x['s']**2)
    emit('P', ref('Dt')*ref('Dg'))
    emit('I', x['r']*x['c']**2)
    emit('I2', ref('I')**2)
    emit('strong', ref('Delta')*ref('I2'))
    emit('Df', 1+ref('strong'))
    emit('Q', ref('Delta')*ref('strong'))
    emit('delta', ref('Q')-1)
    emit('V', ref('Df')*(x['c']-ref('R')+4*ref('I')*x['T'])-x['c'])
    emit('Cy', ref('Q')*ref('V')**2-1)
    emit('Da', ref('delta')*ref('Cy'))
    emit('K', ref('X')*(3*x['c']-2*ref('X'))+2)
    if chart == 'mixed':
        emit('M', 2*ref('q2'))
        emit('Dcarrier', ref('M')*ref('H'))
        emit('carrier', ref('M')*ref('K')+ref('H')*(x['v']-ref('q2')))
        emit('zc', ref('Dcarrier')*x['T']+ref('carrier'))
        emit('M2', ref('M')**2)
        emit('M4', ref('M2')**2)
        emit('S', x['s']*x['r']*ref('M4')*ref('Dcarrier'))
    else:
        emit('Dcarrier', ref('H'))
        emit('zc', ref('H')*x['T']+ref('K'))
        emit('S', x['s']*x['r']*ref('H'))
    emit('Dc2', ref('Dcarrier')**2)
    emit('Dc3', ref('Dc2')*ref('Dcarrier'))
    emit('zc2', ref('zc')**2)
    emit('obstruction', (ref('zc2')+3*ref('Dc2'))
         *(ref('zc2')*ref('zc')-19*ref('Dc3')))
    if centered:
        emit('shift', 3*ref('Q')*ref('V'))
    emit('Z', ref('S')*(x['n']+(ref('shift') if centered else 0))
         -ref('obstruction'))
    emit('S2', ref('S')**2)
    emit('u', ref('S2')*ref('Df'))
    emit('b', 9*ref('S2')*ref('Da'))
    emit('e', 81*ref('S2')*ref('P'))
    emit('Z2', ref('Z')**2)
    emit('ub_sum', ref('u')+ref('b'))
    emit('ub', ref('u')*ref('b'))
    emit('wnorm', ref('Z2')-ref('ub_sum')-ref('e'))
    emit('inner', ref('wnorm')**2-4*(ref('ub')+ref('e')*ref('ub_sum')))
    emit('output', ref('inner')**2-64*ref('ub')*ref('e')*ref('Z2'))


def validate_graph(packet):
    require(packet['schema'] == 'integer-polynomial-dag-v1', 'schema')
    require(packet['domain'] == 'unrestricted integers', 'domain')
    require(packet['variables'] == VARIABLES and packet['variable_count'] == 11,
            'coordinate closure')
    pair = packet['chart'], packet['centered']
    require(pair in EXPECTED, 'unknown chart')
    expected_ops, expected_degree = EXPECTED[pair]
    nodes = packet['nodes']
    arithmetic, syntax_degrees = Counter(), []
    found_vars, found_ports = [], []
    for i, node in enumerate(nodes):
        require(isinstance(node, list) and node, 'malformed node')
        op = node[0]
        if op in ('add', 'sub', 'mul'):
            require(len(node) == 3 and all(type(k) is int and 0 <= k < i
                                        for k in node[1:]), 'topology')
            arithmetic[op] += 1
            a, b = (syntax_degrees[k] for k in node[1:])
            syntax_degrees.append(a+b if op == 'mul' else max(a, b))
        else:
            require(op in ('variable', 'coefficient', 'integer') and len(node) == 2,
                    'forbidden node operation')
            if op == 'variable':
                require(node[1] in VARIABLES, 'unknown variable')
                found_vars.append(node[1]); syntax_degrees.append(1)
            elif op == 'coefficient':
                require(node[1] in PORTS, 'unknown coefficient')
                found_ports.append(node[1]); syntax_degrees.append(0)
            else:
                require(type(node[1]) is int, 'noninteger literal')
                syntax_degrees.append(0)
    require(sorted(found_vars) == sorted(VARIABLES), 'missing/duplicate coordinate')
    require(sorted(found_ports) == sorted(PORTS), 'missing/duplicate fixed port')
    output = packet['output']
    require(type(output) is int and 0 <= output < len(nodes), 'bad output')
    live, pending = set(), [output]
    while pending:
        i = pending.pop()
        if i not in live:
            live.add(i)
            if nodes[i][0] in ('add', 'sub', 'mul'):
                pending.extend(nodes[i][1:])
    require(len(live) == len(nodes), 'dead node')
    require(dict(arithmetic) == packet['operation_counts'], 'operation categories')
    require(sum(arithmetic.values()) == packet['operations'] == expected_ops,
            'operation count')
    require(packet['exact_degree'] == expected_degree, 'degree label')
    require(packet['syntactic_degree_bound'] == syntax_degrees[output],
            'syntactic bound')
    for label, index in packet['named_registers'].items():
        require(type(index) is int and 0 <= index < len(nodes), 'bad register index')
        require(packet['register_degree_bounds'][label] == syntax_degrees[index],
                'register degree bound')
    return {'operations': expected_ops, 'exact_degree': expected_degree,
            'syntactic_degree_bound': syntax_degrees[output], 'nodes': len(nodes)}


def check_local_identities(packet):
    nodes, registers = packet['nodes'], packet['named_registers']
    known, checked = {}, []
    x = {name: Poly.symbol('v_'+name) for name in VARIABLES}
    p = {name: Poly.symbol('p_'+name) for name in PORTS}
    for i, node in enumerate(nodes):
        if node[0] == 'variable': known[i] = x[node[1]]
        elif node[0] == 'coefficient': known[i] = p[node[1]]
        elif node[0] == 'integer': known[i] = Poly(node[1])

    def ref(label):
        require(label in checked, 'specification uses an unverified register '+label)
        return known[registers[label]]

    def emit(label, expected):
        require(label in registers, 'missing named register '+label)
        @lru_cache(None)
        def expand(i):
            if i in known: return known[i]
            op, left, right = nodes[i]
            a, b = expand(left), expand(right)
            return a+b if op == 'add' else a-b if op == 'sub' else a*b
        actual = expand(registers[label])
        require(actual == expected, 'free-ring specification mismatch at '+label)
        if registers[label] not in known:
            known[registers[label]] = Poly.symbol('r_'+label)
        checked.append(label)

    symbolic_specification(emit, ref, x, p, packet['chart'], packet['centered'])
    require(set(checked) == set(registers), 'unverified/extra named register')
    require(registers['output'] == packet['output'], 'output not bound')
    return len(checked)


def generic_norm_and_centering():
    Z, u, b, e = (Poly.symbol(s) for s in ('Z', 'u', 'b', 'e'))
    norm = ((Z*Z-u-b-e)**2-4*(u*b+u*e+b*e))**2-64*u*b*e*Z*Z
    z, a, c, d = (Poly.symbol(s) for s in ('z', 'a', 'c', 'd'))
    product = Poly(1)
    for signs in itertools.product((-1, 1), repeat=3):
        product *= z-signs[0]*a-signs[1]*c-signs[2]*d
    converted = {}
    for monomial, coefficient in product.t.items():
        counts = Counter(monomial)
        require(all(counts[r] % 2 == 0 for r in ('a', 'c', 'd')),
                'odd radical power survived conjugation')
        key = tuple(sorted(('Z',)*counts['z']+('u',)*(counts['a']//2)
                           +('b',)*(counts['c']//2)+('e',)*(counts['d']//2)))
        converted[key] = converted.get(key, 0)+coefficient
    require(norm == Poly(converted), 'complete eight-factor norm identity')
    require(len(norm.t) == 35, 'norm coefficient count')
    omega = Z*Z-b
    reduced = ((omega-u-e)**2-4*(u*e+b*(u+e)))**2-64*u*b*e*Z*Z
    require(norm == reduced, 'cancellation-aware norm identity')
    S, Q, V = (Poly.symbol(s) for s in ('S', 'Q', 'V'))
    auxiliary = 9*S*S*(Q-1)*(Q*V*V-1)
    center = 3*S*Q*V
    defect = 9*S*S*(-Q*(V*V+1)+1)
    require(auxiliary-center*center == defect, 'center defect identity')
    return {'generic_norm_terms': 35, 'eight_conjugates_checked': 8,
            'center_defect_identity': True, 'reduced_norm_identity': True}


def leading_forms(packet):
    """Exact highest homogeneous parts before the deliberate norm cancellation."""
    nodes, registers = packet['nodes'], packet['named_registers']
    stop = max(registers[k] for k in ('u', 'b', 'e', 'Z'))
    tops, degrees = [], []
    for node in nodes[:stop+1]:
        op = node[0]
        if op == 'variable': degree, top = 1, Poly.symbol('v_'+node[1])
        elif op == 'coefficient': degree, top = 0, Poly.symbol('p_'+node[1])
        elif op == 'integer': degree, top = 0, Poly(node[1])
        else:
            left, right = node[1:]
            if op == 'mul':
                degree, top = degrees[left]+degrees[right], tops[left]*tops[right]
            else:
                degree = max(degrees[left], degrees[right])
                a = tops[left] if degrees[left] == degree else Poly(0)
                b = tops[right] if degrees[right] == degree else Poly(0)
                top = a+b if op == 'add' else a-b
        require(bool(top.t), 'unhandled leading cancellation in prefix')
        degrees.append(degree); tops.append(top)
    degree = lambda name: degrees[registers[name]]
    top = lambda name: tops[registers[name]]
    mixed, centered = packet['chart'] == 'mixed', packet['centered']
    required_degrees = ({'I': 3, 'Df': 14, 'Q': 22, 'V': 19, 'Da': 82,
                         'Dt': 22, 'budget': 16, 'Dg': 40, 'P': 62,
                         'S': 16, 'obstruction': 35, 'u': 46, 'b': 114, 'e': 94}
                        if mixed else
                        {'I': 3, 'Df': 18, 'Q': 30, 'V': 23, 'Da': 106,
                         'Dt': 34, 'budget': 24, 'Dg': 60, 'P': 94,
                         'S': 8, 'obstruction': 35, 'u': 34, 'b': 122, 'e': 110})
    for label, expected in required_degrees.items():
        require(degree(label) == expected, 'prefix degree '+label)

    if centered:
        center_degree = degree('S')+degree('Q')+degree('V')
        # Z=center+(Sn-Ac); the exact defect was checked above.
        omega_bound = max(70, center_degree+35,
                          2*degree('S')+degree('Q')+2*degree('V'))
        be_degree = degree('b')+degree('e')
        competitors = [2*max(omega_bound, degree('u'), degree('e')),
                       degree('u')+degree('e'), degree('b')+degree('u')]
        require(all(d < be_degree for d in competitors), 'bracket leading tie')
        correction_degree = degree('u')+degree('b')+degree('e')+2*degree('Z')
        exact_degree = 2*be_degree
        require(correction_degree < exact_degree, 'output leading tie')
        final_top = 16*top('b')**2*top('e')**2
        x = {name: Poly.symbol('v_'+name) for name in VARIABLES}
        beta = Poly.symbol('p_beta')
        q0, X0 = 6*beta*x['j'], 72*beta*x['j']*x['w']
        Y0 = q0*x['v'] if mixed else 2*x['v']*q0**3
        R0 = -q0**3*(12*x['w']*x['C']-q0*x['z'])
        if mixed:
            k0 = R0+x['h']*X0*Y0
            expected_top = (2**64*3**14*x['s']**12*x['r']**24*x['c']**32
                            *q0**84*X0**40*Y0**52*R0**4*k0**12)
            jpower, power2, power3 = 216, 384, 282
        else:
            expected_top = (2**24*3**14*x['s']**12*x['r']**24*x['c']**32
                            *q0**4*x['h']**12*X0**52*Y0**64*R0**4)
            jpower, power2, power3 = 264, 456, 330
        require(final_top == expected_top, 'entire highest homogeneous form')
        exponents = {'j': jpower, 'w': 52, 'v': 64, 'h': 12,
                     'z': 4, 's': 12, 'r': 24, 'c': 32}
        key = ['p_beta']*jpower
        for variable, exponent in exponents.items(): key += ['v_'+variable]*exponent
        key = tuple(sorted(key))
        require(final_top.t.get(key) == 2**power2*3**power3,
                'authentic attained leading coefficient')
        require(sum(exponents.values()) == exact_degree, 'attained degree sum')
        certificate = {'omega_degree_upper_bound': omega_bound,
                       'bracket_competitor_bounds': competitors,
                       'bracket_degree': be_degree,
                       'correction_degree': correction_degree,
                       'highest_homogeneous_terms': len(final_top.t),
                       'attained_monomial': exponents,
                       'coefficient': {'power_of_2': power2, 'power_of_3': power3,
                                       'power_of_authentic_beta': jpower}}
    else:
        require(degree('b') > max(2*degree('Z'), degree('u'), degree('e')),
                'direct norm leading radicand')
        exact_degree = 4*degree('b')
        correction = degree('u')+degree('b')+degree('e')+2*degree('Z')
        require(correction < exact_degree, 'direct correction degree')
        require(all(s.startswith('v_') or s == 'p_beta'
                    for monomial in top('b').t for s in monomial),
                'unexpected coefficient dependency in direct top')
        final_top = top('b')**4
        jpower, power2, power3 = (224, 392, 288) if mixed else (256, 440, 320)
        exponents = {'j': jpower, 'w': 56, 'v': 56, 'z': 8,
                     's': 8, 'r': 40, 'c': 64}
        key = ['p_beta']*jpower
        for variable, exponent in exponents.items(): key += ['v_'+variable]*exponent
        require(final_top.t.get(tuple(sorted(key))) == 2**power2*3**power3,
                'direct authentic attained leading coefficient')
        require(sum(exponents.values()) == exact_degree, 'direct degree sum')
        certificate = {'highest_form': 'b_top**4', 'b_degree': degree('b'),
                       'correction_degree': correction,
                       'attained_monomial': exponents,
                       'coefficient': {'power_of_2': power2, 'power_of_3': power3,
                                       'power_of_authentic_beta': jpower}}
    require(exact_degree == packet['exact_degree'], 'attained output degree')
    certificate['exact_degree'] = exact_degree
    return certificate


def load_coefficients():
    binding = json.loads((ROOT/'coefficients/BINDING.json').read_text())
    require(binding['MF_convention'] == 'MF_native + beta, already shifted', 'MF convention')
    require(set(binding['payloads']) == set(PORTS), 'coefficient port set')
    values, receipts = {}, {}
    for name in PORTS:
        entry = binding['payloads'][name]
        require(entry['file'] == name+'.bin.gz', 'coefficient filename')
        raw = gzip.decompress((ROOT/'coefficients'/entry['file']).read_bytes())
        digest = hashlib.sha256(raw).hexdigest()
        require(digest == entry['raw_sha256'] == EXPECTED_HASHES[name],
                'authenticated payload '+name)
        number = int.from_bytes(raw, 'little')
        require(len(raw) == entry['raw_bytes'] and number.bit_length() == entry['bits'],
                'coefficient size '+name)
        require(raw and raw[-1], 'nonminimal numeral bytes')
        values[name] = number
        receipts[name] = {'bits': number.bit_length(), 'raw_sha256': digest}
    require(values['beta'] == (1 << 1064921)-1, 'beta recipe')
    require(values['cone_A'] == 1 << 1113, 'cone_A recipe')
    require(values['cone_B'] == 1 << 666104, 'cone_B recipe')
    return values, receipts


def evaluate(packet, inputs, ports, modulus):
    values = []
    for row in packet['nodes']:
        op = row[0]
        if op == 'variable': value = inputs[row[1]]
        elif op == 'coefficient': value = ports[row[1]]
        elif op == 'integer': value = row[1]
        else:
            a, b = values[row[1]], values[row[2]]
            value = a+b if op == 'add' else a-b if op == 'sub' else a*b
        values.append(value % modulus)
    return values


def modular_controls(packet, authentic):
    rng = random.Random(20261024)
    count = 0
    for modulus in (101, 1009, 65537, 1000003):
        ports = {k: v % modulus for k, v in authentic.items()}
        for trial in range(24):
            inputs = {k: rng.randrange(-20, 21) for k in VARIABLES}
            if trial < 4:
                inputs.update({'r': 0, 's': 0, 'c': 0, 'v': 0})
                inputs[('r', 's', 'c', 'v')[trial]] = 1
            actual = evaluate(packet, inputs, ports, modulus)
            expected = {}
            def emit(label, value): expected[label] = value % modulus
            symbolic_specification(emit, expected.__getitem__, inputs, ports,
                                   packet['chart'], packet['centered'])
            for label, value in expected.items():
                require(actual[packet['named_registers'][label]] == value,
                        'modular transcription '+label)
            count += 1
    return count


def small_arithmetic_controls():
    # These controls check boundaries and congruence transcription only.
    guard_cases = crt_cases = 0
    for q, F, C, k, eta in itertools.product((-14, -8, -2, 4, 10),
                                             range(-2, 3), range(-2, 3),
                                             range(-2, 3), range(-2, 3)):
        error = (8*F-q)**2+(16*C-q)**2
        budget = k*k*(q*q-error)-4*q*q*eta*eta
        require(budget % 4 == 0 and (3*budget-4) % 4 == 0, 'guard parity')
        guard_cases += 1
    for q, w, v, T, K in itertools.product((-10, -4, 2, 8), range(-1, 2),
                                           range(-1, 2), range(-1, 2), range(-2, 3)):
        X, Y = q*(12*w+4), q*v
        H, M = 4*(X+1)*Y+3, 2*q*q
        Dc = M*H
        zc = Dc*T+M*K+H*(v-q*q)
        require(math.gcd(M, H) == 1, 'CRT coprimality boundary')
        require((zc-H*(v-q*q)) % M == 0 and (zc-M*K) % H == 0,
                'CRT residues')
        ell = X*Y*Y
        require(ell*(ell+1) % 3 == 0, 'first radicand residue')
        crt_cases += 1
    return {'guard_divisibility_cases': guard_cases,
            'carrier_coprimality_and_residue_cases': crt_cases}


def mutation_controls(packet):
    rejected = []
    for register in ('I', 'Dg', 'S', 'b', 'e', 'output'):
        altered = copy.deepcopy(packet)
        index = altered['named_registers'][register]
        row = altered['nodes'][index]
        require(row[0] in ('add', 'sub', 'mul'), 'mutation target')
        row[0] = 'sub' if row[0] != 'sub' else 'add'
        try:
            check_local_identities(altered)
        except ValueError:
            rejected.append(register)
        else:
            raise ValueError('corruption accepted at '+register)
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path)
    args = parser.parse_args()
    authentic, coefficient_receipt = load_coefficients()
    result = {'checker': 'independent standard-library free-ring auditor',
              'scope': 'finite polynomial artifacts; unbounded proof remains ordinary mathematics',
              'coefficients': coefficient_receipt,
              'generic_identities': generic_norm_and_centering(),
              'bounded_controls': small_arithmetic_controls(), 'variants': []}
    for chart, centered in EXPECTED:
        filename = 'integer11_'+chart+('_centered' if centered else '_direct')+'.json'
        packet = json.loads((ROOT/filename).read_text())
        entry = {'file': filename, **validate_graph(packet)}
        entry['exact_local_register_identities'] = check_local_identities(packet)
        entry['degree_certificate'] = leading_forms(packet)
        entry['authentic_coefficient_modular_replays'] = modular_controls(packet, authentic)
        entry['rejected_corruptions'] = mutation_controls(packet)
        result['variants'].append(entry)
    result['passed'] = True
    text = json.dumps(result, indent=2)+'\n'
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(text)
    print(text)


if __name__ == '__main__':
    main()
