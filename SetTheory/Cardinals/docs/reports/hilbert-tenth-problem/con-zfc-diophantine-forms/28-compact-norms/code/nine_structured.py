#!/usr/bin/env python3
"""Structured-majorant and signed-divisor nine-variable specialization.

Derived from ProveIt package 18-jones9/nine/nine_compressor.py; the fixed
quartic/index construction is preserved, and only relation combining changes.

Standard-library only. The output is a finite binary +,-,* DAG; every nonliteral
constant has a bounded recipe in constants.json. It does not expand giant fixed
integers, solve the Diophantine equation, or certify the imported compiler.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
from hashlib import sha256
from itertools import product
import json
from math import comb, factorial
from pathlib import Path


def add(p, q):
    r = dict(p)
    for a, c in q.items():
        r[a] = r.get(a, 0) + c
        if not r[a]:
            del r[a]
    return r


def mul(p, q):
    r = defaultdict(int)
    for a, c in p.items():
        for b, d in q.items():
            r[tuple(x + y for x, y in zip(a, b))] += c * d
    return {a: c for a, c in r.items() if c}


def shift_term(a, c, n):
    """Substitute the first n coordinates by X+1; leave fixed ports alone."""
    active = [(i, e) for i, e in enumerate(a[:n]) if e]
    for chosen in product(*(range(e + 1) for _, e in active)):
        b = [0] * n + list(a[n:])
        d = c
        for (i, e), f in zip(active, chosen):
            b[i] = f
            d *= comb(e, f)
        yield tuple(b), d


def shift(p, n):
    r = defaultdict(int)
    for a, c in p.items():
        for b, d in shift_term(a, c, n):
            r[b] += d
    return {a: c for a, c in r.items() if c}


def build_parent(parent):
    n = len(parent['variables'])
    residuals = []
    shifted = []
    total = {}
    for eq in parent['equations']:
        r = {tuple(t['powers']): t['coefficient'] for t in eq['terms']}
        if any(sum(a[:n]) > 2 for a in r):
            raise ValueError('Parent contains a residual above degree two')
        rs = shift(r, n)
        residuals.append(r)
        shifted.append(rs)
        total = add(total, mul(rs, rs))
    grouped = defaultdict(dict)
    for a, c in total.items():
        grouped[(0,) + a[:n]][a[n:]] = c
    weighted = {}
    for a, poly in grouped.items():
        k0 = 4 - sum(a)
        if k0 < 0:
            raise ValueError('Parent sum of squares exceeds degree four')
        fac = factorial(k0)
        for e in a:
            fac *= factorial(e)
        weighted[a] = {p: fac * c for p, c in poly.items()}
    return residuals, shifted, total, dict(grouped), weighted


def sparse_records(poly):
    return [{'powers': list(a), 'coefficient': c}
            for a, c in sorted(poly.items())]


def polynomial_value(poly, values, modulus=None):
    out = 0
    for a, c in poly.items():
        term = c
        for v, e in zip(values, a):
            term *= pow(v, e, modulus) if modulus else v ** e
            if modulus:
                term %= modulus
        out += term
        if modulus:
            out %= modulus
    return out


def exponent_vector_compositions(length, total):
    if length == 0:
        if total == 0:
            yield ()
        return
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in exponent_vector_compositions(length - 1, total - first):
            yield (first,) + tail


def all_alphas(nu):
    for degree in range(5):
        yield from exponent_vector_compositions(nu + 1, degree)


def expo(a):
    return sum(e * 5 ** j for j, e in enumerate(a))


class DAG:
    """Hash-consed binary arithmetic DAG; no division or variable powers."""
    def __init__(self):
        self.nodes = []
        self.cache = {}
        self.pow_cache = {}
        self.known = {}
        self.names = {}

    def node(self, obj):
        key = json.dumps(obj, sort_keys=True, separators=(',', ':'))
        if key not in self.cache:
            self.cache[key] = len(self.nodes)
            self.nodes.append(obj)
        return self.cache[key]

    def const(self, value):
        i = self.node({'kind': 'literal', 'value': value})
        self.known[i] = value
        return i

    def fixed(self, name):
        return self.node({'kind': 'fixed', 'name': name})

    def var(self, name):
        return self.node({'kind': 'variable', 'name': name})

    def op(self, op, a, b):
        ka, kb = self.known.get(a), self.known.get(b)
        if ka is not None and kb is not None:
            return self.const({'add': lambda: ka + kb,
                               'sub': lambda: ka - kb,
                               'mul': lambda: ka * kb}[op]())
        if op == 'add':
            if ka == 0: return b
            if kb == 0: return a
        if op == 'sub' and kb == 0: return a
        if op == 'mul':
            if ka == 0 or kb == 0: return self.const(0)
            if ka == 1: return b
            if kb == 1: return a
        if op in ('add', 'mul') and a > b:
            a, b = b, a
        return self.node({'kind': op, 'left': a, 'right': b})

    def plus(self, *args):
        out = self.const(0)
        for a in args: out = self.op('add', out, a)
        return out

    def times(self, *args):
        out = self.const(1)
        for a in args: out = self.op('mul', out, a)
        return out

    def minus(self, a, b):
        return self.op('sub', a, b)

    def power(self, a, e):
        if not isinstance(e, int) or e < 0:
            raise ValueError('Only fixed nonnegative integer exponents')
        key = (a, e)
        if key in self.pow_cache: return self.pow_cache[key]
        if e == 0: out = self.const(1)
        elif e == 1: out = a
        else:
            half = self.power(a, e // 2)
            out = self.times(half, half)
            if e % 2: out = self.times(out, a)
        self.pow_cache[key] = out
        return out

    def geometric(self, a, e):
        """1+a+...+a^(e-1), using a finite O(log e) addition circuit."""
        if e == 0: return self.const(0)
        if e == 1: return self.const(1)
        half = e // 2
        val = self.times(self.geometric(a, half),
                         self.plus(self.const(1), self.power(a, half)))
        if e % 2: val = self.plus(val, self.power(a, 2 * half))
        return val

    def save(self, name, value):
        self.names[name] = value
        return value

    def prune(self, root):
        live, todo = set(), [root]
        while todo:
            i = todo.pop()
            if i in live: continue
            live.add(i)
            n = self.nodes[i]
            if n['kind'] in ('add', 'sub', 'mul'):
                todo += [n['left'], n['right']]
        remap = {old: new for new, old in enumerate(sorted(live))}
        nodes = []
        for old in sorted(live):
            n = dict(self.nodes[old])
            if n['kind'] in ('add', 'sub', 'mul'):
                n['left'], n['right'] = remap[n['left']], remap[n['right']]
            nodes.append(n)
        return nodes, remap[root], {k: remap[v] for k, v in self.names.items() if v in live}


def base_sum(dag, B, nu):
    """Sum_{|alpha|<=4} B^(L-expo(alpha)), with no division.

    It is B^(5^nu) h_4(B^(5^nu), B^(5^nu-1), ...,
    B^(5^nu-5^nu)); the first argument accounts for the slack exponent.
    """
    top = 5 ** nu
    weights = [dag.power(B, top)]
    weights += [dag.power(B, top - 5 ** j) for j in range(nu + 1)]
    hs = [dag.const(1)] + [dag.const(0)] * 4
    for t in weights:
        for degree in range(1, 5):
            hs[degree] = dag.plus(hs[degree], dag.times(t, hs[degree - 1]))
    return dag.times(dag.power(B, top), hs[4])


def make_body(nu, coefficient_keys, weights='majorant'):
    d = DAG()
    c = d.const
    A, M, S, P = d.plus, d.times, d.minus, d.power
    v = {name: d.var(name) for name in
         ['epsilon', 'g0', 'h0', 's0', 'w0', 'phi', 'i0', 'j0', 'n']}
    z, y = d.fixed('z_index'), d.fixed('y_index')
    b = d.save('b', A(y, c(1), v['epsilon']))
    g, h, s, w, ii, jj = (A(v[key], c(1)) for key in
                         ['g0', 'h0', 's0', 'w0', 'i0', 'j0'])
    B = d.save('B', P(b, 5))
    L = 5 ** (nu + 1)
    q = d.save('q', P(B, L))
    ell = d.save('ell', A(*(P(B, 5 ** j) for j in range(1, nu + 1))))
    lam = d.save('lambda', d.geometric(B, 4 * L))
    e = M(z, base_sum(d, B, nu))
    for a, name in coefficient_keys:
        e = A(e, M(d.fixed(name), P(B, L - expo(a))))
    e = d.save('e', e)
    theta = S(B, M(c(2), z))
    N = d.save('N', P(q, 16))
    Gcap = d.save('Gcap', M(c(32), b, P(B, 5 ** nu)))
    Rleft = A(g, M(e, P(q, 3)), M(ell, P(q, 5)),
              M(A(M(c(2), S(e, M(z, lam)), P(A(c(1), B, g), 4)),
                  M(lam, B), M(lam, B, P(q, 4))), P(q, 7)))
    Rright = A(S(P(q, 3), M(b, ell)), ell, M(theta, lam, P(q, 3)),
               M(S(B, c(2)), P(q, 8)))
    R = d.save('R', A(M(Rleft, S(P(N, 2), N)),
                       M(Rright, S(P(N, 2), c(1)))))
    U = d.save('U', M(P(N, 2), w))
    Y = d.save('Y', M(P(N, 2), s))
    MM = d.save('M', M(R, Y))
    PP = d.save('P', M(c(2), P(MM, 2), U))
    K = d.save('K', A(R, c(1), M(h, S(PP, c(1)))))
    AA = d.save('A', M(MM, A(U, c(1))))
    Bprime = A(M(c(2), R), c(1))
    Wsmall = d.save('Wsmall', M(b, w))
    CC = d.save('C', A(Bprime, Wsmall, v['phi']))
    JJ = d.save('J', S(M(c(4), AA), c(5)))
    QQ = d.save('Q', S(M(c(3), Wsmall, CC), M(c(2), S(P(Wsmall, 2), c(1)))))
    DD = d.save('D', A(M(S(P(AA, 2), c(1)), P(CC, 2)), c(1)))
    EE = d.save('E', M(ii, JJ, DD, P(CC, 2)))
    FF = d.save('F', A(M(S(P(AA, 2), c(1)), P(EE, 2)), c(1)))
    Gp = d.save('Gp', A(AA, M(FF, S(A(M(CC, DD), c(1)), AA))))
    HH = d.save('H', A(Bprime, M(jj, CC)))
    II = d.save('I', A(M(S(P(Gp, 2), c(1)), P(HH, 2)), c(1)))
    a0 = d.save('a0', A(M(S(P(PP, 2), c(1)), P(K, 2)), c(1)))
    a1 = d.save('a1', M(DD, FF, II))
    if weights == 'structured':
        divisor = d.save('divisor', M(JJ, FF))
        dividend = d.save('dividend', A(M(QQ, FF), M(JJ, S(HH, CC))))
        divbound = d.save('division_bound', A(P(QQ, 2), P(S(HH, CC), 2), c(1)))
    else:
        divisor = d.save('divisor', P(M(JJ, FF), 2))
        dividend = d.save('dividend', P(A(M(QQ, FF), M(JJ, S(HH, CC))), 2))
    margin = d.save('margin', S(S(M(P(K, 2), Gcap),
                               M(c(4), P(S(CC, M(K, Y)), 2), Gcap)),
                             M(c(8), g, P(K, 2))))
    if weights == 'literal':
        V0 = d.save('V0', A(P(a0, 2), c(2)))
        V1 = d.save('V1', A(P(a1, 2), c(2)))
    elif weights == 'structured':
        # A=R*Y*(U+1), C=2R+1+bw+phi. All eight outer variables are nonnegative.
        # These bounds use the unconditional R!=0 and |A|>=2 lemmas.
        r = d.save('r_positive', A(Wsmall, v['phi']))
        psmall = d.save('A_scale', M(Y, A(U, c(1))))
        MD = d.save('majorant_D', M(psmall, A(P(R, 2), P(CC, 2))))
        MF = d.save('majorant_F', A(M(AA, EE), c(1)))
        ch = d.save('majorant_CH', A(M(A(jj, c(2)), P(CC, 2)), P(r, 2)))
        MI = d.save('majorant_I', A(S(M(FF, A(M(DD, ch), M(c(2), P(HH, 2)),
                                                  P(AA, 2))), P(AA, 2)), c(1)))
        V0 = d.save('V0', A(M(PP, K), c(1)))
        V1 = d.save('V1', A(M(MD, MF, MI), c(1)))
    elif weights == 'majorant':
        V0 = d.save('V0', A(P(PP, 2), P(K, 2), c(2)))
        V1 = d.save('V1', A(M(A(P(AA, 2), P(CC, 2), c(1)),
                              A(P(AA, 2), P(EE, 2), c(1)),
                              A(P(Gp, 2), P(HH, 2), c(1))), c(1)))
    else:
        raise ValueError('Unknown weight choice')
    WW = d.save('W', M(divisor, S(M(c(2), margin), c(1))))
    if weights == 'structured':
        TT = d.save('T', S(A(M(divisor, A(v['n'], divbound)), dividend),
                           M(WW, A(M(c(2), divbound), M(V0, V1)))))
    else:
        TT = d.save('T', S(A(M(divisor, v['n']), dividend),
                           M(WW, A(dividend, M(V0, V1)))))
    output = d.save('output', S(P(S(P(TT, 2), M(P(WW, 2), A(a0, M(P(V0, 2), a1)))), 2),
                                  M(c(4), P(WW, 4), P(V0, 2), a0, a1)))
    nodes, root, names = d.prune(output)
    return {'nu': nu, 'L': L, 'weights': weights,
            'variables': list(v), 'nodes': nodes, 'output': root,
            'named_nodes': names,
            'operation_counts': {kind: sum(n['kind'] == kind for n in nodes)
                                 for kind in ['add', 'sub', 'mul']},
            'model': 'Binary +,-,*; squaring and fixed-coefficient multiplication charged; fixed integer recipes not evaluated.'}


def evaluate_dag(body, fixed, variables, modulus):
    vals = []
    for node in body['nodes']:
        k = node['kind']
        if k == 'literal': value = node['value']
        elif k == 'fixed': value = fixed[node['name']]
        elif k == 'variable': value = variables[node['name']]
        elif k == 'add': value = vals[node['left']] + vals[node['right']]
        elif k == 'sub': value = vals[node['left']] - vals[node['right']]
        elif k == 'mul': value = vals[node['left']] * vals[node['right']]
        else: raise ValueError(k)
        vals.append(value % modulus)
    return vals[body['output']], {name: vals[i] for name, i in body['named_nodes'].items()}


def direct_body_mod(nu, coeffs, z, y, variables, modulus, weights='majorant'):
    p = modulus
    eps, g0, h0, s0, w0, phi, i0, j0, n = variables
    g, h, s, w, i, j = g0+1, h0+1, s0+1, w0+1, i0+1, j0+1
    b = (y+1+eps) % p
    B = pow(b, 5, p)
    L = 5 ** (nu+1)
    q = pow(B, L, p)
    ell = sum(pow(B, 5**j, p) for j in range(1, nu+1)) % p
    # Used only for small nu in bounded tests.
    lam = sum(pow(B, j, p) for j in range(4*L)) % p
    e = sum((z+coeffs.get(a, 0))*pow(B, L-expo(a), p) for a in all_alphas(nu)) % p
    N = pow(q, 16, p)
    Gcap = 32*b*pow(B, 5**nu, p) % p
    theta = B-2*z
    R = ((g+e*q**3+ell*q**5+(2*(e-z*lam)*(1+B+g)**4+lam*B+lam*B*q**4)*q**7)*(N*N-N)
         +(q**3-b*ell+ell+theta*lam*q**3+(B-2)*q**8)*(N*N-1)) % p
    U, Y = N*N*w % p, N*N*s % p
    MM = R*Y % p
    PP = 2*MM*MM*U % p
    K = (R+1+h*(PP-1)) % p
    AA = MM*(U+1) % p
    Bp = (2*R+1) % p
    Ws = b*w % p
    CC = (Bp+Ws+phi) % p
    JJ = (4*AA-5) % p
    QQ = (3*Ws*CC-2*(Ws*Ws-1)) % p
    DD = ((AA*AA-1)*CC*CC+1) % p
    EE = i*JJ*DD*CC*CC % p
    FF = ((AA*AA-1)*EE*EE+1) % p
    Gp = (AA+FF*(CC*DD+1-AA)) % p
    HH = (Bp+j*CC) % p
    II = ((Gp*Gp-1)*HH*HH+1) % p
    a0, a1 = ((PP*PP-1)*K*K+1) % p, DD*FF*II % p
    div = (JJ*FF)**2 % p
    dvnd = (QQ*FF+JJ*(HH-CC))**2 % p
    marg = (K*K*Gcap-4*(CC-K*Y)**2*Gcap-8*g*K*K) % p
    if weights == 'structured':
        r = (Ws+phi) % p
        scale = Y*(U+1) % p
        md = scale*(R*R+CC*CC) % p
        mf = (AA*EE+1) % p
        ch = ((j+2)*CC*CC+r*r) % p
        mi = (FF*DD*ch+2*FF*HH*HH+(FF-1)*AA*AA+1) % p
        V0, V1 = (PP*K+1) % p, (md*mf*mi+1) % p
        div, dvnd = JJ*FF % p, (QQ*FF+JJ*(HH-CC)) % p
        bound = (QQ*QQ+(HH-CC)**2+1) % p
    elif weights == 'literal':
        V0, V1 = (a0*a0+2) % p, (a1*a1+2) % p
    else:
        V0 = (PP*PP+K*K+2) % p
        V1 = ((AA*AA+CC*CC+1)*(AA*AA+EE*EE+1)*(Gp*Gp+HH*HH+1)+1) % p
    WW = div*(2*marg-1) % p
    TT = ((div*(n+bound)+dvnd-WW*(2*bound+V0*V1)) if weights == 'structured'
          else (div*n+dvnd-WW*(dvnd+V0*V1))) % p
    return ((TT*TT-WW*WW*(a0+V0*V0*a1))**2-4*WW**4*V0*V0*a0*a1) % p


def write_json(path, obj):
    path.write_text(json.dumps(obj, sort_keys=True, separators=(',', ':'))+'\n')


def construct(parent_path, outdir):
    data = parent_path.read_bytes()
    parent = json.loads(data)
    residuals, shifted, total, grouped, weighted = build_parent(parent)
    nu = len(parent['variables'])
    rho = []
    s_bound = {(0,)*len(parent['constants']): 2}
    for residual in residuals:
        rp = defaultdict(int)
        for a, coefficient in residual.items():
            rp[a[nu:]] += abs(coefficient) * 2**sum(a[:nu])
        rho.append(dict(rp))
        s_bound = add(s_bound, {a: 24*v for a, v in mul(rp, rp).items()})
    coeffs = []
    keys = []
    for k, (a, cp) in enumerate(sorted(weighted.items())):
        name = f'c{k:04d}'
        keys.append((a, name))
        coeffs.append({'name': name, 'alpha': list(a), 'expo': expo(a),
                       'coefficient_polynomial_in_fixed_ports': sparse_records(cp)})
    constants = {'parent_sha256': sha256(data).hexdigest(),
                 'parent_file': parent_path.name, 'nu': nu,
                 'fixed_port_order': parent['constants'],
                 'port_binding': 'Use the complete fixed compiler tuple specified by the enclosing release; none of these are unknowns.',
                 'coefficient_records': coeffs,
                 'z_index': '2^s, with s given by index_bound_s.json = 2+24*sum(rho_j^2)',
                 'index_bound_proof': 'For nonnegative fixed compiler ports, rho_j bounds the coefficient l1 norm of r_j(n+1). Thus sum(abs(c_alpha)) <= 24*sum(rho_j^2) = s-2, and z=2^s > abs(c_alpha)+1.',
                 'y_index': 'sum((z_index+c_alpha)*(2*z_index)^(L-expo(alpha)) over alpha in N^(nu+1), sum(alpha)<=4; unlisted c_alpha=0)',
                 'u_index_unused_by_body': 'sum((2*z_index)^(5^j), j=1..nu)',
                 'L': 5**(nu+1),
                 'coefficient_multiplier': '(4-sum(alpha))! * product(alpha_j!)',
                 'dummy_input': 1,
                 'normalization': 'P(x,n)=sum_j r_j(n+1)^2; r_5(1,...,1)=1, so P(x,0)>=1 for every x.',
                 'bounded_sum_cardinality': comb(nu+5, 4)}
    outdir.mkdir(parents=True, exist_ok=True)
    write_json(outdir/'constants.json', constants)
    write_json(outdir/'index_bound_s.json',
               {'fixed_port_order': parent['constants'], 'terms': sparse_records(s_bound),
                'rho': [sparse_records(p) for p in rho],
                'formula': 's=2+24*sum(rho_j^2)',
                'requires': 'The four fixed compiler ports are nonnegative.'})
    write_json(outdir/'shifted_quartic.json',
               {'coordinate_order': ['n_'+x for x in parent['variables']]+parent['constants'],
                'terms': sparse_records(total), 'degree_in_unknowns': 4})
    counts = {}
    for weights in ['structured']:
        body = make_body(nu, keys, weights)
        write_json(outdir/f'nine_{weights}_dag.json', body)
        counts[weights] = {'nodes': len(body['nodes']),
                           'operations': body['operation_counts'],
                           'total_operations': sum(body['operation_counts'].values()),
                           'fixed_leaves': sum(x['kind']=='fixed' for x in body['nodes']),
                           'unknowns': body['variables']}
    return {'parent_residuals': len(residuals), 'parent_unknowns': nu,
            'shifted_symbolic_terms': len(total),
            'nonzero_weighted_coefficient_records': len(coeffs),
            'counts': counts}


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('parent', type=Path)
    ap.add_argument('output_directory', type=Path)
    args = ap.parse_args()
    print(json.dumps(construct(args.parent, args.output_directory), indent=2))

