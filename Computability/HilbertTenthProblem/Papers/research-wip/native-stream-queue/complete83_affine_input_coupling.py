#!/usr/bin/env python3
"""Fresh bounded evidence; all predecessors are authenticated inert bytes only."""
import argparse
import hashlib
import json
from pathlib import Path

PINS = {
 'complete83_independent_gamma_scout.py': 'b67ee981d5475a745094924d6ec3cbe72dfb38e3d28d9bd2c144ff0c2a59dc18',
 'complete83_independent_gamma_scout.json': 'ed570bc9e96d59e88ec6b6c1302ac177eb6704cfcd85fe39a3346798e89f5e20',
 'complete83_independent_gamma_scout.md': 'bdbcc3be5396bced89373da5ffb30f0f3f113f7e8e7ebe65e4f7b730264f1b41',
 'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf',
 'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
 'complete83_input_quotient_dichotomy.md': '46d6457d10d1847cd4241aa1ed6705bf520216fc32cf97891c1f439f6c2c2505',
 'complete83_input_witness_power_gap.md': '30a2b5eb4aa5dda7c08df01acd89fca3c4311b91f62e9df1f767341ed670f4f6',
 'complete84_exterior_auxiliary_absorption.md': '69f8e40bd44dca5bcb2f0f292a2ad842fff5a41b2014007f3f986176cd7bd8de',
 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
 'review_complete85_auxiliary_bezout_math.md': '77a4071be471db23642cabddc5bd4880debfa53441bf3640c3c45523e9bdb36d',
 'review_complete74_asymmetric_scale_math.md': 'a7f8d64389597c5a8fff93bad1f023dfc440d736bb9d77f2acd549e758aa0b58',
 '../../1980/FIXED_RAW_UNIVERSAL_76_PROOF.md': '75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87',
 '../../1980/FIXED_RAW_UNIVERSAL_78_PROOF.md': 'b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39',
}
# Literal dependency-free partition, checked against all 83 actual rows.
GROUPS = {
 'unit': 'norm_first norm_main norm_pair norm_index norm_transport'.split(),
 'first': 'tau_square R10b ksn2 first_root_base first_next first_product R10a hpm1'.split(),
 'main': 'cam2 D1 a4 a4m5 gam R14 L15 a_square A c2 Ac2'.split(),
 'outer': 'repunit q Lbig n2 wn2 sn2 UM R12 q_minus_F q_minus_FZ C_after_alpha scaled_t marked_rhs W odd_index index_difference gap_product gap Lm1 rproduct qMF mask_factor mask r_lhs kinner innerC transport_partial local_rhs'.split(),
}
FREE = 'Jrep F alpha transport_quotient h s w tau_root eta zeta Z sigma x Bm1 Kconstant twice_cell_bits inner_bits MC MF'.split()
EXCLUDED = {'delta', 'rho', 'i', 'f', 'auxiliary_quotient', 'y_aux'}

def require(ok, message):
    if not ok:
        raise ValueError(message)

def canonical(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':'), ensure_ascii=True)

def digest(b):
    return hashlib.sha256(b).hexdigest()

def pairs(items):
    out = {}
    for k, v in items:
        require(k not in out, 'duplicate JSON key')
        out[k] = v
    return out

def read_json(b):
    def bad(x):
        raise ValueError('noninteger JSON number: ' + x)
    return json.loads(b, object_pairs_hook=pairs, parse_float=bad, parse_constant=bad)

# Small independent sparse ring for the actual input cone and eliminant.
NAMES = 'alpha beta chi a Delta H u W delta rho kappa mu p q r'.split()
ZERO = (0,) * len(NAMES)

class Poly:
    def __init__(self, value=0):
        if isinstance(value, Poly):
            self.d = dict(value.d)
        elif isinstance(value, str):
            e = list(ZERO); e[NAMES.index(value)] = 1
            self.d = {tuple(e): 1}
        elif isinstance(value, dict):
            self.d = {m: c for m, c in value.items() if c}
        else:
            self.d = {ZERO: value} if value else {}
    def __add__(self, other):
        out = dict(self.d)
        for m, c in Poly(other).d.items():
            out[m] = out.get(m, 0) + c
        return Poly(out)
    __radd__ = __add__
    def __neg__(self):
        return Poly({m: -c for m, c in self.d.items()})
    def __sub__(self, other):
        return self + (-Poly(other))
    def __rsub__(self, other):
        return Poly(other) - self
    def __mul__(self, other):
        out = {}
        for m, c in self.d.items():
            for n, d in Poly(other).d.items():
                e = tuple(a+b for a, b in zip(m, n))
                out[e] = out.get(e, 0) + c*d
        return Poly(out)
    __rmul__ = __mul__
    def square(self):
        return self * self
    def __eq__(self, other):
        return self.d == Poly(other).d
    def record(self):
        return [[list(m), c] for m, c in sorted(self.d.items())]

def ceil_log2(n):
    require(type(n) is int and n > 0, 'positive integer log argument')
    return (n-1).bit_length()

def pell(A, n):
    # Pair multiplication, separate from the recurrence used for cross-checking.
    D = A*A-1
    out = (1, 0); base = (A, 1)
    while n:
        if n & 1:
            x, y = out; z, w = base
            out = (x*z+D*y*w, x*w+y*z)
        x, y = base
        base = (x*x+D*y*y, 2*x*y)
        n //= 2
    return out

def audit(root):
    blobs = {}
    for name, expected in PINS.items():
        b = (root / name).read_bytes()
        require(digest(b) == expected, 'pin: ' + name)
        blobs[name] = b
    p = read_json(blobs['complete83_independent_gamma_scout.json'])['packet']
    parent = read_json(blobs['complete84_scaled_strong_output.json'])
    require('packet' in parent, 'parent packet')
    parent = parent['packet']
    saved = canonical(p)
    rebuilt = []
    for row in parent['source']:
        if row[0] == 'gamma_sum':
            require(row == ['gamma_sum', '+', 'rho', 'sigma'], 'deleted addition')
        else:
            rebuilt.append([row[0], row[1]] + ['sigma' if x == 'gamma_sum' else x for x in row[2:]])
    require(rebuilt == p['source'], 'literal complete83 pullback')
    seen = set(p['free']); defs = {}; dep = {x: {x} for x in p['free']}
    ledger = {'M': 0, 'A': 0}
    for name, op, a, b in p['source']:
        require(name not in seen and op in ('+', '-', '*'), 'unique source target/op')
        require(all(type(x) is int or x in seen for x in (a, b)), 'source topology')
        seen.add(name); defs[name] = [op, a, b]
        dep[name] = set().union(*(dep[x] for x in (a,b) if isinstance(x,str)))
        ledger['M' if op == '*' else 'A'] += 1
    live = {p['output']}; todo = list(live)
    while todo:
        name = todo.pop()
        if name in defs:
            for x in defs[name][1:]:
                if isinstance(x, str) and x not in live:
                    live.add(x); todo.append(x)
    require(live == seen, 'all complete source rows and free ports live')
    require(ledger == {'M': 47, 'A': 36}, '83 ledger')
    exterior = [r[0] for r in p['source'] if not dep[r[0]] & EXCLUDED]
    claimed = sum(GROUPS.values(), [])
    require(len(claimed) == len(set(claimed)) == 52, 'partition size')
    require(set(exterior) == set(claimed), 'complete 52-row partition')
    require([x for x in p['free'] if x not in EXCLUDED] == FREE, '19 free ports')
    for name in p['factors']:
        if name != 'norm_input':
            require(not dep[name] & {'delta', 'rho'}, 'input witnesses private to input factor')
    # Bind all ten actual input rows, with only genuine exterior cuts.
    env = {'A': Poly('Delta'), 'R12': Poly('a'), 'a4m5': Poly('H'),
           'odd_index': Poly('u'), 'W': Poly('W'),
           'delta': Poly('delta'), 'rho': Poly('rho')}
    input_rows = []
    for row in p['source']:
        if row[0] in ['index_product','index_rhs','difference_multiple','exponent_partial',
                      'modulus_multiple','exponent_rhs','mu2','kappa2','scaled_kappa2','norm_input']:
            name, op, a, b = row
            v, w = env[a], env[b]
            env[name] = v+w if op == '+' else v-w if op == '-' else v*w
            input_rows.append(row)
    al, be, ch, a, D, H, u, W, delta, rho = (Poly(x) for x in NAMES[:10])
    kap = u+D*delta; mu = W+a*kap+H*rho
    require(env['index_rhs'] == kap and env['exponent_rhs'] == mu, 'literal roots')
    require(env['norm_input'] == mu.square()-D*kap.square(), 'literal input norm')
    pp = al*H-a*D*be; qq = D*be; rr = al*H*u+be*D*W+ch*H*D
    require(pp*kap+qq*mu-rr == H*D*(al*delta+be*rho-ch), 'exact affine input translation')
    k, m, pp0, qq0, rr0 = (Poly(x) for x in ['kappa','mu','p','q','r'])
    line = pp0*k+qq0*m-rr0
    quad = (pp0.square()-D*qq0.square())*k.square()-2*pp0*rr0*k+rr0.square()-qq0.square()
    require(quad == line.square()-2*qq0*m*line+qq0.square()*(m.square()-D*k.square()-1), 'eliminant identity')
    require(canonical(p) == saved, 'parent data immutable')
    recurrence_checks = 0
    for A in (2,4,8,16):
        x,y = 1,0
        for n in range(25):
            require(pell(A,n) == (x,y), 'independent Pell multiplication')
            x,y = A*x+(A*A-1)*y, x+A*y
            recurrence_checks += 1
    components = []
    for A in (4,8,16):
        D = A*A-1; a = A-2; H = 4*a+3; u = 3
        for v in (u,A*u,u+2*D,A*u+2*D):
            mu,kap = pell(A,v)
            E = mu-a*kap; W = E % H
            if 2*W > H:
                W -= H
            require((kap-u) % D == 0 and (E-W) % H == 0, 'component integrality')
            delta=(kap-u)//D; rho=(E-W)//H
            require(delta>0 and rho>0 and mu*mu-D*kap*kap==1, 'positive component')
            for al,be in ((1,0),(0,1),(1,1),(1,-1),(2,-3),(-2,3)):
                ch=al*delta+be*rho
                pp=al*H-a*D*be; qq=D*be; rr=al*H*u+be*D*W+ch*H*D
                leader=pp*pp-D*qq*qq
                require(leader != 0, 'nonzero integer leader')
                require(leader*kap*kap-2*pp*rr*kap+rr*rr-qq*qq==0, 'component eliminant')
                height=1+2*abs(pp*rr)+abs(rr*rr-qq*qq)
                require(kap<=height, 'integral Cauchy bound')
                components.append({'A': A, 'v': v, 'alpha': al, 'beta': be,
                    'chi_bits': abs(ch).bit_length(), 'kappa_bits': kap.bit_length(),
                    'kappa_sha256': digest(str(kap).encode()), 'W': W})
    cutoff_checks=0
    for t in range(13):
        for L in (1,2,3,7,16,101):
            bound=8*t+4+ceil_log2(23*L*L)
            for c in (2,3,5):
                require(c**(bound-8*t-4)>=23*L*L, 'cutoff contradiction')
                cutoff_checks += 1
    for R in range(7,257):
        require(3*(2**R+1)//R>=R*R, 'finite growth corroboration')
    return {'status': 'PASS', 'source_sha256': digest(Path(__file__).read_bytes()),
        'pins': PINS, 'unchanged_packet_sha256': digest(saved.encode()),
        'literal_source_rows': len(p['source']), 'ledger': ledger,
        'all_rows_and_free_ports_live': True, 'data_immutable': True,
        'excluded_supplied': sorted(EXCLUDED), 'exterior_groups': GROUPS,
        'exterior_computed': exterior, 'exterior_free': FREE, 'exterior_total': 71,
        'input_rows': input_rows, 'input_norm_terms': env['norm_input'].record(),
        'affine_translation_verified': True, 'eliminant_terms': quad.record(),
        'recurrence_checks': recurrence_checks, 'component_line_checks': len(components),
        'components': components, 'cutoff_checks': cutoff_checks, 'growth_checks': 250,
        'scope': 'No new circuit; components are not compiler histories or full zeros; universal inequalities are proved in the companion.'}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--root', type=Path, required=True)
    group=ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--output',type=Path); group.add_argument('--expect',type=Path)
    args=ap.parse_args(); result=audit(args.root.resolve())
    if args.output:
        with args.output.open('x') as f:
            json.dump(result,f,indent=2,sort_keys=True); f.write('\n')
    else:
        require(canonical(result)==canonical(read_json(args.expect.read_bytes())), 'exact receipt')
    print('PASS: 83 rows; 71 bounded ports; exact Pell-line elimination; 72 diagnostic lines.')

if __name__ == '__main__':
    main()
