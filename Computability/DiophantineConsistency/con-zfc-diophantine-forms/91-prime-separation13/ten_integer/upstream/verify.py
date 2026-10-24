#!/usr/bin/env python3
"""Independent exact algebra, literal-circuit, degree, and coefficient audit.

Only Python's standard library is required. Explicit checks survive -O.
This does not test consistency or replace the cited unbounded source proof.
"""
from pathlib import Path
import gzip, hashlib, json, math, random

ROOT = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise ValueError(message)


class Poly:
    """Exact sparse Z[h,B,C,xi,y]; independent of the circuit builder."""
    zero = (0, 0, 0, 0, 0)

    def __init__(self, terms=None):
        self.d = {k: int(v) for k, v in (terms or {}).items() if v}

    @classmethod
    def lift(cls, v):
        return v if isinstance(v, cls) else cls({cls.zero: v})

    @classmethod
    def var(cls, i):
        e = [0] * 5
        e[i] = 1
        return cls({tuple(e): 1})

    def __add__(self, other):
        out = dict(self.d)
        for k, v in self.lift(other).d.items():
            out[k] = out.get(k, 0) + v
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({k: -v for k, v in self.d.items()})

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) + -self

    def __mul__(self, other):
        out = {}
        for a, x in self.d.items():
            for b, y in self.lift(other).d.items():
                e = tuple(i + j for i, j in zip(a, b))
                out[e] = out.get(e, 0) + x * y
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, n):
        need(type(n) is int and n >= 0, 'fixed nonnegative exponent')
        out, base = Poly.lift(1), self
        while n:
            if n & 1:
                out = out * base
            base = base * base
            n //= 2
        return out

    def __eq__(self, other):
        return self.d == self.lift(other).d

    def weighted_degree(self, weights):
        return max((sum(a * b for a, b in zip(e, weights)) for e in self.d), default=-1)


def decode(packet):
    return Poly({tuple(t['powers']): t['coefficient'] for t in packet})


def algebra():
    h, B, C, xi, y = [Poly.var(i) for i in range(5)]
    A, u = 2 * h, C * C
    D = (A * A - 4) * u + 4
    E0, E = u * xi, u * D * xi
    F = 4 * (A * A - 4) * u * u * D * xi * xi + 1
    G = (h - 1) * (F - 1) - 1
    H = C + F * (B - C + 16 * E * y)
    a1 = D * F * ((G * G - 1) * H * H + 1)
    P0 = 2 * A * E
    P1 = 2 * A * E0 * (D - 2 * u)
    delta0 = D - 16 * E * E
    delta1 = D + 16 * E0 * E0 * (u * (3 * u - 4) * A * A - 16 * (u - 1) ** 2)
    need(D * F - P0 * P0 == delta0, 'first radical-core identity')
    need(D * F - P1 * P1 == delta1, 'second radical-core identity')
    J = B - C
    T = xi * J * (u * (2 * h * h - 11) + 6)
    T += 16 * u * xi * xi * y * (u * u * (8 * h ** 4 - 52 * h * h + 143) + u * (32 * h * h - 176) + 48) + 3 * y
    R6 = 32768 * u ** 7 * xi ** 4 * h ** 9 * ((h - 1) * T - 2 * y)
    roots = {'linear': P0 * G * H, 'cubic': P1 * G * H, 'sixterm': R6}
    cert = json.loads((ROOT / 'ROOT_CERTIFICATES.json').read_text())
    weights = [16384, 7942, 1, 2, 1]
    need(decode(cert['center6']['R']) == R6, 'six-term root coefficient certificate')
    need(decode(cert['center6']['defect']) == a1 - R6 * R6, 'complete six-term defect certificate')
    expected_defects = {'linear': 426050, 'cubic': 393282, 'sixterm': 368449}
    data = {}
    for variant, R in roots.items():
        defect = a1 - R * R
        dr, de = R.weighted_degree(weights), defect.weighted_degree(weights)
        need(dr == 229409 and de == expected_defects[variant], 'weighted degree ' + variant)
        ds, dz, da0, da1 = 81922, 81925, 294619, 458818
        dinner = max(2 * dz, ds + dr + dz, 2 * ds + da0, 2 * ds + de)
        bound = max(2 * dinner, 4 * ds + da0 + da1)
        data[variant] = {'degree_root': dr, 'degree_defect': de,
                         'final_degree_bound': bound, 'defect_terms': len(defect.d)}
    return data


def fixed_values():
    manifest = json.loads((ROOT / 'FIXED_COEFFICIENTS.json').read_text())
    out = {}
    for name, item in manifest.items():
        raw_gz = (ROOT / item['file']).read_bytes()
        raw = gzip.decompress(raw_gz)
        need(hashlib.sha256(raw_gz).hexdigest() == item['gzip_sha256'], 'compressed payload ' + name)
        need(hashlib.sha256(raw).hexdigest() == item['raw_sha256'], 'coefficient payload ' + name)
        need(raw[0] in (0, 1), 'sign encoding')
        out[name] = (-1 if raw[0] else 1) * int.from_bytes(raw[1:], 'little')
    old = json.loads((ROOT / 'upstream/integer10.json').read_text())
    ports = [int.from_bytes(gzip.decompress((ROOT / 'data' / (name + '.bin.gz')).read_bytes()), 'little')
             for name in ('beta', 'K', 'MC', 'MF_source')]
    for name, terms in old['fixed_recipes'].items():
        val = sum(t['coefficient'] * math.prod(p ** e for p, e in zip(ports, t['powers'])) for t in terms)
        need(out[name] == val, 'derived fixed integer ' + name)
    need(out['radix'] == 2 ** 2134940 and out['threshold'] == 2 ** 34159017, 'radix and threshold')
    return out


def eval_dag(body, inputs, fixed, modulus):
    vals = []
    for i, n in enumerate(body['nodes']):
        k = n['kind']
        if k == 'variable':
            v = inputs[n['name']]
        elif k == 'literal':
            v = n['value']
        elif k == 'fixed':
            v = fixed[n['name']]
        else:
            need(0 <= n['left'] < i and 0 <= n['right'] < i, 'DAG topology')
            a, b = vals[n['left']], vals[n['right']]
            v = a + b if k == 'add' else a - b if k == 'sub' else a * b
        vals.append(v % modulus)
    return vals


def digests(body, m_replacement=None):
    """Exact syntactic identity modulo commutativity, using SHA256 labels.

    This is an integrity/transcription certificate, alongside the mathematical
    identities; the universal polynomial proof is in the manuscript.
    """
    out = []
    for n in body['nodes']:
        k = n['kind']
        if k == 'variable' and n['name'] == 'm' and m_replacement is not None:
            out.append(m_replacement)
            continue
        if k in ('add', 'mul', 'sub'):
            a, b = out[n['left']], out[n['right']]
            if k != 'sub':
                a, b = sorted((a, b))
            obj = [k, a, b]
        else:
            obj = [k, n.get('name', n.get('value'))]
        out.append(hashlib.sha256(json.dumps(obj, separators=(',', ':')).encode()).hexdigest())
    return out


def degree_leaders(body, fixed, prime):
    degrees, heads = [], []
    for n in body['nodes']:
        k = n['kind']
        if k == 'variable':
            deg, coeff = 1, 1
        elif k in ('literal', 'fixed'):
            deg, coeff = 0, n['value'] if k == 'literal' else fixed[n['name']]
        else:
            i, j = n['left'], n['right']
            if k == 'mul':
                deg, coeff = degrees[i] + degrees[j], heads[i] * heads[j]
            else:
                deg = max(degrees[i], degrees[j])
                a = heads[i] if degrees[i] == deg else 0
                b = heads[j] if degrees[j] == deg else 0
                coeff = a + b if k == 'add' else a - b
        degrees.append(deg)
        heads.append(coeff % prime)
    return degrees, heads


def main():
    exact = algebra()
    fixed = fixed_values()
    old = json.loads((ROOT / 'upstream/integer10.json').read_text())
    need(old['total_operations'] == 480, 'pinned predecessor count')
    expected = {'linear': (1179788, 484), 'cubic': (1114252, 487), 'sixterm': (1081125, 521)}
    rng = random.Random(20261023)
    for variant, (degree, count) in expected.items():
        body = json.loads((ROOT / ('integer10_' + variant + '.json')).read_text())
        need(len(body['variables']) == 10 and body['domain'] == 'Z', 'ten unrestricted integers')
        ops = sum(n['kind'] in ('add', 'sub', 'mul') for n in body['nodes'])
        need(ops == count == body['total_operations'], 'live operation count')
        need(exact[variant]['final_degree_bound'] == degree == body['exact_degree'], 'degree certificate')
        seen, todo = set(), [body['output']]
        while todo:
            i = todo.pop()
            if i in seen:
                continue
            seen.add(i)
            n = body['nodes'][i]
            if 'left' in n:
                todo.extend((n['left'], n['right']))
        need(len(seen) == len(body['nodes']), 'no dead nodes')
        dh = digests(body)
        shifted = dh[body['named_nodes']['shifted_m']]
        oldh = digests(old, shifted)
        need(dh[body['output']] == oldh[old['output']], 'exact syntactic shear identity')
        cases, leaders = 0, {}
        for p in (1000003, 1000033, 1000037):
            dg, lc = degree_leaders(old, fixed, p)
            lead = {k: lc[i] for k, i in old['named_nodes'].items()}
            required_degrees = {'halfA': 16384, 'A': 16384, 'B1': 7942,
                'C': 1, 'xi': 2, 'Sigma': 81922, 'Theta': 81925,
                'guard': 294619, 'lucas': 458818, 'E': 32774,
                'G': 81930, 'H': 98321}
            for name, expected_degree in required_degrees.items():
                need(dg[old['named_nodes'][name]] == expected_degree,
                     'literal-prefix degree ' + name)
                need(lead[name] != 0, 'literal-prefix attained degree ' + name)
            if variant == 'linear':
                defect_lead = -16 * lead['E'] ** 2 * lead['G'] ** 2 * lead['H'] ** 2
                final_lead = lead['Sigma'] ** 4 * defect_lead ** 2
            elif variant == 'cubic':
                core_lead = 48 * lead['C'] ** 8 * lead['xi'] ** 2 * lead['A'] ** 2
                defect_lead = core_lead * lead['G'] ** 2 * lead['H'] ** 2
                final_lead = lead['Sigma'] ** 4 * defect_lead ** 2
            else:
                final_lead = -4 * lead['Sigma'] ** 4 * lead['guard'] * lead['lucas']
            leaders[str(p)] = final_lead % p
            need(leaders[str(p)] != 0, 'attained degree over actual fixed integers')
            for trial in range(40):
                inputs = {n: rng.randrange(-50, 51) for n in body['variables']}
                got = eval_dag(body, inputs, fixed, p)
                shifted_inputs = dict(inputs)
                shifted_inputs['m'] += got[body['named_nodes']['shear']]
                previous = eval_dag(old, shifted_inputs, fixed, p)
                need(got[body['output']] == previous[old['output']], 'signed modular shear evaluation')
                cases += 1
        exact[variant].update(exact_degree=degree, live_binary_operations=ops,
                              leading_coefficients_mod_primes=leaders, signed_modular_cases=cases,
                              syntactic_shear_identity=True)
    result = {'status': 'PASS', 'variants': exact, 'fixed_integer_payloads_verified': len(fixed),
              'scope': 'Exact sparse algebra, fixed data, symbolic shear transcription, total-degree bounds and nonzero leading certificates; inherited semantic calibration is not re-proved by finite tests.'}
    (ROOT / 'VERIFICATION.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
