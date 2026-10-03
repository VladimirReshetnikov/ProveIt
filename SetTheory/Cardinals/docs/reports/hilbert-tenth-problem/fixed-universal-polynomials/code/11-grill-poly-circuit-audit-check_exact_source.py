# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Independent exact row/motif audit. Never imports or executes producer/upstream code.
Source schedules are checked one row at a time; large coefficients are exact Python
integers, not probabilistic hashes. Only pinned JSON, binary table, and DAG are data.
"""
import hashlib, json, mmap, struct, sys
from array import array
from collections import Counter
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PROD = ROOT.parent / 'arithmetic'
LIT = ROOT.parent / 'input-research/literal/literal_tables.json'
BASE = 1 << 50
ROW = struct.Struct('<Bqq')

def need(ok, msg):
    if not ok:
        raise ValueError(msg)

def readj(path):
    return json.loads(path.read_bytes())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def exact_type(x):
    return type(x) is int

def pinned_data():
    entries = readj(ROOT.parent / 'PROVENANCE.json')['sources']
    bysource = {e['source']: e for e in entries}
    pins = readj(ROOT / 'pins.json')
    for p, d in pins.items():
        key = p.removeprefix('source://')
        e = bysource[key]
        need(e['original_sha256'] == d['sha256'] and e['original_bytes'] == d['bytes'], 'original dependency pin ' + key)
        path = ROOT.parent / 'frozen-copy' / e['delivered'].removeprefix('frozen/')
        need(sha(path) == e['delivered_sha256'], 'delivered dependency ' + key)
    cp = readj(ROOT / 'source_connector_pins.json')
    for name, d in cp.items():
        e = bysource['circuit-audit/sources/' + name]
        need(e['original_git_blob_sha1'] == d['sha'], 'original Git blob pin ' + name)
        path = ROOT.parent / 'frozen-copy' / e['delivered'].removeprefix('frozen/')
        need(sha(path) == e['delivered_sha256'], 'delivered Git source ' + name)
    return (len(pins), len(cp))

class C:
    __slots__ = ('v',)

    def __init__(self, v):
        need(exact_type(v), 'exact constant')
        self.v = v

def exact_constants(rows):
    out = []
    for i, r in enumerate(rows):
        op = r[0]
        if op == 'int':
            need(len(r) == 2 and type(r[1]) is str, 'integer recipe')
            v = int(r[1])
        elif op in ('pow2', 'geom4'):
            need(len(r) == 2 and exact_type(r[1]) and (0 <= r[1] < 1000000), 'fixed recipe exponent')
            v = 1 << r[1] if op == 'pow2' else sum_pow4(r[1])
        else:
            need(op in ('add', 'sub', 'mul') and len(r) == 3, 'recipe opcode')
            need(all((exact_type(h) and h < 0 and (-h <= i) for h in r[1:])), 'constant-only topological recipe')
            a, b = (out[-h - 1] for h in r[1:])
            v = a + b if op == 'add' else a - b if op == 'sub' else a * b
        out.append(v)
    return out

def sum_pow4(n):
    numerator = (1 << 2 * n) - 1
    q, r = divmod(numerator, 3)
    need(r == 0, 'geometric divisibility')
    return q

class Audit:

    def __init__(self, m, mm):
        self.m = m
        self.mm = mm
        self.at = 0
        self.count = [0, 0, 0]
        self.cs = exact_constants(m['constants'])
        self.inputs = {}
        cursor = 0
        self.input_count = Counter()
        for d in m['inputs']:
            need(d['name'] not in self.inputs and d['start'] == cursor and (d['count'] > 0), 'input partition')
            need(d['domain'] == 'positive_integer' and d['role'] in ('witness', 'external'), 'input domain')
            external_names = {'x', 'a_e', 'p_e', 's_e', 'C_e', 'L_e'}
            need(d['role'] == ('external' if d['name'] in external_names else 'witness'), 'specific coordinate role ' + d['name'])
            self.inputs[d['name']] = range(BASE + cursor, BASE + cursor + d['count'])
            self.input_count[d['role']] += d['count']
            cursor += d['count']
        need(cursor == m['input_count'], 'input total')
        need(m['input_base'] == BASE and m['row_bytes'] == 17 and (m['row_struct'] == '<Bqq'), 'declared source format')
        need(m['constant_count'] == len(self.cs), 'constant census')
        extra = m['extra']
        need(extra['program_parameters_are_existential'] is False, 'program parameter quantifiers')
        need([p['name'] for p in extra['program_parameters']] == ['a_e', 'p_e', 's_e', 'C_e', 'L_e'], 'program parameter names')
        for p in extra['program_parameters']:
            need(p['fixed_for_represented_set'] is True and p['domain'] == 'positive_integer' and (p['ref'] == self.inputs[p['name']][0]), 'program parameter scope')
        self.used_names = set()
        self.motifs = []

    def inp(self, n, count=1):
        r = self.inputs[n]
        need(len(r) == count, 'input family arity ' + n)
        self.used_names.add(n)
        return r[0] if count == 1 else r

    def getrow(self, n):
        return ROW.unpack_from(self.mm, 8 + 17 * n)

    def equivalent(self, expect, actual):
        return actual < 0 and self.cs[-actual - 1] == expect.v if isinstance(expect, C) else expect == actual

    def ref(self, x):
        if isinstance(x, C):
            return [i for i, v in enumerate(self.cs) if v == x.v]
        return x

    def op(self, o, a, b):
        if isinstance(a, C) and isinstance(b, C):
            return C(a.v + b.v if o == 0 else a.v - b.v if o == 1 else a.v * b.v)
        if o == 0:
            if isinstance(a, C) and a.v == 0:
                return b
            if isinstance(b, C) and b.v == 0:
                return a
        if o == 1:
            if isinstance(b, C) and b.v == 0:
                return a
            if not isinstance(a, C) and (not isinstance(b, C)) and (a == b):
                return C(0)
        if o == 2:
            if isinstance(a, C) and a.v == 0 or (isinstance(b, C) and b.v == 0):
                return C(0)
            if isinstance(a, C) and a.v == 1:
                return b
            if isinstance(b, C) and b.v == 1:
                return a
        need(self.at < self.m['ledger']['operations'], 'source exhausted')
        row = self.getrow(self.at)
        need(row[0] == o and self.equivalent(a, row[1]) and self.equivalent(b, row[2]), f'exact motif mismatch row {self.at}: opcode {o}, got {row}')
        self.count[o] += 1
        self.at += 1
        return self.at - 1

    def add(self, a, b):
        return self.op(0, a, b)

    def sub(self, a, b):
        return self.op(1, a, b)

    def mul(self, a, b):
        return self.op(2, a, b)

    def total(self, seq):
        out = C(0)
        for h in seq:
            out = self.add(out, h)
        return out

    def block(self, label, start):
        self.motifs.append({'name': label, 'start': start, 'end': self.at, 'rows': self.at - start})

    def binary_power(self, base, n):
        v = base
        for bit in format(n, 'b')[1:]:
            v = self.mul(v, v)
            if bit == '1':
                v = self.mul(v, base)
        return v

def table_audit(literal, raw):
    alphabet = literal['genera']['alphabet']
    N = len(alphabet)
    a = 28 * (N + 1)
    need(N == 1013 and literal['genera']['modulus'] == 2, 'source alphabet/modulus')
    need([v['id'] for v in alphabet] == list(range(N)), 'literal IDs')
    need(len(raw) == 14 * a, 'run count')
    H = literal['genera']['halt_symbol']
    need(H == 1012, 'H')
    for t, got in enumerate(raw):
        phase = t // (7 * a)
        z = t % (7 * a)
        expected = 0
        hit = 0
        for off in (17, a + 13):
            w = z - off
            if w >= 0:
                y, r = divmod(w, 28)
                if y < N and r in (0, 2, 4):
                    expected = (a - 3, 7, a - 4)[r // 2]
                    hit += 1
        w = z - (2 * a + 3)
        if w >= 0:
            y, r = divmod(w, 14)
            if y < N and y != H and (r % 2 == 0) and (r <= 12):
                u, v = alphabet[y]['productions'][phase]
                ext = lambda j: 3 * a // 2 if j == H else 7 * a * (1 - alphabet[j]['width'])
                expected = (14 * u + 7, 3, 3 * a - 14 * u - 10 + ext(u), 0, 14 * v + 7, 3, 3 * a - 14 * v - 10 + ext(v))[r // 2]
                hit += 1
        need(hit <= 1 and got == expected, 'literal run table phase ' + str(t))
    return a

def recoder(A, packet, k, ns, x, z):
    start = A.at
    env = {n: A.inp(ns + '__' + n) for n in packet['auxiliaries']}
    env.update(x=x, z=z)
    need(len(packet['auxiliaries']) == 49 and len(packet['comparisons']) == 34, 'recoder arity')
    need(packet['source'][:3] == [['q2', '*', 'q', 'q'], ['Q', '*', 'q2', 'q2'], ['B', '*', 8, 'Q']], 'old recoder prefix')
    need(not any(('q2' in row[2:] for row in packet['source'][3:])), 'private power temporary')
    env['Q'] = A.binary_power(env['q'], k)
    env['B'] = A.mul(C(1 << k - 1), env['Q'])
    for n, o, a, b in packet['source'][3:]:
        need(n not in env, 'recoder SSA')
        operand = lambda v: C(v) if exact_type(v) else env[v]
        env[n] = A.op('+-*'.index(o), operand(a), operand(b))
    A.block(ns, start)
    return (env, [(env[a], env[b]) for a, b in packet['comparisons']])

def pair_value(literal, a):
    g = literal['genera']
    ids = g['canonical_symbols']['0']
    need((ids['b'], ids['x']) == (300, 539), 'input source pair')

    def E(y):
        need(g['alphabet'][y]['width'] == 1, 'original input width')
        grill = lambda r: '0' + '10' * r
        return '0' * (14 * y + 7) + grill(a - 3) + grill(7) + grill(a - 4) + '0' * (3 * a - 14 * y - 10)
    bits = E(ids['b']) + E(ids['x'])
    need(len(bits) == 14 * a, 'exact pair length')
    v = int(bits[::-1], 2)
    need(0 < 3 * v < 1 << len(bits), 'literal strong cone')
    return (v, len(bits))

def loaders(A, literal, a):
    packet = readj(PROD / 'input_recoder130_receipt.json')['certificate']
    ext = {n: A.inp(n) for n in ('x', 'a_e', 'p_e', 's_e', 'C_e', 'L_e')}
    one = C(1)
    u = A.add(ext['x'], one)
    R = A.inp('canonical_input_bits__spread')
    c, res = recoder(A, packet, 32, 'canonical_input_bits', u, R)
    beta = A.inp('input_loader__canonical_beta')
    res.append((A.add(c['input_slack'], beta), A.add(u, one)))
    N = A.inp('input_loader__N')
    m = C((1 << 32) - 1)
    lhs = A.mul(m, N)
    t0 = A.mul(m, ext['a_e'])
    t1 = A.mul(A.mul(ext['p_e'], C(3941247658)), c['modulus'])
    t2 = A.mul(A.mul(ext['p_e'], C(((1 << 32) - 1) * -4194240)), R)
    t3 = A.mul(A.mul(A.mul(ext['p_e'], m), ext['s_e']), c['Q'])
    res.append((lhs, A.total([t0, t1, t2, t3])))
    V, k = pair_value(literal, a)
    e, pairs = recoder(A, packet, k, 'unrestricted_tape_exponent', one, one)
    res += pairs
    ell, v, g = [A.inp('input_loader__' + n) for n in ('ell', 'v', 'g')]
    res.extend([(A.add(A.mul(e['Bm1'], v), ell), e['J']), (A.add(ell, g), e['Bm1']), (ell, A.add(N, one))])
    T = A.inp('input_loader__T')
    res.append((A.mul(C(1 << k), T), e['Q']))
    X = A.inp('input_loader__X')
    km = C((1 << k) - 1)
    left = A.mul(km, X)
    right = A.add(A.mul(km, ext['C_e']), A.mul(A.mul(ext['L_e'], C(V)), A.sub(T, one)))
    res.append((left, right))
    W = A.mul(ext['L_e'], T)
    need(A.at == 310 and len(res) == 75, 'loader source boundary')
    return (X, W, res, {'pair_value_bit_length': V.bit_length(), 'pair_width': k})

def kernel_from_upstream():
    receipt = readj(ROOT / 'sources/grill_tag_native_composed205.json')
    frozen = readj(PROD / 'native_unit_kernel.json')
    rows = None
    cases = 0
    for form in receipt['forms']:
        if not form['unit_product']:
            continue
        p = form['compiler']
        aliases = {p['interfaces'][k]: '@' + k for k in ('H', 'M', 'Z', 'scale')}
        rename = lambda x: aliases.get(x, x) if type(x) is str else x
        ds = {n: [o, rename(a), rename(b)] for n, o, a, b in p['source'] if n.startswith('and__')}
        need(len(ds) == 67, 'upstream kernel size')
        target = {n: [o, a, b] for n, o, a, b in frozen['source']}
        need(ds == target, 'all frozen native rows vs pinned upstream')
        need(p['comparisons'][-7:-1] == frozen['comparisons'], 'native six retained comparisons')
        need(p['comparisons'][-1] == [frozen['unit'], 1] and p['unit_factors'] == frozen['unit_factors'], 'unit product')
        need([n for n in p['auxiliaries'] if n.startswith('and__')] == frozen['auxiliaries'], '16 native coordinate names')
        rows = ds
        cases += 1
    need(cases == 4, 'complete native fixtures')
    return (frozen, cases)

def native(A, program, X, kernel):
    begin = A.at
    s = 2 * len(program)
    m = len(program)
    order = list(dict.fromkeys(program))
    g = len(order)
    gi = {n: i for i, n in enumerate(order)}
    counts = Counter(program)
    f = {n: A.inp('native.' + n) for n in ('Z0', 'Vfinal', 'phase_initial', 'height_slack', 'H_U', 'H_V', 'global_bound')}
    sh = A.inp('native.Shat', s)
    zh = A.inp('native.ZVhat', g)
    P0 = A.add(X, f['Z0'])
    Uf = A.add(A.mul(P0, f['Vfinal']), X)
    D = A.add(A.add(Uf, f['phase_initial']), f['height_slack'])
    Kexp = max(3, (s + 3).bit_length(), 2 * max(order) + 2)
    B = A.mul(C(1 << Kexp), D)
    Bm1 = A.sub(B, C(1))
    pairsum = prefix = triangle = C(0)
    groups = [C(0) for _ in order]
    for i, n in enumerate(program):
        pair = A.add(sh[2 * i], sh[2 * i + 1])
        pairsum = A.add(pairsum, pair)
        if i == 0:
            first = pair
        else:
            prefix = A.add(prefix, pair)
            triangle = A.add(triangle, prefix)
        j = gi[n]
        groups[j] = A.add(groups[j], sh[2 * i + 1])
    J = A.sub(pairsum, C(s))
    P = A.add(A.mul(Bm1, J), C(1))
    A.block('history selector and phase linear motifs', begin)
    start = A.at
    G = [A.sub(h, C(counts[n])) for h, n in zip(groups, order)]
    z = [A.sub(v, C(1)) for v in zh]
    nextU = A.add(A.mul(C(2), f['H_U']), A.total(G))
    terms = [f['H_V']]
    for n, sel, zz in zip(order, G, z):
        terms.append(A.mul(C((1 << 2 * n + 1) - 1), zz))
        if n:
            terms.append(A.mul(C(2 * sum_pow4(n)), sel))
    nextV = A.total(terms)
    global_lhs = A.add(A.add(f['H_U'], f['H_V']), A.add(A.total(zh), f['global_bound']))
    residual = [(global_lhs, P), (A.add(A.mul(B, nextU), C(1)), A.add(f['H_U'], A.mul(P, Uf))), (A.add(A.mul(B, nextV), C(1)), A.add(f['H_V'], A.mul(P, f['Vfinal'])))]
    tt = A.sub(triangle, C(m * (m - 1)))
    pl = A.add(A.sub(A.mul(C(m), first), A.mul(Bm1, tt)), f['phase_initial'])
    pr = A.add(J, C(3 * m))
    residual.append((pl, pr))
    A.block('group transports and exact phase residual', start)
    start = A.at
    powers = {0: C(1), 1: P}
    reps = {0: C(0), 1: C(1)}

    def power(n):
        if n not in powers:
            h = power(n // 2)
            sq = A.mul(h, h)
            powers[n] = A.mul(sq, P) if n % 2 else sq
        return powers[n]

    def rep(n):
        if n not in reps:
            h = n // 2
            rh = rep(h)
            factor = A.add(C(1), power(h))
            r = A.mul(rh, factor)
            reps[n] = A.add(r, power(2 * h)) if n % 2 else r
        return reps[n]

    def pack(seq):
        r = C(0)
        for i in range(len(seq) - 1, -1, -1):
            r = A.add(seq[i], A.mul(P, r))
        return r
    S = A.sub(pack(sh), rep(s))
    Mc = A.mul(J, rep(s))
    T = A.add(f['H_U'], A.mul(P, f['H_V']))
    Gp = pack(G)
    Hb = A.mul(f['H_V'], rep(g))
    Mb = A.mul(Bm1, Gp)
    Zb = pack(z)
    RM = A.mul(A.mul(A.sub(D, C(1)), J), A.add(C(1), P))
    ec = g
    er = g + s
    et = g + s + 2
    ei = g + s + 4
    common = A.add(A.mul(power(ec), S), A.mul(power(er), T))
    H = A.total([Hb, common, A.mul(power(et), B), A.mul(power(ei), P0)])
    M = A.total([Mb, A.mul(power(ec), Mc), A.mul(power(er), RM), A.mul(power(et), Bm1), A.mul(power(ei), A.sub(P0, C(1)))])
    Z = A.add(Zb, common)
    scale = power(ei + 1)
    A.block('all paid Horner power repunit and lane motifs', start)
    start = A.at
    env = {n: A.inp('native.' + n) for n in kernel['auxiliaries']}
    env.update({'@H': H, '@M': M, '@Z': Z, '@scale': scale})
    for n, o, a, b in kernel['source']:
        operand = lambda v: C(v) if exact_type(v) else env[v]
        need(n not in env, 'native kernel SSA')
        env[n] = A.op('+-*'.index(o), operand(a), operand(b))
    residual += [(env[a], env[b]) for a, b in kernel['comparisons']]
    A.block('67 pinned native kernel rows', start)
    need(A.at == 3600286, 'native source boundary')
    return (P0, env[kernel['unit']], residual, [env[n] for n in kernel['unit_factors']], {'K_exponent': Kexp, 'scale_exponent': ei + 1, 'groups': g, 'selectors': s})

def structural(A):
    m = A.m
    n = m['ledger']['operations']
    need(len(A.mm) == 8 + n * 17 and A.mm[:8] == b'CDAGv1\x00\x00', 'DAG framing')
    deg = array('Q')
    counts = [0, 0, 0]
    for i in range(n):
        op, a, b = A.getrow(i)
        need(op in (0, 1, 2), 'gate op')
        dd = []
        for r in (a, b):
            if r < 0:
                need(-r <= len(A.cs), 'constant range')
                dd.append(0)
            elif r >= BASE:
                need(r - BASE < m['input_count'], 'input range')
                dd.append(1)
            else:
                need(r < i, 'topological order')
                dd.append(deg[r])
        deg.append(sum(dd) if op == 2 else max(dd))
        counts[op] += 1
    live = bytearray(n)
    used = bytearray(m['input_count'])
    live[m['output']] = 1
    for i in range(n - 1, -1, -1):
        if live[i]:
            for r in A.getrow(i)[1:]:
                if r >= BASE:
                    used[r - BASE] = 1
                elif r >= 0:
                    live[r] = 1
    need(all(live) and all(used), 'whole-source liveness')
    need(deg[m['output']] == 71731007, 'formal degree upper')
    return {'operations': n, 'additions': counts[0], 'subtractions': counts[1], 'multiplications': counts[2], 'degree_upper': deg[m['output']], 'all_gates_live': True, 'all_inputs_live': True}

def main():
    np, nc = pinned_data()
    m = readj(PROD / 'universal.json')
    literal = readj(LIT)
    program = array('I')
    program.frombytes((PROD / 'grill_program.u32').read_bytes())
    if sys.byteorder != 'little':
        program.byteswap()
    a = table_audit(literal, program)
    kernel, cases = kernel_from_upstream()
    with (PROD / 'universal.dag').open('rb') as f, mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as mm:
        A = Audit(m, mm)
        X, W, loader, info = loaders(A, literal, a)
        P0, U, native_pairs, factors, ninfo = native(A, program, X, kernel)
        residuals = native_pairs + loader + [(P0, W)]
        need(residuals == [tuple(x) for x in m['extra']['residual_pairs']], 'all 86 comparison operands exactly')
        need(U == m['extra']['native_unit'] and factors == m['extra']['unit_factors'], 'exact unit and factors')
        begin = A.at
        total = C(0)
        squares = []
        for lhs, rhs in residuals:
            r = A.sub(lhs, rhs)
            q = A.mul(r, r)
            squares.append(q)
            total = A.add(total, q)
        pos = A.add(C(1), total)
        out = A.sub(A.mul(U, pos), C(1))
        A.block('one integer-unit finalizer', begin)
        need(out == m['output'] and A.at == m['ledger']['operations'], 'all source rows consumed')
        need(squares == m['extra']['residual_squares'] and pos == m['extra']['finalizer_positive'], 'complete finalizer roots')
        need(A.used_names == set(A.inputs), 'all declared input families interpreted')
        need(A.input_count == {'external': 6, 'witness': 797135}, 'coordinate ledger')
        result = structural(A)
        result.update(status='PASS_EXACT_SOURCE', constant_recipes=len(A.cs), max_constant_bits=max((abs(v).bit_length() for v in A.cs)), positive_witnesses=A.input_count['witness'], external_parameters=A.input_count['external'], nonunit_comparisons=len(residuals), comparisons_including_unit=len(residuals) + 1, native_kernel_upstream_fixtures=cases, full_program_phases=len(program), authenticated_dependencies=np, connector_authenticated_sources=nc, source_sha256=sha(PROD / 'universal.dag'), motifs=A.motifs, coefficient_checks='Exact integer equality at every runtime constant operand; every recipe is constant-only and topological', theorem_scope='Conditional native/recoder/U15 imports, valid fixed program slices; no complete Pell witness materialized', **info, **ninfo)
    print(json.dumps(result, indent=2, sort_keys=True))
if __name__ == '__main__':
    main()
