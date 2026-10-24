"""Finite structural/algebraic audits, not a substitute for the all-input proof."""
import json, pathlib, collections, hashlib, random, importlib.util
R = pathlib.Path(__file__).resolve().parent
s = importlib.util.spec_from_file_location('builder', R / 'build_direct.py')
b = importlib.util.module_from_spec(s)
s.loader.exec_module(b)
checks = {}

def record(name, n):
    checks[name] = {'passed': True, 'cases': n}

def evaluate(nodes, inputs):
    v = []
    for n in nodes:
        if n[0] == 'c':
            z = n[1]
        elif n[0] == 'v':
            z = inputs[n[1]]
        elif n[0] == 'a':
            z = v[n[1]] + v[n[2]]
        else:
            z = v[n[1]] * v[n[2]]
        v.append(z)
    return v
res = json.loads((R / 'residuals.json').read_text())
eq = json.loads((R / 'equation.json').read_text())
C = json.loads((R / 'circuit.json').read_text())
S = json.loads((R / 'summary.json').read_text())
a = collections.defaultdict(int)
for r in res:
    for x, m in r['terms']:
        for y, n in r['terms']:
            a[tuple(sorted(m + n))] += x * y
actual = {tuple(m): x for x, m in eq['terms']}
if not {m: x for m, x in a.items() if x} == actual:
    raise AssertionError('check failed')
if not (max(map(len, actual)) == 4 and max((max(m, default=-1) for m in actual)) + 1 == eq['variable_count']):
    raise AssertionError('check failed')
record('independent exact SOS expansion and variable domain', len(res))
nodes = C['nodes']
names = C['variable_names']
nv = len(names)
mapping = {}
expected = []

def t(i):
    return {(): nodes[i][1]} if nodes[i][0] == 'c' else {(mapping[i],): 1}

def add(a, b, sgn=1):
    out = collections.defaultdict(int, a)
    for m, v in b.items():
        out[m] += sgn * v
    return {m: v for m, v in out.items() if v}

def mul(a, b):
    out = collections.defaultdict(int)
    for ma, va in a.items():
        for mb, vb in b.items():
            out[tuple(sorted(ma + mb))] += va * vb
    return dict(out)
for i, n in enumerate(nodes):
    if not n[0] in ('c', 'v', 'a', 'm'):
        raise AssertionError('check failed')
    if n[0] == 'v':
        mapping[i] = n[1]
        if not 0 <= n[1] < len(names):
            raise AssertionError('check failed')
    elif n[0] == 'c':
        if not n[1] >= 0:
            raise AssertionError('check failed')
    else:
        if not (n[1] < i and n[2] < i):
            raise AssertionError('check failed')
        mapping[i] = nv
        nv += 1
        value = add(t(n[1]), t(n[2])) if n[0] == 'a' else mul(t(n[1]), t(n[2]))
        expected.append(add(t(i), value, -1))
for left, right, label in C['equalities']:
    expected.append(add(t(left), t(right), -1))
if not expected == [{tuple(m): v for v, m in r['terms']} for r in res]:
    raise AssertionError('check failed')
if not nv == eq['variable_count']:
    raise AssertionError('check failed')
record('every gate and final equality reconstructed', len(expected))
H = json.loads((R / 'horn_shared_source.json').read_text())
for branch in H['branches']:
    p = collections.defaultdict(int)
    for residual in branch['quadratic_residuals']:
        for a in residual:
            for bb in residual:
                p[tuple(sorted(a['monomial'] + bb['monomial']))] += a['coefficient'] * bb['coefficient']
    target = {tuple(sorted(t['monomial'])): t['coefficient'] for t in branch['sum_of_squares']}
    if not {m: x for m, x in p.items() if x} == target:
        raise AssertionError('check failed')
record('twelve exact inherited Horn branches', 12)
row = json.loads((R / 'row_source.json').read_text())
rng = random.Random(120032)
for _ in range(100):
    vs=[rng.randrange(5) for _ in row['variables']];v=dict(zip(row['variables'],vs));vals=evaluate(row['nodes'],vs)
    def pp(ts):
        total=0
        for t0 in ts:
            z=t0['coefficient']
            for name in t0['monomial']:z*=v[name]
            total+=z
        return total
    direct=1
    for branch in H['branches']:direct*=sum(pp(r)**2 for r in branch['quadratic_residuals'])
    rem=[]
    for ind in ['i','next']:
        r=v['x.'+ind+'.remainder'];q=v['x.'+ind+'.quotient'];slack=v['x.'+ind+'.slack'];ix=v['i']+(ind=='next');d=(ix+1)*v['y']+1
        direct+=(v['x']-q*d-r)**2+(d-r-slack-1)**2;rem.append(r)
    for lab in ['p','q','v']:direct+=(v['m']-v[lab]-v[lab+'.upper_slack'])**2
    ss,sp=rem;mm=v['M0']+1
    direct+=(sp*(1+v['v']*mm)-ss*(1+v['p']*mm)*(1+v['q']*mm))**2
    if vals[row['output'][0]]-vals[row['output'][1]]!=direct:raise AssertionError('geometric source mismatch')
record('row polynomial versus direct source evaluation', 100)
c = b.Compiler()
nn = c.var('n')
kk = c.var('k')
out = c.pow(nn, kk)
w = [0] * len(c.vars)
values = {'n': 1, 'k': 1, 'power.output': 1, 'power.w': 1, 'power.a': 2, 'power.t': 2, 'power.z': 1, 'power.x': 2, 'power.y': 1, 'power.truncated_difference': 1, 'pell.u': 7, 'pell.w': 4, 'pell.s': 9, 'pell.t': 1, 'pell.b': 9, 'pell.b.slack': 7, 'pell.by.q1': 2, 'pell.ba.q1': 1, 'pell.w.slack': 3, 'pell.dvd': 4, 'pell.sx.q1': 1}
for i, name in enumerate(c.vars):
    key = name.rsplit('.', 1)[0] if name.rsplit('.', 1)[-1].isdigit() else name
    w[i] = values.get(key, 0)
vv = evaluate(c.nodes, w)
if not all((vv[l] == vv[r] for l, r, _ in c.eqs)):
    raise AssertionError('check failed')
record('nonzero exponent genuine Pell power certificate', 1)
for n in range(10):
    w = [0] * len(c.vars)
    w[0] = n
    w[2] = 1
    vv = evaluate(c.nodes, w)
    if not all((vv[l] == vv[r] for l, r, _ in c.eqs)):
        raise AssertionError('check failed')
for k in range(1, 10):
    w = [0] * len(c.vars)
    w[1] = k
    w[next((i for i, n in enumerate(c.vars) if n.startswith('power.k.slack.')))] = k - 1
    vv = evaluate(c.nodes, w)
    if not all((vv[l] == vv[r] for l, r, _ in c.eqs)):
        raise AssertionError('check failed')
record('power boundary branch certificates', 19)
import math
ncase = 0
for n in range(12):
    for k in range(15):
        result = (2 ** n + 2) ** n // (2 ** n + 1) ** k % (2 ** n + 1)
        if not result == (math.comb(n, k) if k <= n else 0):
            raise AssertionError('check failed')
        ncase += 1
    r = (n + 2) ** (n + 2)
    choose = math.comb(r + n, n)
    if not ((r + 1) ** n + choose - 1) // choose == math.factorial(n):
        raise AssertionError('check failed')
record('binomial and factorial arithmetic identities', ncase + 12)
for N in range(8):
    for T in range(1, 9):
        Q = ((N + 1) * T + 1) ** N + 2
        B = T ** N * math.factorial(N) * math.comb(Q + N, N) % (T * Q - 1)
        if not B == math.prod((1 + (j + 1) * T for j in range(N))):
            raise AssertionError('check failed')
record('encoded CRT modulus product arithmetic identity', 64)
if not (S['input_existentials'] == len(names) and S['arithmetic_wires'] == nv - len(names)):
    raise AssertionError('check failed')
if not (S['ordinary_polynomial_monomials'] == len(actual) and S['max_abs_coefficient'] == max(map(abs, actual.values()))):
    raise AssertionError('check failed')
if not collections.Counter(({'pow': 'power', 'fact': 'factorial', 'choose': 'binomial'}.get(x['kind'], x['kind']) for x in C['call_ledger'])) == S['calls']:
    raise AssertionError('check failed')
record('counts and complete arithmetic-call ledger', len(C['call_ledger']))
(R / 'CHECKS.json').write_text(json.dumps(checks, indent=2) + '\n')
print(json.dumps(checks, indent=2))

# Geometric bound on coefficient sums of A and B separately.
for case in range(1000):
    N=rng.randrange(10);m=rng.randrange(15);ap=1;bp=2
    for _ in range(N):
        p,q,c=[rng.randrange(m+1) for _ in range(3)];ap*=1+c;bp*=(1+p)*(1+q)
    bound=2**(2*m*N+1)
    if max(ap,bp)>bound:raise AssertionError('height bound')
record('geometric height domination',1000)
(R/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
