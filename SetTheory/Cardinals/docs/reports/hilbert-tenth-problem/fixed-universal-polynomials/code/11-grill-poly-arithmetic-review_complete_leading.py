# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Optional independent top-homogeneous coefficient probes; zero is inconclusive."""
from array import array
from pathlib import Path
import hashlib, json, mmap, random, resource, struct, time
resource.setrlimit(resource.RLIMIT_AS, (1024 ** 3, 1024 ** 3))
resource.setrlimit(resource.RLIMIT_CPU, (300, 300))
root = Path(__file__).resolve().parent
m = json.loads((root / 'universal.json').read_text())
base = 1 << 50
row = struct.Struct('<Bqq')
start = time.monotonic()

def geom_mod(n, p):
    bp, bs, ap, ass = (4, 1, 1, 0)
    while n:
        if n & 1:
            ass = (ass + ap * bs) % p
            ap = ap * bp % p
        bs = bs * (1 + bp) % p
        bp = bp * bp % p
        n //= 2
    return ass
trials = []
with open(root / 'universal.dag', 'rb') as f, mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ) as mm:
    for p, seed in [(2305843009213693951, 2026100391), (2147483647, 2026100392)]:
        const = []
        for r in m['constants']:
            op = r[0]
            if op == 'int':
                z = int(r[1])
            elif op == 'pow2':
                z = pow(2, r[1], p)
            elif op == 'geom4':
                z = geom_mod(r[1], p)
            else:
                a, b = (const[-r[1] - 1], const[-r[2] - 1])
                z = a + b if op == 'add' else a - b if op == 'sub' else a * b
            const.append(z % p)
        rng = random.Random(seed)
        inputs = array('Q', (rng.randrange(1, p) for _ in range(m['input_count'])))
        deg = array('Q')
        lead = array('Q')

        def at(h):
            return (0, const[-h - 1]) if h < 0 else (1, inputs[h - base]) if h >= base else (deg[h], lead[h])
        for i in range((len(mm) - 8) // 17):
            op, a, b = row.unpack_from(mm, 8 + 17 * i)
            da, va = at(a)
            db, vb = at(b)
            if op == 2:
                d = da + db
                v = va * vb % p
            else:
                d = max(da, db)
                v = ((va if da == d else 0) + (1 if op == 0 else -1) * (vb if db == d else 0)) % p
            deg.append(d)
            lead.append(v)
        trials.append({'modulus': p, 'seed': seed, 'formal_degree': deg[-1], 'top_homogeneous_value': lead[-1], 'native_unit_top_value': lead[m['extra']['native_unit']], 'unit_factor_top_values': [lead[h] for h in m['extra']['unit_factors']], 'status': 'degree_bound_attained' if lead[-1] else 'inconclusive'})
        print(json.dumps(trials[-1]), flush=True)
result = {'trials': trials, 'scope': 'Evaluate propagated degree-bound homogeneous forms modulo primes at deterministic nonzero coordinate weights. A nonzero final value certifies the upper bound is attained; zero does not lower the bound.', 'source_sha256': m['source_sha256'], 'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'resources': {'seconds': time.monotonic() - start, 'max_rss_bytes': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024}}
(root / 'review_complete_leading.json').write_text(json.dumps(result, indent=2) + '\n')
