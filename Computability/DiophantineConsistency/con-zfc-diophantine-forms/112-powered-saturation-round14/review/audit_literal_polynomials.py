"""Independent data-only audit. Does not import or execute archive code."""
import collections, hashlib, json, pathlib

ROOT = pathlib.Path(__file__).resolve().parents[1]
results = []
paths = [p for p in sorted((ROOT / 'intake').glob('*/**/equations/*/equation.json'))
         if p.parent.name in {'natural363', 'natural364', 'integer660', 'natural375', 'integer553'}]
paths += sorted((ROOT/'review'/'sources').glob('public*/equation.json'))
for p in paths:
    eq = json.loads(p.read_text())
    exp_path = p.with_name('expanded_polynomial.json')
    if not exp_path.exists():
        exp_path = p.with_name('polynomial.json')
    exp = json.loads(exp_path.read_text())
    n = len(eq['variables'])
    if len(set(json.dumps(v, sort_keys=True) for v in eq['variables'])) != n:
        raise ValueError('duplicate variables')
    poly = collections.defaultdict(int)
    for row in eq['residuals']:
        r = collections.defaultdict(int)
        for c, inds in row['terms']:
            if type(c) is not int or len(inds) > 2 or any(type(i) is not int or not 0 <= i < n for i in inds):
                raise ValueError('invalid quadratic residual term')
            r[tuple(sorted(inds))] += c
        for a, ca in r.items():
            for b, cb in r.items():
                poly[tuple(sorted(a+b))] += ca * cb
    poly = {m:c for m,c in poly.items() if c}
    claimed = {tuple(inds): c for c,inds in exp['terms']}
    if len(claimed) != len(exp['terms']) or any(tuple(sorted(k)) != k for k in claimed) or poly != claimed:
        raise ValueError('expanded polynomial mismatch')
    data = dict(variables=n, quadratic_rows=len(eq['residuals']), exact_degree=max(map(len,poly)),
                expanded_monomials=len(poly), max_abs_expanded_coefficient=max(map(abs,poly.values())))
    if any(eq['metrics'][k] != v for k,v in data.items()):
        raise ValueError('metrics mismatch')
    used = {i for m in poly for i in m}
    if used != set(range(n)):
        raise ValueError('unused or missing coordinates')
    data.update(domain=eq['domain'], label=p.parent.name, equation_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),
                expanded_sha256=hashlib.sha256(exp_path.read_bytes()).hexdigest(), coefficient_height_bits=data['max_abs_expanded_coefficient'].bit_length(),
                equation_path=str(p.relative_to(ROOT)), status='PASS')
    results.append(data)
receipt = {'scope':'Independent complete expansion and metric verification for seven literal polynomial data files. No source scripts imported; no claim to verify unbounded arithmetic/calibration proofs.', 'results':results}
out = ROOT/'review'/'LITERAL_AUDIT.json'
out.write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt, indent=2))
