"""Read-only exact formal-polynomial verification of positional code files."""
from pathlib import Path
import json, hashlib, itertools, collections
ROOT = Path(__file__).resolve().parent

def h(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def verify(name, sourcefile):
    cp = ROOT / (name + '_code.json')
    kp = ROOT / (name + '_kernels.json')
    sp = ROOT / '../source' / sourcefile
    code = json.loads(cp.read_text())
    kernel = json.loads(kp.read_text())
    source = json.loads(sp.read_text())
    if not code['source_sha256'] == kernel['source_sha256'] == h(sp):
        raise AssertionError()
    if not kernel['code_sha256'] == h(cp):
        raise AssertionError()
    w = code['weights']
    n = len(w)
    if not (n == 31 and len(set(w)) == n and (min(w) >= 1)):
        raise AssertionError()
    W = max(w)
    if not W == code['max_weight']:
        raise AssertionError()
    targets = code['targets_by_row']
    if not len(set(targets)) == 22:
        raise AssertionError()
    if not code['targets'] == sorted(targets):
        raise AssertionError()
    if not code['order'] == [j + 1 for j in sorted(range(22), key=targets.__getitem__)]:
        raise AssertionError()
    expected = [collections.defaultdict(int) for _ in range(3)]
    for j, row in enumerate(source['equations']):
        for t in row['terms']:
            a = tuple(t['powers'])
            d = sum(a[:n])
            e = targets[j] - sum((x * y for x, y in zip(a[:n], w)))
            if not e >= 0:
                raise AssertionError()
            mult = 2 if d < 2 or max(a[:n]) == 2 else 1
            expected[d][e, a[n:]] += mult * t['coefficient'] * code['row_orientations'][j]
    for d, layer in enumerate(kernel['kernels']):
        actual = {}
        for t in layer['terms']:
            for c in t['coefficient']:
                k = (t['exponent'], tuple(c['powers']))
                if not k not in actual:
                    raise AssertionError()
                actual[k] = c['coefficient']
        if not actual == {k: v for k, v in expected[d].items() if v}:
            raise AssertionError(('kernel', d))
    candidate = [[((), 0, 1)], [], []]
    for i in range(n):
        candidate[1].append(((i,), w[i], 1))
    for i in range(n):
        for j in range(i, n):
            candidate[2].append(((i, j), w[i] + w[j], 1 if i == j else 2))
    extracted = [collections.defaultdict(int) for _ in range(22)]
    targetmap = {v: j for j, v in enumerate(targets)}
    interactions = 0
    hitterms = 0
    for d, layer in enumerate(kernel['kernels']):
        for t in layer['terms']:
            for inds, e, mult in candidate[d]:
                interactions += 1
                where = targetmap.get(t['exponent'] + e)
                if where is None:
                    continue
                hitterms += 1
                a = [0] * n
                for i in inds:
                    a[i] += 1
                for c in t['coefficient']:
                    extracted[where][tuple(a) + tuple(c['powers'])] += mult * c['coefficient']
    for j, row in enumerate(source['equations']):
        desired = {tuple(t['powers']): 2 * t['coefficient'] * code['row_orientations'][j] for t in row['terms']}
        if not {k: v for k, v in extracted[j].items() if v} == desired:
            raise AssertionError(('target', j + 1))
    degrees = [max((t['exponent'] for t in k['terms'])) for k in kernel['kernels']]
    if not degrees == code['kernel_degrees']:
        raise AssertionError()
    H = max((degrees[d] + d * W for d in range(3)))
    if not H == code['convolution_height']:
        raise AssertionError()
    lead = kernel['kernels'][2]['terms'][-1]
    if not all((c['coefficient'] > 0 for c in lead['coefficient'])):
        raise AssertionError()
    gaps = [degrees[2] + W - degrees[1], degrees[2] + 2 * W - degrees[0]]
    if not gaps == code['quadratic_positivity_gaps']:
        raise AssertionError()
    for dd in [0, 1]:
        if not (gaps[1 - dd] >= 1 or all((c['coefficient'] > 0 for c in kernel['kernels'][dd]['terms'][-1]['coefficient']))):
            raise AssertionError()
    if not (max(targets) == code['maximum_target'] and H - max(targets) >= 2):
        raise AssertionError()
    if not (interactions == code['exhaustive_interactions'] and hitterms == code['record_count'] == code['intended_hits']):
        raise AssertionError()
    return {'name': name, 'source': sourcefile, 'height': H, 'maximum_weight': W, 'interactions': interactions, 'target_identities': 22, 'code_sha256': h(cp), 'kernels_sha256': h(kp), 'status': 'PASS'}

def main():
    out = []
    for x in json.loads((ROOT / 'CERTIFICATES.json').read_text()):
        sf = 'gapNq85_source.json' if x['name'].startswith('gapNq') else 'gapN86_source.json'
        out.append(verify(x['name'], sf))
    print(json.dumps({'checks': out, 'status': 'PASS'}, indent=2))
if __name__ == '__main__':
    main()
