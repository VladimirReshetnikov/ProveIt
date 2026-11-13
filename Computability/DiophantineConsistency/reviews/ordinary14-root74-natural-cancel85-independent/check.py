#!/usr/bin/env python3
"""Independent exact graph cuts and modular diagonal; does not invoke Lean."""
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[2]
author = root / 'research/ordinary14-root74-natural-cancel85'
parent = root / 'research/ordinary14-root74-natural-cancel86'
sha = lambda b: hashlib.sha256(b).hexdigest()
for path, h in {
    author / 'README.md': '9cde191ad41cf8a3bfc5d8d91003e880e37e3595036928e42b867187998330bd',
    author / 'candidate.json': '24a5ddfdabeae36eb40867239fdc5dfd53ba60d611f0e83268ffb9bfbac85957',
    author / 'check.py': '311db241831cb0dd1fa59aa996489e67b2a7a716f5c1127ef0400f28716e169e',
    author / 'result.json': 'ebf2caacb30f6b88aa47fbef3277aad971fdd3bfbf8c548f53795d003cc4d2f0',
    parent / 'candidate.json': '0211a1bcac635af617090facdc3b7f98d18ad94579027df840532d87ae5a5170',
    parent / 'check.py': 'a2d45e7346c9d41e157318b67cf19a412e5a4f35b4a031c1a7073d5c8058ab05',
    parent / 'result.json': 'f19c4f42c52605ccebef713e7fbe3705ab2145c8136a783e90a884158bc47eda',
}.items():
    assert sha(path.read_bytes()) == h, str(path)
tail = b'\nIndependent external review: [natural cancellation 85](../../reviews/ordinary14-root74-natural-cancel85-independent/README.md).\n'
readme = (author / 'README.md').read_bytes()
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == 'f625582006ce501d33be9df787e116b8de119ed7b50c05006f24575e728f5196'
old = json.loads((parent / 'candidate.json').read_bytes())
new = json.loads((author / 'candidate.json').read_bytes())
assert old['parent_sha256'] != new['parent_sha256']
assert new['parent_sha256'] == sha((parent / 'candidate.json').read_bytes())
assert old['witnesses'] == new['witnesses'] and len(new['witnesses']) == 14
assert old['fixed_numerals'] == new['fixed_numerals'] and len(new['fixed_numerals']) == 4
assert old['domain'] == new['domain'] == 'nonnegative integers'
assert old['output'] == new['output'] == 'out'
assert len(old['source']) == old['operations'] == 86
assert len(new['source']) == new['operations'] == 85

def inspect(g):
    env = set(g['witnesses'] + g['fixed_numerals'])
    assert len(env) == 18
    byname = {}
    for name, op, x, y in g['source']:
        assert name not in env and op in ('+', '-', '*')
        assert all(type(z) is int or z in env for z in (x, y))
        byname[name] = (op, x, y)
        env.add(name)
    needed = {g['output']}
    for name, _, x, y in reversed(g['source']):
        if name in needed:
            needed.update(z for z in (x, y) if isinstance(z, str))
    return byname, needed

a, _ = inspect(old)
b, live = inspect(new)
assert set(b).issubset(live) and set(new['witnesses'] + new['fixed_numerals']).issubset(live)
assert {n: a[n] for n in ('zeta', 'k', 'g52', 'r0')} == {
    'zeta': ('+', 'n_zeta', 1), 'k': ('+', 'eta', 'zeta'),
    'g52': ('-', 'k', 'R'), 'r0': ('-', 'g52', 1)}
assert {n: b[n] for n in ('kbase', 'k', 'r0')} == {
    'kbase': ('+', 'eta', 'n_zeta'), 'k': ('+', 'kbase', 1), 'r0': ('-', 'kbase', 'R')}
assert {n for n, (_, x, y) in a.items() if 'zeta' in (x, y)} == {'k'}
assert {n for n, (_, x, y) in a.items() if 'g52' in (x, y)} == {'r0'}
assert set(a) - set(b) == {'zeta', 'g52'} and set(b) - set(a) == {'kbase'}
assert all(a[n] == b[n] for n in set(a) & set(b) - {'k', 'r0'})
# Exact coefficient-vector identities in Z[eta,n_zeta,R], including constants.
eta, z, R, one = ((1,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1))
add = lambda x,y: tuple(i+j for i,j in zip(x,y))
sub = lambda x,y: tuple(i-j for i,j in zip(x,y))
k_old = add(eta, add(z, one)); k_new = add(add(eta, z), one)
assert k_old == k_new
assert sub(sub(k_old, R), one) == sub(add(eta, z), R)

# Independent read/decompression and all-coefficient univariate F_p evaluation.
p72 = root / 'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
p115 = root / 'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json'
assert sha((p72 / 'ACTIVE_BINDING.json').read_bytes()) == '6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'
assert sha(p115.read_bytes()) == 'dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'
binding = json.loads((p72 / 'ACTIVE_BINDING.json').read_bytes())
supplement = json.loads(p115.read_bytes())
prime = 1000000007
fixed = {}
for n, info in binding['ports'].items():
    assert supplement['ports'][n]['sha256_raw'] == info['sha256_raw']
    assert supplement['ports'][n]['sha256_gzip'] == info['sha256_gzip']
    data = (p72 / info['path']).read_bytes()
    assert sha(data) == info['sha256_gzip']
    raw = gzip.decompress(data)
    assert len(raw) == info['raw_bytes'] and sha(raw) == info['sha256_raw']
    fixed[n] = int.from_bytes(raw, 'little') % prime
assert set(fixed) == set(new['fixed_numerals'])
env = {n:{1:1} for n in new['witnesses']}
env.update({n:{0:v} for n,v in fixed.items()})
def get(x):
    return {0:x % prime} if type(x) is int else env[x]
for name, op, x, y in new['source']:
    x, y = get(x), get(y)
    r = {}
    if op == '*':
        for i, u in x.items():
            for j, v in y.items():
                r[i+j] = (r.get(i+j,0) + u*v) % prime
    else:
        for i in x.keys() | y.keys():
            r[i] = (x.get(i,0) + (1 if op == '+' else -1) * y.get(i,0)) % prime
    env[name] = {i:v for i,v in r.items() if v}
assert max(env['out']) == 107 and env['out'][107] == 419359493

replayed = subprocess.run([sys.executable, '-I', '-S', '-B', str(author/'check.py')],
                          cwd=root, capture_output=True, check=True, timeout=180)
assert not replayed.stderr and replayed.stdout == (author/'result.json').read_bytes()
assert json.loads((parent/'result.json').read_bytes())['degree_upper_from_replayed_88'] == 107
print(json.dumps({'status':'PASS', 'exact_cut_identities':2, 'live_gates':85,
  'live_inputs':14, 'live_ports':4, 'ray_degree':107, 'ray_leader':419359493,
  'ray_prime':prime, 'upper_bound':'inherited from replayed 86 and 88 certificates',
  'author_receipt_reproduced':True, 'lean_run':False, 'physical_binding_in_lean':False},
  indent=2, sort_keys=True))
