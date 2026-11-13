#!/usr/bin/env python3
"""Independent syntax comparison; this is not a Lean proof or model bridge."""
import hashlib, json, re, sys
from pathlib import Path

assert sys.flags.isolated and sys.flags.no_site and not sys.flags.optimize
review = Path(__file__).resolve().parent
root = review.parents[1]
packet = root / 'research/nine-sharing-forward38-draft'
ports = {0: 'beta', 1: 'K0', 2: 'MC', 3: 'MF'}
hashes = {
    38: '312ab65ec472f01339c41dab93859e368ec0b9a2213b906856526263dd68eb23',
}

def sha(data): return hashlib.sha256(data).hexdigest()

def parse(text):
    tokens = re.findall(r'w\d+|\d+|[A-Za-z_]+|[:()+*]', text)
    assert ''.join(tokens) == re.sub(r'\s+', '', text), text
    pos = 0
    def take(s=None):
        nonlocal pos
        t = tokens[pos]; pos += 1
        if s is not None: assert t == s, (t, s)
        return t
    def expression():
        nonlocal pos
        t = take()
        if t.startswith('w') and t[1:].isdigit(): return ['var', int(t[1:])]
        assert t == '('
        if tokens[pos].isdigit():
            n = int(take()); take(':'); take('S'); take(')'); return ['num', n]
        if tokens[pos] in ('ports', 'u'):
            k = take(); n = int(take()); take(')')
            return ['port', ports[n]] if k == 'ports' else ['var', n + 1]
        lhs = expression(); op = take(); assert op in ('+', '*')
        rhs = expression(); take(')')
        return ['add' if op == '+' else 'mul', lhs, rhs]
    result = expression(); assert pos == len(tokens)
    return result

results = {}
for n in (38,):
    raw = (root / 'research/nine-sharing-quartic65-norm38-candidate/seed.json').read_bytes()
    assert sha(raw) == hashes[n]
    data = json.loads(raw)
    source = (packet / f'ForwardWitness{n}.lean').read_bytes()
    text = source.decode()
    assert 'UNCOMPILED DRAFT' in text
    assert f'(ports : Fin 4 → S) (u : Fin 14 → S) : Fin {n} → S :=' in text
    assignments = re.findall(r'^  let w(\d+) : S := (.+)$', text, re.M)
    norms = [r for r in data['residuals'] if r['kind'] == 'norm']
    assert len(norms) == 5
    rows = [r['expr'] for r in data['residuals'] if r['kind'] != 'norm']
    assert len(rows) == len(assignments) == n - 14
    known = set(range(1,15))
    for (s, rhs), row in zip(assignments, rows):
        index = int(s)
        assert index not in known and row[:2] == ['sub', ['var', index]]
        actual = parse(rhs)
        assert actual == row[2], (n, index)
        def visit(t):
            if t[0] == 'var': assert t[1] in known
            for child in t[1:]:
                if isinstance(child, list): visit(child)
        visit(actual); known.add(index)
    assert known == set(range(1,n+1))
    vector = re.search(r'^  !\[(.*)\]$', text, re.M).group(1).split(', ')
    assert vector == [f'u {i}' for i in range(14)] + [f'w{i}' for i in range(15,n+1)]
    results[str(n)] = {'seed_sha256': sha(raw), 'lean_sha256': sha(source),
                       'ordered_assignments': len(assignments)}

print(json.dumps({'status': 'PASS_SOURCE_COMPARISON_ONLY', 'forward': results,
  'norm_residuals_skipped': len(norms), 'ports': ports,
  'scope': 'Parsed semiring constructor assignments and vector order only; no Lean elaboration, provider, model or endpoint check.'}, sort_keys=True, indent=2))
