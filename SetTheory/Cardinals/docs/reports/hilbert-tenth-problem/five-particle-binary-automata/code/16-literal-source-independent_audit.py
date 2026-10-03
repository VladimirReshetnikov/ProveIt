#!/usr/bin/env python3
# Verification conditions are explicit and remain active under python -O.
"""Independent graph audit. Never imports build_source.py or its functions.

Certificates supply private-state names only. Each graph is reconstructed from
the previous literal layer; total equality, not sampling, establishes coverage.
Finite traces corroborate clocks; the all-input proofs are in the audit note.
"""
import collections
import hashlib
import itertools
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
PRIMES = (2, 3, 5, 7, 11)

def load(name):
    return json.loads((ROOT / name).read_text())

def edge(e):
    return (e['source'], e['counter'], e['symbol'], e['target'])

def grouped(es, field):
    d = collections.defaultdict(list)
    for e in es:
        d[e[field]].append(e)
    return d

def compatible(a, b):
    return a['counter'] == b['counter'] and {a['symbol'], b['symbol']} == {'Z', 'P'}

def structure(m, reversible):
    rows, controls = (m['rows'], m['controls'])
    if not len(controls) == len(set(controls)):
        raise AssertionError('Verification obligation failed')
    if not len(rows) == len({e['name'] for e in rows}):
        raise AssertionError('Verification obligation failed')
    if not len(rows) == len({edge(e) for e in rows}):
        raise AssertionError('Verification obligation failed')
    if not set(controls) == {m['start'], m['halt']} | {q for e in rows for q in (e['source'], e['target'])}:
        raise AssertionError('Verification obligation failed')
    if not all((0 <= e['counter'] < m['counters'] and e['symbol'] in ('Z', 'P', '+', '-', '0') for e in rows)):
        raise AssertionError('Verification obligation failed')
    if not not any((e['target'] == m['start'] for e in rows)):
        raise AssertionError('Verification obligation failed')
    if not not any((e['source'] == m['halt'] for e in rows)):
        raise AssertionError('Verification obligation failed')
    for field in ('source', 'target') if reversible else ('source',):
        for q, es in grouped(rows, field).items():
            if not all((compatible(a, b) for a, b in itertools.combinations(es, 2))):
                raise AssertionError((field, q, es))

def exact(m, expected):
    actual = collections.Counter((edge(e) for e in m['rows']))
    expect = collections.Counter(expected)
    if not actual == expect:
        raise AssertionError({'missing': list((expect - actual).items())[:5], 'extra': list((actual - expect).items())[:5]})

def run(out, start, values, boundaries, limit):
    q, v, t = (start, list(values), 0)
    while t <= limit:
        if t and q in boundaries:
            return (q, tuple(v), t, False)
        enabled = []
        for e in out.get(q, []):
            x, n = (e['symbol'], v[e['counter']])
            if x in ('+', '0') or (x in ('P', '-') and n > 0) or (x == 'Z' and n == 0):
                enabled.append(e)
        if not len(enabled) <= 1:
            raise AssertionError('Verification obligation failed')
        if not enabled:
            return (q, tuple(v), t, True)
        e = enabled[0]
        if e['symbol'] in ('+', '-'):
            v[e['counter']] += 1 if e['symbol'] == '+' else -1
        q, t = (e['target'], t + 1)
    raise AssertionError(('clock bound exceeded', start, values, limit))

def main():
    v = load('dependency/virtual3.json')
    m, n, h, p = [load(f) for f in ('primitive3.json', 'normalized3.json', 'reversible5.json', 'reversible2-primitives.json')]
    c, s = (load('certificates.json'), load('source.json'))
    for machine, rev in ((m, False), (n, False), (h, True), (p, True)):
        structure(machine, rev)
    expected = [('START', 0, '0', v['entry'])]
    for j, (q, row) in enumerate(v['rows'].items()):
        op, i, *dst = row
        if op == 'ADD':
            expected.append((q, i, '+', dst[0]))
        else:
            if not op == 'SUB':
                raise AssertionError('Verification obligation failed')
            d = f'v{j:04}d'
            expected += [(q, i, 'Z', dst[1]), (q, i, 'P', d), (d, i, '-', dst[0])]
    exact(m, expected)
    incoming = grouped(m['rows'], 'target')
    if not {a['target'] for a in c['normalization']} == {q for q, es in incoming.items() if len(es) > 2}:
        raise AssertionError('Verification obligation failed')
    if not len(c['normalization']) == len({a['target'] for a in c['normalization']}):
        raise AssertionError('Verification obligation failed')
    normalized = {e['name']: edge(e) for e in m['rows']}
    added = []
    for a in c['normalization']:
        es, chain = (incoming[a['target']], a['chain'])
        if not a['incoming'] == [e['name'] for e in es]:
            raise AssertionError('Verification obligation failed')
        if not len(chain) == len(es) - 2:
            raise AssertionError('Verification obligation failed')
        for j, e in enumerate(es):
            dest = chain[max(0, j - 1)] if j < len(es) - 1 else a['target']
            normalized[e['name']] = (e['source'], e['counter'], e['symbol'], dest)
        added += [(q, 0, '0', chain[j + 1] if j + 1 < len(chain) else a['target']) for j, q in enumerate(chain)]
    exact(n, list(normalized.values()) + added)
    if not max(map(len, grouped(n['rows'], 'target').values())) <= 2:
        raise AssertionError('Verification obligation failed')
    incoming = grouped(n['rows'], 'target')
    collisions = {q for q, es in incoming.items() if len(es) == 2 and (not compatible(*es))}
    if not {a['target'] for a in c['history']} == collisions:
        raise AssertionError('Verification obligation failed')
    if not len(c['history']) == len(collisions):
        raise AssertionError('Verification obligation failed')
    expected = [edge(e) for e in n['rows'] if e['target'] not in collisions]
    history_cases = []
    for a in c['history']:
        t, d, parts = (a['target'], a['doubling'], a['parts'])
        es = incoming[t]
        if not a['incoming'] == [e['name'] for e in es]:
            raise AssertionError('Verification obligation failed')
        if not (len(d) == 6 and len(parts) == 2 and all((len(z) == 5 for z in parts))):
            raise AssertionError('Verification obligation failed')
        for bit, (e, z) in enumerate(zip(es, parts)):
            expected += [(e['source'], e['counter'], e['symbol'], z[0]), (z[0], 4, 'Z', z[1]), (z[1], 3, 'Z', d[0] if bit == 0 else d[4]), (z[1], 3, 'P', z[2]), (z[2], 3, '-', z[3]), (z[3], 4, '+', z[4]), (z[4], 4, 'P', z[1])]
            history_cases.append((e, bit))
        expected += [(d[0], 4, 'Z', t), (d[0], 4, 'P', d[1]), (d[1], 4, '-', d[2]), (d[2], 3, '+', d[3]), (d[3], 3, 'P', d[4]), (d[4], 3, '+', d[5]), (d[5], 3, 'P', d[0])]
    exact(h, expected)
    hi, ho = (grouped(h['rows'], 'target'), grouped(h['rows'], 'source'))
    restores = c['restoration']
    targets = {q for q, es in hi.items() if es[0]['symbol'] in ('Z', 'P')}
    if not set(restores) == targets:
        raise AssertionError('Verification obligation failed')
    for q in targets:
        if not all((e['symbol'] in ('Z', 'P') and e['counter'] == hi[q][0]['counter'] for e in hi[q])):
            raise AssertionError('Verification obligation failed')
        if not restores[q]['prime'] == PRIMES[hi[q][0]['counter']]:
            raise AssertionError('Verification obligation failed')
    if not len(c['prime']) == len(ho):
        raise AssertionError('Verification obligation failed')
    if not {a['source'] for a in c['prime']} == set(ho):
        raise AssertionError('Verification obligation failed')
    expected = []
    for a in c['prime']:
        q, pref = (a['source'], a['prefix'])
        es = ho[q]
        if not a['rows'] == [e['name'] for e in es]:
            raise AssertionError('Verification obligation failed')
        x, prime = (es[0]['symbol'], PRIMES[es[0]['counter']])
        if not all((e['counter'] == es[0]['counter'] for e in es)):
            raise AssertionError('Verification obligation failed')
        if not a['kind'] == ('test' if x in ('Z', 'P') else x):
            raise AssertionError('Verification obligation failed')
        if x == '0':
            if not (len(es) == 1 and a['target'] == es[0]['target']):
                raise AssertionError('Verification obligation failed')
            expected.append((q, 0, '0', es[0]['target']))
            continue
        if not a['prime'] == prime:
            raise AssertionError('Verification obligation failed')
        if x in ('+', '-'):
            if not (len(es) == 1 and a['target'] == es[0]['target']):
                raise AssertionError('Verification obligation failed')
            st = lambda j: pref + f'S{j}'
            expected += [(q, 1, 'Z', st(1)), (st(1), 0, 'Z', st(5)), (st(1), 0, 'P', st(2)), (st(2), 0, '-', st(3)), (st(3), 1, '+', st(4)), (st(4), 1, 'P', st(1)), (st(5), 1, 'Z', es[0]['target'])]
            if x == '+':
                expected += [(st(5), 1, 'P', st(6)), (st(6), 1, '-', pref + 'C0')]
                expected += [(pref + f'C{j}', 0, '+', pref + f'C{j + 1}' if j + 1 < prime else st(7)) for j in range(prime)]
            else:
                expected.append((st(5), 1, 'P', pref + 'C0'))
                expected += [(pref + f'C{j}', 1, '-', pref + f'C{j + 1}' if j + 1 < prime else st(6)) for j in range(prime)]
                expected.append((st(6), 0, '+', st(7)))
            expected.append((st(7), 0, 'P', st(5)))
        else:
            ts = {e['symbol']: e['target'] for e in es}
            if not a['targets'] == ts:
                raise AssertionError('Verification obligation failed')
            st = lambda j, k: pref + f'R{j}T{k}'
            expected.append((q, 1, 'Z', st(0, 1)))
            for j in range(prime):
                symbol = 'P' if j == 0 else 'Z'
                if symbol in ts:
                    expected.append((st(j, 1), 0, 'Z', restores[ts[symbol]]['prefix'] + f'R{j}T1'))
                expected += [(st(j, 1), 0, 'P', st(j, 2)), (st(j, 2), 0, '-', st(j + 1, 1))]
            expected += [(st(prime, 1), 1, '+', st(prime, 2)), (st(prime, 2), 1, 'P', st(0, 1))]
    for q, a in restores.items():
        pref, prime = (a['prefix'], a['prime'])
        st = lambda j, k: pref + f'R{j}T{k}'
        expected += [(st(0, 1), 1, 'Z', q), (st(0, 1), 1, 'P', st(0, 2)), (st(0, 2), 1, '-', st(prime, 1))]
        for j in range(prime, 0, -1):
            expected += [(st(j, 1), 0, '+', st(j, 2)), (st(j, 2), 0, 'P', st(j - 1, 1))]
    exact(p, expected)
    if not (s['start'] == p['start'] and s['halt'] == p['halt'] and (s['controls'] == p['controls'])):
        raise AssertionError('Verification obligation failed')
    if not s['class_cut'] == 0:
        raise AssertionError('Verification obligation failed')
    if not len(s['branches']) == len(p['rows']):
        raise AssertionError('Verification obligation failed')
    named = {e['name']: e for e in p['rows']}
    if not len({b['name'] for b in s['branches']}) == len(named):
        raise AssertionError('Verification obligation failed')
    for b in s['branches']:
        e = named[b['name']]
        if not (b['source'] == e['source'] and b['target'] == e['target']):
            raise AssertionError('Verification obligation failed')
        if not b['side'] == (-1 if e['counter'] == 0 else 1):
            raise AssertionError('Verification obligation failed')
        if not b['delta'] == (1 if e['symbol'] == '+' else -1 if e['symbol'] == '-' else 0):
            raise AssertionError('Verification obligation failed')
        guard = {'op': 'true'} if e['symbol'] not in ('Z', 'P', '-') else {'op': 'eq' if e['symbol'] == 'Z' else 'gt', 'counter': e['counter'], 'value': 0}
        if not b['guard'] == guard:
            raise AssertionError('Verification obligation failed')
    hist_traces, prime_traces = (0, 0)
    for e, bit in history_cases:
        for old_h in (0, 1, 2, 3, 7):
            values = [2, 3, 4, old_h, 0]
            if e['symbol'] == 'Z':
                values[e['counter']] = 0
            wanted = values.copy()
            if e['symbol'] in ('+', '-'):
                wanted[e['counter']] += 1 if e['symbol'] == '+' else -1
            wanted[3] = 2 * old_h + bit
            clock = 10 * old_h + 4 + 2 * bit
            got = run(ho, e['source'], values, set(n['controls']), clock)
            if not got == (e['target'], tuple(wanted), clock, False):
                raise AssertionError((e, bit, old_h, got))
            hist_traces += 1
    po, boundaries = (grouped(p['rows'], 'source'), set(h['controls']))
    for a in c['prime']:
        kind, q, prime = (a['kind'], a['source'], a.get('prime', 2))
        if kind == '-':
            numbers = [prime, 2 * prime, 3 * prime]
        else:
            numbers = sorted({1, prime - 1, prime, prime + 1, 2 * prime, 2 * prime + 1, 3 * prime + 2})
        for value in numbers:
            if kind == '0':
                clock, dest, result = (1, a['target'], value)
            elif kind == '+':
                clock, dest, result = ((prime + 7) * value + 3, a['target'], prime * value)
            elif kind == '-':
                clock, dest, result = (4 * value + (prime + 3) * (value // prime) + 3, a['target'], value // prime)
            else:
                symbol = 'P' if value % prime == 0 else 'Z'
                clock, dest, result = (4 * value + 4 * (value // prime) + 3, a['targets'].get(symbol), value)
            got = run(po, q, (value, 0), boundaries, clock)
            if dest is None:
                if not (got[3] and got[0] not in boundaries and (got[2] < clock)):
                    raise AssertionError('Verification obligation failed')
            elif not got == (dest, (result, 0), clock, False):
                raise AssertionError((a, value, got))
            prime_traces += 1
    names = ('dependency/virtual3.json', 'primitive3.json', 'normalized3.json', 'reversible5.json', 'reversible2-primitives.json', 'source.json', 'certificates.json')
    receipt = {'status': 'PASS', 'audit_scope': 'independent whole-graph reconstruction, global syntactic determinism/reversibility, literal trace clock corroboration', 'all_input_basis': 'canonical whole-graph equality plus invariant/rank proofs in independent-macro-audit.md; finite traces are supplementary', 'layers': {name: {'controls': len(x['controls']), 'rows': len(x['rows'])} for name, x in (('primitive3', m), ('normalized3', n), ('reversible5', h), ('reversible2', p))}, 'history_collision_pairs': len(c['history']), 'prime_macros': len(c['prime']), 'shared_restorations': len(restores), 'literal_history_traces': hist_traces, 'literal_prime_traces': prime_traces, 'sha256': {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in names}, 'visual_primary_pdf_check': 'Unavailable: web PDF screenshots failed and live PDF URL returned HTML; explicit graphs proved directly instead.'}
    (ROOT / 'independent-audit-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))
if __name__ == '__main__':
    main()
