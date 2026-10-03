#!/usr/bin/env python3
"""Independent finite corroboration of the CA-clock domination theorem.

Reads frozen tables, never imports their builder/checkers, never compiles a CA,
and writes only the selected receipt. All checks survive Python -O.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT))
from verify_pins import verify_inputs
from baseline_support import regenerated_baseline
OPT = ROOT
PRIMES = (2, 3, 5, 7, 11)


def require(condition, detail):
    if not condition:
        raise RuntimeError(detail)


def read(root, name):
    return json.loads((root / name).read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def grouped(rows, idx):
    answer = defaultdict(list)
    for row in rows:
        answer[row[idx]].append(row)
    return answer


def edge(row):
    return row['source'], row['counter'], row['symbol'], row['target']


def enabled(symbol, n):
    return symbol in ('0', '+') or (n == 0 if symbol == 'Z' else n > 0)


def delta(symbol):
    return 1 if symbol == '+' else -1 if symbol == '-' else 0


def compatible_pair(rows):
    return len(rows) == 2 and rows[0][1] == rows[1][1] and {e[2] for e in rows} == {'Z', 'P'}


def structural_checks(machine, reversible):
    rows = [edge(e) for e in machine['rows']]
    require(len(machine['controls']) == len(set(machine['controls'])), 'Duplicate control')
    require(len(rows) == len(set(rows)) == len({e['name'] for e in machine['rows']}), 'Duplicate row')
    require(set(machine['controls']) == {machine['start'], machine['halt']} | {q for e in rows for q in (e[0], e[3])},
            'Declared controls differ from graph vertices')
    require(not any(e[0] == machine['halt'] or e[3] == machine['start'] for e in rows), 'Start/halt normal form')
    require(all(0 <= e[1] < machine['counters'] and e[2] in ('0', '+', '-', 'Z', 'P') for e in rows),
            'Primitive alphabet')
    for idx in ((0, 3) if reversible else (0,)):
        for q, es in grouped(rows, idx).items():
            require(len(es) == 1 or compatible_pair(es), ('Local deterministic/reversible row condition', idx, q))


def reconstruct_history(normal, cert, flipped=frozenset()):
    by_name = {row['name']: row for row in normal['rows']}
    collision_targets = {item['target'] for item in cert['history']}
    result = [edge(row) for row in normal['rows'] if row['target'] not in collision_targets]
    for item in cert['history']:
        names = item['incoming'][::-1] if item['target'] in flipped else item['incoming']
        d = item['doubling']
        for bit, name in enumerate(names):
            original = by_name[name]
            a, b, c, e, f = item['parts'][bit]
            result.extend([
                (original['source'], original['counter'], original['symbol'], a),
                (a, 4, 'Z', b), (b, 3, 'Z', d[0 if bit == 0 else 4]),
                (b, 3, 'P', c), (c, 3, '-', e), (e, 4, '+', f), (f, 4, 'P', b),
            ])
        result.extend([
            (d[0], 4, 'Z', item['target']), (d[0], 4, 'P', d[1]),
            (d[1], 4, '-', d[2]), (d[2], 3, '+', d[3]),
            (d[3], 3, 'P', d[4]), (d[4], 3, '+', d[5]),
            (d[5], 3, 'P', d[0]),
        ])
    return result


def history_signature_and_literal_counts(rows, control_count):
    """Count expansion from local templates, without materializing its rows."""
    sources = grouped(rows, 0)
    incoming = grouped(rows, 3)
    sig_source = Counter()
    sig_restorer = Counter()
    symbol_counts = Counter()
    extra_controls = 0
    for q, edges in sources.items():
        indices = {e[1] for e in edges}
        symbols = ''.join(sorted(e[2] for e in edges))
        require(len(indices) == 1, ('counter mismatch', q))
        p = PRIMES[next(iter(indices))]
        sig_source[p, symbols] += 1
        if symbols == '0':
            symbol_counts['0'] += 1
        elif symbols in ('+', '-'):
            extra_controls += p + 7
            symbol_counts.update({'Z': 3, 'P': 4})
            symbol_counts.update({'+': p + 1, '-': 2} if symbols == '+' else {'+': 2, '-': p + 1})
        else:
            require(symbols in ('P', 'Z', 'PZ'), ('unexpected source group', q, symbols))
            exits = int('P' in symbols) + (p - 1) * int('Z' in symbols)
            extra_controls += 2 * p + 2
            symbol_counts.update({'Z': 1 + exits, 'P': p + 1, '-': p, '+': 1})
    for q, edges in incoming.items():
        tested = [e for e in edges if e[2] in ('Z', 'P')]
        if not tested:
            continue
        require(len(tested) == len(edges) and len({e[1] for e in edges}) == 1,
                ('invalid restorer join', q))
        p = PRIMES[edges[0][1]]
        sig_restorer[p] += 1
        extra_controls += 2 * p + 2
        symbol_counts.update({'Z': 1, 'P': p + 1, '-': 1, '+': p})
    counts = {'controls': control_count + extra_controls, 'rows': sum(symbol_counts.values()),
              'symbols': dict(sorted(symbol_counts.items()))}
    return sig_source, sig_restorer, counts


def reconstruct_prime(five_rows, cert):
    """Rebuild complete edge multiset; certificate names are checked against rows."""
    sources = grouped(five_rows, 0)
    incoming = grouped(five_rows, 3)
    restores = cert['restoration']
    wanted_restores = {q for q, es in incoming.items() if es[0][2] in ('Z', 'P')}
    require(set(restores) == wanted_restores, 'Restorer coverage')
    require({a['source'] for a in cert['prime']} == set(sources) and
            len(cert['prime']) == len(sources), 'Prime source coverage')
    result = []
    for item in cert['prime']:
        q, prefix = item['source'], item['prefix']
        edges = sources[q]
        p = PRIMES[edges[0][1]]
        sym = edges[0][2]
        require(item['kind'] == ('test' if sym in ('Z', 'P') else sym), 'Prime kind')
        if sym == '0':
            require(len(edges) == 1, 'Identity arity')
            result.append((q, 0, '0', edges[0][3]))
            continue
        require(item['prime'] == p, 'Prime number')
        if sym in ('+', '-'):
            require(len(edges) == 1, 'Move arity')
            st = lambda j: prefix + 'S' + str(j)
            c = lambda j: prefix + 'C' + str(j)
            result.extend([
                (q, 1, 'Z', st(1)), (st(1), 0, 'Z', st(5)),
                (st(1), 0, 'P', st(2)), (st(2), 0, '-', st(3)),
                (st(3), 1, '+', st(4)), (st(4), 1, 'P', st(1)),
                (st(5), 1, 'Z', edges[0][3]),
                (st(7), 0, 'P', st(5)),
            ])
            if sym == '+':
                result.extend([(st(5), 1, 'P', st(6)), (st(6), 1, '-', c(0))])
                result.extend((c(j), 0, '+', c(j + 1) if j + 1 < p else st(7)) for j in range(p))
            else:
                result.append((st(5), 1, 'P', c(0)))
                result.extend((c(j), 1, '-', c(j + 1) if j + 1 < p else st(6)) for j in range(p))
                result.append((st(6), 0, '+', st(7)))
        else:
            ts = {e[2]: e[3] for e in edges}
            require(item['targets'] == ts, 'Test destinations')
            st = lambda j, k: prefix + f'R{j}T{k}'
            result.append((q, 1, 'Z', st(0, 1)))
            for j in range(p):
                branch = 'P' if j == 0 else 'Z'
                if branch in ts:
                    t = ts[branch]
                    result.append((st(j, 1), 0, 'Z', restores[t]['prefix'] + f'R{j}T1'))
                result.extend([(st(j, 1), 0, 'P', st(j, 2)), (st(j, 2), 0, '-', st(j + 1, 1))])
            result.extend([(st(p, 1), 1, '+', st(p, 2)), (st(p, 2), 1, 'P', st(0, 1))])
    for q, item in restores.items():
        prefix, p = item['prefix'], item['prime']
        require(p == PRIMES[incoming[q][0][1]], 'Restorer prime')
        st = lambda j, k: prefix + f'R{j}T{k}'
        result.extend([(st(0, 1), 1, 'Z', q), (st(0, 1), 1, 'P', st(0, 2)),
                       (st(0, 2), 1, '-', st(p, 1))])
        for j in range(1, p + 1):
            result.extend([(st(j, 1), 0, '+', st(j, 2)), (st(j, 2), 0, 'P', st(j - 1, 1))])
    return result


def literal_clock_trace(out, start, n, boundaries, limit=10000):
    q, regs = start, [n, 0]
    moving, energy, stationary, steps = 0, 0, 0, 0
    while not steps or q not in boundaries:
        es = [e for e in out.get(q, ()) if enabled(e[2], regs[e[1]])]
        if not es:
            return q, tuple(regs), moving, energy, stationary, steps, False
        require(len(es) == 1, ('Nondeterminism', q, regs))
        _, i, symbol, target = es[0]
        change = delta(symbol)
        if change:
            energy += abs((regs[i] + change) ** 2 - regs[i] ** 2)
            moving += 1
        else:
            stationary += 1
        regs[i] += change
        q = target
        steps += 1
        require(steps <= limit, ('Literal trace budget', start, n))
    return q, tuple(regs), moving, energy, stationary, steps, True


def macro_components(symbol, p, n):
    """Expected coefficients of lambda, constant quadratic part, stationary count."""
    q = n // p
    if symbol == '0':
        return 0, 0, 1
    if symbol == '+':
        return (p + 3) * n, (p * p + 3) * n * n, 4 * n + 3
    if symbol == '-':
        require(n % p == 0, 'Disabled decrement cost requested')
        return 3 * n + q, 3 * n * n + q * q, 2 * n + 2 * q + 3
    return 2 * (n + q), 2 * (n * n + q * q), 2 * (n + q) + 3


def macro_clock(symbol, p, n, lam):
    moves, quadratic, zero = macro_components(symbol, p, n)
    return moves * lam + quadratic + zero


def suffix_ops(k, h, bit):
    """Exact recorder suffix operation word, with encoded pre-values."""
    H, W = h, 0
    answer = []
    def op(i, symbol):
        nonlocal H, W
        n = k * 7 ** H * 11 ** W
        require(enabled(symbol, H if i == 3 else W), ('Disabled suffix', H, W, i, symbol))
        answer.append((i, symbol, n))
        if i == 3:
            H += delta(symbol)
        else:
            W += delta(symbol)
    op(4, 'Z')
    for _ in range(h):
        for i, s in ((3, 'P'), (3, '-'), (4, '+'), (4, 'P')):
            op(i, s)
    op(3, 'Z')
    if bit:
        op(3, '+'); op(3, 'P')
    for _ in range(h):
        for i, s in ((4, 'P'), (4, '-'), (3, '+'), (3, 'P'), (3, '+'), (3, 'P')):
            op(i, s)
    op(4, 'Z')
    require((H, W) == (2 * h + bit, 0), 'Suffix output')
    return answer


def embedding(h, d, high_bit, low_bit):
    """Return the lower-word operation indices' order-preserving high indices."""
    require(d > 0 or (d == 0 and (high_bit, low_bit) == (1, 0)), 'Embedding domain')
    pairs = [(0, 0)] + [(1 + j, 1 + j) for j in range(4 * h)]
    pairs.append((1 + 4 * h, 1 + 4 * (h + d)))
    low_prep, high_prep = 2 + 4 * h, 2 + 4 * (h + d)
    high_double = high_prep + 2 * high_bit
    if low_bit:
        to = high_prep if high_bit else high_double + 2
        pairs.extend((low_prep + j, to + j) for j in (0, 1))
    low_double = low_prep + 2 * low_bit
    pairs.extend((low_double + j, high_double + 6 * d + j) for j in range(6 * h + 1))
    return pairs


def audit_embedding(lam):
    comparisons = matched = 0
    for k, h in product((1, 13, 30), range(13)):
        cases = [(d, a, b) for d in range(1, 7) for a, b in product(range(2), repeat=2)] + [(0, 1, 0)]
        for d, a, b in cases:
            low, high = suffix_ops(k, h, b), suffix_ops(k, h + d, a)
            pairs = embedding(h, d, a, b)
            require([i for i, j in pairs] == list(range(len(low))), 'Lower embedding coverage')
            require(all(pairs[i][1] < pairs[i+1][1] for i in range(len(pairs)-1)), 'Embedding not ordered')
            for i, j in pairs:
                lo, hi = low[i], high[j]
                require(lo[:2] == hi[:2] and lo[2] <= hi[2], ('Bad embedded operations', lo, hi))
                require(macro_clock(lo[1], PRIMES[lo[0]], lo[2], lam) <=
                        macro_clock(hi[1], PRIMES[hi[0]], hi[2], lam), 'Bad embedded cost')
            require(len(high) > len(low), 'No strict unmatched operations')
            lo_cost = sum(macro_clock(s, PRIMES[i], n, lam) for i, s, n in low)
            hi_cost = sum(macro_clock(s, PRIMES[i], n, lam) for i, s, n in high)
            require(lo_cost < hi_cost, 'Recorder clock non-strict')
            comparisons += 1
            matched += len(low)
    return {'comparisons': comparisons, 'matched_primitive_operations': matched}


def audit_startup(normal, cert, lam, tm_boundary):
    out = defaultdict(list)
    for row in normal['rows']:
        out[row['source']].append(row)
    target_to_pair = {c['target']: c for c in cert['history']}
    @lru_cache(None)
    def suffix_clock(k, h, b):
        return sum(macro_clock(s, PRIMES[i], n, lam) for i, s, n in suffix_ops(k, h, b))
    inputs = comparisons = boundary_checks = 0
    recorded_empty = None
    for l, r, t, c, h0 in product(range(2), range(2), range(4), (1, 13), range(2)):
        q, data, trace = normal['start'], [l, r, t], []
        first = {}
        while q != tm_boundary:
            es = [e for e in out[q] if enabled(e['symbol'], data[e['counter']])]
            require(len(es) == 1, 'Normalized startup determinism')
            e = es[0]
            old_factor = c * 2 ** data[0] * 3 ** data[1] * 5 ** data[2]
            data[e['counter']] += delta(e['symbol'])
            new_factor = c * 2 ** data[0] * 3 ** data[1] * 5 ** data[2]
            pair = e['target'] if e['target'] in target_to_pair else None
            if pair is not None:
                first.setdefault(pair, e['name'])
            trace.append((e, old_factor, new_factor, pair))
            q = e['target']
            require(len(trace) < 100, 'Startup budget')
        require(len(first) == 6, 'Startup pair count')
        require(set(first.values()) == {'entry', 'v0000z', 'n0001e0', 'n0001e1', 'n0001e2', 'n0001e3'},
                'Startup first encounters')
        pair_number = {pair: i for i, pair in enumerate(first)}
        def arrival(mask):
            hist, clock, result = h0, 0, []
            for e, old_k, new_k, pair in trace:
                clock += macro_clock(e['symbol'], PRIMES[e['counter']], old_k * 7 ** hist, lam)
                if pair is not None:
                    bit = int(first[pair] != e['name']) ^ ((mask >> pair_number[pair]) & 1)
                    clock += suffix_clock(new_k, hist, bit)
                    hist = 2 * hist + bit
                result.append((hist, clock))
            return result
        best = arrival(0)
        if (l, r, t, c, h0) == (0, 0, 0, 1, 0):
            recorded_empty = best[-1][1]
        for mask in range(64):
            candidate = arrival(mask)
            encountered_difference = False
            for j, (_, _, _, pair) in enumerate(trace):
                if pair is not None and ((mask >> pair_number[pair]) & 1):
                    encountered_difference = True
                if encountered_difference:
                    require(best[j][0] < candidate[j][0] and best[j][1] < candidate[j][1],
                            ('Startup strictness', l, r, t, c, h0, mask, j))
                else:
                    require(best[j] == candidate[j], 'Startup equality')
                boundary_checks += 1
            comparisons += 1
        inputs += 1
    require(recorded_empty == 1394018396, 'Frozen empty startup CA-clock mismatch')
    return {'inputs': inputs, 'orientation_comparisons': comparisons, 'boundary_comparisons': boundary_checks,
            'empty_startup_CA_clock': recorded_empty, 'suffix_cache_entries': suffix_clock.cache_info().currsize}


def run(OLD):
    verify_inputs()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt', type=Path, default=HERE / 'receipt.json')
    args = parser.parse_args()
    names = ('normalized3.json', 'reversible5.json', 'reversible2-primitives.json', 'certificates.json',
             'source.json')
    paths = {label + '/' + name: root / name for label, root in (('optimized', OPT), ('regenerated-baseline', OLD)) for name in names}
    for name in ('target-ledger.json', 'compiler-reference/reversible_binary.py', 'compiler-reference/COMPILER_PROOF.md'):
        paths['optimized/' + name] = OPT / name
    before = {label: sha(path) for label, path in paths.items()}
    normal, five, two, cert, source = [read(OPT, n) for n in names[:5]]
    require(sha(OPT / 'source.json') == 'fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3', 'Optimized source pin')
    for machine, reverse in ((normal, False), (five, True), (two, True)):
        structural_checks(machine, reverse)
    normal_in = defaultdict(list)
    for row in normal['rows']:
        normal_in[row['target']].append(row)
    require(all(len(es) <= 2 for es in normal_in.values()), 'Normalized indegree bound')
    collision_targets = {q for q, es in normal_in.items() if len(es) == 2 and not compatible_pair([edge(e) for e in es])}
    require({c['target'] for c in cert['history']} == collision_targets and len(cert['history']) == len(collision_targets),
            'Collision-pair coverage')
    for item in cert['history']:
        require(len(item['incoming']) == 2 and set(item['incoming']) == {e['name'] for e in normal_in[item['target']]},
                'Pair orientation is not a bijection on the actual incoming pair')
    five_rows = [edge(e) for e in five['rows']]
    require(Counter(reconstruct_history(normal, cert)) == Counter(five_rows), 'Complete history graph mismatch')
    two_rows = [edge(e) for e in two['rows']]
    require(Counter(reconstruct_prime(five_rows, cert)) == Counter(two_rows), 'Complete prime graph mismatch')
    by_name = {r['name']: r for r in two['rows']}
    require(len(source['branches']) == len(by_name), 'Serialized branch coverage')
    for row in source['branches']:
        old = by_name[row['name']]
        s = old['symbol']
        expected_guard = {'op': 'true'} if s in ('0', '+') else {'op': 'eq' if s == 'Z' else 'gt', 'counter': old['counter'], 'value': 0}
        require((row['source'], row['target'], row['side'], row['delta'], row['guard']) ==
                (old['source'], old['target'], -1 if old['counter'] == 0 else 1, delta(s), expected_guard),
                'Serialized branch mismatch')
    require(set(two['controls']) == set(five['controls']) | {q for e in two_rows for q in (e[0], e[3])},
            'Literal control coverage')
    sig_source, sig_restorer, counts = history_signature_and_literal_counts(five_rows, len(five['controls']))
    require(counts == {'controls': len(two['controls']), 'rows': len(two_rows),
                       'symbols': dict(sorted(Counter(e[2] for e in two_rows).items()))}, 'Template-ledger mismatch')
    for item in cert['history']:
        candidate = reconstruct_history(normal, cert, frozenset([item['target']]))
        require(history_signature_and_literal_counts(candidate, len(five['controls'])) ==
                (sig_source, sig_restorer, counts), ('Single-flip count mismatch', item['target']))
    all_targets = frozenset(a['target'] for a in cert['history'])
    require(history_signature_and_literal_counts(reconstruct_history(normal, cert, all_targets), len(five['controls'])) ==
            (sig_source, sig_restorer, counts), 'All-flipped count mismatch')
    old_five, old_cert = read(OLD, 'reversible5.json'), read(OLD, 'certificates.json')
    structural_checks(old_five, True)
    require(read(OLD, 'normalized3.json') == normal, 'Predecessor normalization changed')
    old_rows = [edge(e) for e in old_five['rows']]
    require(Counter(reconstruct_history(normal, old_cert)) == Counter(old_rows), 'Predecessor recorder mismatch')
    require(history_signature_and_literal_counts(old_rows, len(old_five['controls'])) ==
            (sig_source, sig_restorer, counts), 'Predecessor counts differ')
    m, p, a, J = len(source['controls']), sum(bool(e['delta']) for e in source['branches']), sum(not e['delta'] for e in source['branches']), source['class_cut']
    D = 2 * m + 4 * p
    S, Z = 2 * D + 2, 40 * D + 60 + 2 * J
    lam = 3 + 2 * Z - 4 * S
    require(lam == 72 * D + 115 + 4 * J == 36684691, 'Lambda')
    require((m, p, a, J) == (122622, 66066, 75495, 0), 'Compiler inputs')
    symbols = counts['symbols']
    cells = {'B': 4 * (symbols['0'] + symbols['+']) + 2 * (symbols['Z'] + symbols['P'] + symbols['-']),
             'r': 4 * (symbols['0'] + symbols['+']) + symbols['Z'] + 3 * (symbols['P'] + symbols['-']),
             'P': 4 * symbols['+'] + 2 * symbols['-']}
    require(cells == {'B': 350054, 'r': 411291, 'P': 199004}, 'Class-cell counts')
    pair, triple, contextual = 4 * p, 8 * p * D + 23 * p + m, 2 * p + a
    factors = pair + triple + contextual
    radius = pair * (6 * D + 8) + triple * (24 * D + 32) + contextual * (Z + J + 12 * D + 16)
    ledger = read(OPT, 'target-ledger.json')
    require((factors, radius) == (ledger['factors'], ledger['radius']), 'Compiler resource ledger')
    out, boundaries = grouped(two_rows, 0), set(five['controls'])
    prime_cases = disabled = raw_rows = 0
    for item in cert['prime']:
        kind, prime = item['kind'], item.get('prime', 2)
        for n in sorted({1, prime - 1, prime, prime + 1, 2 * prime, 2 * prime + 1, 3 * prime + 2}):
            success_expected = kind != '-' or n % prime == 0
            target = item.get('target')
            if kind == 'test':
                target = item['targets'].get('P' if n % prime == 0 else 'Z')
                success_expected = target is not None
            got = literal_clock_trace(out, item['source'], n, boundaries)
            raw_rows += got[5]
            require(got[-1] == success_expected, ('Macro enablement', item, n, got))
            if not success_expected:
                disabled += 1
                continue
            expected_n = prime * n if kind == '+' else n // prime if kind == '-' else n
            require(got[:2] == (target, (expected_n, 0)), ('Macro output', item, n, got))
            require(got[2:5] == macro_components(kind, prime, n), ('Macro clock coefficients', item, n, got))
            prime_cases += 1
    # Exact finite monotonicity corroboration, including the floor discontinuities.
    monotone = 0
    for prime in PRIMES:
        for kind in ('0', '+', '-', 'test'):
            ns = list(range(prime, 501, prime)) if kind == '-' else list(range(1, 501))
            for n1, n2 in zip(ns, ns[1:]):
                require(macro_clock(kind, prime, n1, lam) <= macro_clock(kind, prime, n2, lam), 'Monotonicity')
                monotone += 1
    embed = audit_embedding(lam)
    tm_boundary = read(OPT, 'dependency/virtual3.json')['tm_cuts']['A0']
    startup = audit_startup(normal, cert, lam, tm_boundary)
    # Traverse the actual frozen serialized two-counter startup, independently.
    q, regs, micro, steps = source['start'], [1, 0], 0, 0
    while q != tm_boundary:
        choices = [e for e in out[q] if enabled(e[2], regs[e[1]])]
        require(len(choices) == 1, 'Startup literal determinism')
        _, i, s, target = choices[0]
        change = delta(s)
        micro += 1 if not change else lam + abs((regs[i] + change) ** 2 - regs[i] ** 2)
        regs[i] += change
        q, steps = target, steps + 1
        require(steps < 10000, 'Empty startup literal budget')
    require((steps, micro, regs) == (138, 1394018396, [1, 0]), 'Actual startup mismatch')
    after = {label: sha(path) for label, path in paths.items()}
    require(before == after, 'Frozen inputs changed during audit')
    receipt = {'status': 'PASS', 'mode_policy': 'Executed separately under normal and -O by run_checks.py',
               'independence': 'No producer clock checker imported; complete pinned graphs reconstructed independently; baseline materialized by its pinned generator; no CA compiled or evaluated',
               'source_sha256': before['optimized/source.json'], 'lambda': lam,
               'compiler_counts': {'m': m, 'p': p, 'a': a, 'J': J, 'D': D, 'S': S, 'Z': Z},
               'class_cell_counts': cells, 'compiler_factors': factors, 'compiler_radius_bound': radius,
               'source_group_signature': [{'prime': k[0], 'symbols': k[1], 'count': v} for k, v in sorted(sig_source.items())],
               'restorer_prime_signature': dict(sorted(sig_restorer.items())),
               'literal_graph_counts': counts, 'single_pair_flips_checked': len(cert['history']),
               'global_primitive_determinism_and_reversibility_checked': True,
               'all_pairs_flipped_checked': True, 'predecessor_checked': True,
               'prime_macro_enabled_traces': prime_cases, 'prime_macro_disabled_traces': disabled,
               'literal_rows_traversed_in_macro_tests': raw_rows, 'finite_monotonicity_pairs': monotone,
               'recorder_embeddings': embed, 'startup_comparisons': startup,
               'empty_startup_literal_traversal': {'rows': steps, 'derived_CA_clock': micro},
               'frozen_inputs_unchanged': before == after, 'frozen_input_sha256': before,
               'checker_sha256': sha(Path(__file__))}
    args.receipt.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'frozen_input_sha256'}, indent=2))


def main():
    with regenerated_baseline() as baseline:
        run(baseline)


if __name__ == '__main__':
    main()
