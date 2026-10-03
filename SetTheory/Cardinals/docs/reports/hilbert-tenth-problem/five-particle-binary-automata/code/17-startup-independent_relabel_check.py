#!/usr/bin/env python3
"""Independent optimization audit. Reads literal artifacts; never imports builders.
Writes only independent-relabel-receipt.json beside this script. Explicit checks
remain active under python -O. Invariant proofs are in independent-relabel-audit.md.
"""
from verify_pins import verify_inputs
verify_inputs()
import ast
from collections import Counter, defaultdict
import hashlib
import itertools
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent
from baseline_support import regenerated_baseline
PRIMES = (2, 3, 5, 7, 11)
FILES = ('dependency/virtual3.json', 'primitive3.json', 'normalized3.json',
         'reversible5.json', 'reversible2-primitives.json', 'source.json', 'certificates.json')
ZERO = {'entry', 'v0000z', 'n0001e0', 'n0001e1', 'n0001e2', 'n0001e3'}
SWAPS = {'n0001_1': ('n0001e0', 'v0028'), 'n0001_2': ('n0001e1', 'v0066'),
         'n0001_3': ('n0001e2', 'v0155'), 'tm_A0_pop0': ('n0001e3', 'v0303z')}

def require(test, detail):
    if not test:
        raise AssertionError(detail)

def hashes(root):
    return {name: hashlib.sha256((root / name).read_bytes()).hexdigest() for name in FILES}

def read(root, name):
    return json.loads((root / name).read_text())

def groups(rows, field):
    result = defaultdict(list)
    for row in rows:
        result[row[field]].append(row)
    return result

def edge(row):
    return tuple(row[k] for k in ('source', 'counter', 'symbol', 'target'))

def complementary(a, b):
    return a['counter'] == b['counter'] and {a['symbol'], b['symbol']} == {'Z', 'P'}

def structural(machine, reversible):
    controls, rows = machine['controls'], machine['rows']
    require(len(controls) == len(set(controls)), 'Repeated control')
    require(len(rows) == len({e['name'] for e in rows}) == len({edge(e) for e in rows}), 'Repeated edge')
    require(set(controls) == {machine['start'], machine['halt']} | {q for e in rows for q in (e['source'], e['target'])}, 'Control coverage')
    require(not any(e['target'] == machine['start'] for e in rows), 'Incoming START')
    require(not any(e['source'] == machine['halt'] for e in rows), 'Outgoing HALT')
    require(all(type(e['counter']) is int and 0 <= e['counter'] < machine['counters'] and e['symbol'] in ('0', '+', '-', 'Z', 'P') for e in rows), 'Malformed primitive')
    for field in ('source', 'target') if reversible else ('source',):
        for q, es in groups(rows, field).items():
            require(all(complementary(a, b) for a, b in itertools.combinations(es, 2)), ('Non-disjoint domains/ranges', field, q))

def exact(machine, expected, layer):
    actual, wanted = Counter(map(edge, machine['rows'])), Counter(expected)
    require(actual == wanted, (layer, 'missing', list((wanted-actual).items())[:3], 'extra', list((actual-wanted).items())[:3]))

def enabled(row, values):
    symbol, n = row['symbol'], values[row['counter']]
    return symbol in ('0', '+') or (symbol == 'Z' and n == 0) or (symbol in ('P', '-') and n > 0)

def run(graph, start, values, boundaries, budget):
    q, values = start, list(values)
    for clock in range(1, budget+1):
        candidates = [e for e in graph.get(q, ()) if enabled(e, values)]
        require(len(candidates) == 1, ('Wrong enabled-edge count', q, values, candidates))
        e = candidates[0]
        values[e['counter']] += {'+': 1, '-': -1}.get(e['symbol'], 0)
        q = e['target']
        if q in boundaries:
            return q, tuple(values), clock
    raise AssertionError(('Budget exhausted', start, values, budget))

def formula(A):
    return 76*A + 4*(A//5) + 24*(A//7) + 48*(A//11) + 62

def audit(OLD):
    original_hashes, current_hashes = hashes(OLD), hashes(ROOT)
    for name in FILES[:3]:
        require(original_hashes[name] == current_hashes[name], ('Changed dependency/source', name))
    n = read(ROOT, 'normalized3.json')
    r = read(ROOT, 'reversible5.json')
    p = read(ROOT, 'reversible2-primitives.json')
    s = read(ROOT, 'source.json')
    cert = read(ROOT, 'certificates.json')
    old_cert = read(OLD, 'certificates.json')
    structural(n, False)
    structural(r, True)
    structural(p, True)
    nr = {e['name']: e for e in n['rows']}
    incoming = groups(n['rows'], 'target')
    require(all(len(es) <= 2 for es in incoming.values()), 'Indegree > 2')
    collisions = {q for q, es in incoming.items() if len(es) == 2 and not complementary(*es)}
    records = {h['target']: h for h in cert['history']}
    old_records = {h['target']: h for h in old_cert['history']}
    require(len(records) == len(cert['history']) and set(records) == collisions == set(old_records), 'Collision coverage')
    history_private = [q for h in cert['history'] for q in h['doubling'] + [q for z in h['parts'] for q in z]]
    require(len(history_private) == len(set(history_private)) and set(history_private).isdisjoint(n['controls']), 'History private-state separation')
    changed = {}
    selected_targets = []
    expected = [edge(e) for e in n['rows'] if e['target'] not in collisions]
    for target, h in records.items():
        names, parts, d = h['incoming'], h['parts'], h['doubling']
        require(len(names) == 2 and set(names) == {e['name'] for e in incoming[target]}, ('Non-bijective tags', target))
        require(len(parts) == 2 and all(len(z) == 5 for z in parts) and len(d) == 6, 'History state arity')
        chosen = ZERO.intersection(names)
        require(len(chosen) <= 1, ('Zero-tag conflict', target))
        if chosen:
            require(names[0] in chosen, ('Wrong startup bit', target))
            selected_targets.append(target)
        canonical = [e['name'] for e in incoming[target]]
        prescribed = ([name for name in canonical if name in ZERO] + [name for name in canonical if name not in ZERO]) if chosen else canonical
        require(names == prescribed, ('Actual tags differ from independently prescribed policy', target))
        old = old_records[target]
        require(old['incoming'] == canonical, ('Frozen tags are not canonical', target))
        require(all(h[k] == old[k] for k in ('target', 'parts', 'doubling', 'prefix')), 'Non-label history change')
        if names != old['incoming']:
            require(names == list(reversed(old['incoming'])), 'Change other than swap')
            changed[target] = tuple(names)
        for bit, (name, z) in enumerate(zip(names, parts)):
            e = nr[name]
            expected.extend([(e['source'], e['counter'], e['symbol'], z[0]),
                             (z[0], 4, 'Z', z[1]), (z[1], 3, 'Z', d[0] if bit == 0 else d[4]),
                             (z[1], 3, 'P', z[2]), (z[2], 3, '-', z[3]),
                             (z[3], 4, '+', z[4]), (z[4], 4, 'P', z[1])])
        expected.extend([(d[0], 4, 'Z', target), (d[0], 4, 'P', d[1]),
                         (d[1], 4, '-', d[2]), (d[2], 3, '+', d[3]),
                         (d[3], 3, 'P', d[4]), (d[4], 3, '+', d[5]),
                         (d[5], 3, 'P', d[0])])
    require(changed == SWAPS and len(selected_targets) == len(ZERO), ('Unexpected relabel scope', changed))
    exact(r, expected, 'history')

    # Independently instantiate every arithmetic/test/restoration template from
    # its preceding literal row(s); certificate fields supply only private names.
    rg, ri = groups(r['rows'], 'source'), groups(r['rows'], 'target')
    restores = cert['restoration']
    require(set(restores) == {q for q, es in ri.items() if es[0]['symbol'] in ('Z', 'P')}, 'Restoration coverage')
    for q, c in restores.items():
        require(all(e['symbol'] in ('Z', 'P') and PRIMES[e['counter']] == c['prime'] for e in ri[q]), 'Restoration prime')
    macros = {m['source']: m for m in cert['prime']}
    require(len(macros) == len(cert['prime']) and set(macros) == set(rg), 'Prime coverage')
    expected = []
    prime_private = []
    for q, c in macros.items():
        es = rg[q]
        symbol, prime = es[0]['symbol'], PRIMES[es[0]['counter']]
        pref = c['prefix']
        require(c['rows'] == [e['name'] for e in es], 'Prime row claim')
        require(c['kind'] == ('test' if symbol in ('Z', 'P') else symbol), 'Prime kind claim')
        if symbol == '0':
            require(len(es) == 1 and c['target'] == es[0]['target'], 'Identity destination')
            expected.append((q, 0, '0', es[0]['target']))
            continue
        require(c['prime'] == prime, 'Prime claim')
        if symbol in ('+', '-'):
            require(len(es) == 1 and c['target'] == es[0]['target'], 'Arithmetic destination')
            a = lambda j: pref+'S'+str(j)
            prime_private.extend([a(j) for j in range(1, 8)] + [pref+'C'+str(j) for j in range(prime)])
            expected.extend([(q, 1, 'Z', a(1)), (a(1), 0, 'Z', a(5)), (a(1), 0, 'P', a(2)),
                             (a(2), 0, '-', a(3)), (a(3), 1, '+', a(4)), (a(4), 1, 'P', a(1)),
                             (a(5), 1, 'Z', es[0]['target'])])
            if symbol == '+':
                expected.extend([(a(5), 1, 'P', a(6)), (a(6), 1, '-', pref+'C0')])
                expected.extend((pref+'C'+str(j), 0, '+', pref+'C'+str(j+1) if j+1 < prime else a(7)) for j in range(prime))
            else:
                expected.append((a(5), 1, 'P', pref+'C0'))
                expected.extend((pref+'C'+str(j), 1, '-', pref+'C'+str(j+1) if j+1 < prime else a(6)) for j in range(prime))
                expected.append((a(6), 0, '+', a(7)))
            expected.append((a(7), 0, 'P', a(5)))
        else:
            targets = {e['symbol']: e['target'] for e in es}
            require(c['targets'] == targets, 'Test destination claim')
            a = lambda j, k: pref+'R'+str(j)+'T'+str(k)
            prime_private.extend(a(j, k) for j in range(prime+1) for k in (1, 2))
            expected.append((q, 1, 'Z', a(0, 1)))
            for j in range(prime):
                outcome = 'P' if j == 0 else 'Z'
                if outcome in targets:
                    expected.append((a(j, 1), 0, 'Z', restores[targets[outcome]]['prefix']+'R'+str(j)+'T1'))
                expected.extend([(a(j, 1), 0, 'P', a(j, 2)), (a(j, 2), 0, '-', a(j+1, 1))])
            expected.extend([(a(prime, 1), 1, '+', a(prime, 2)), (a(prime, 2), 1, 'P', a(0, 1))])
    for q, c in restores.items():
        pref, prime = c['prefix'], c['prime']
        a = lambda j, k: pref+'R'+str(j)+'T'+str(k)
        prime_private.extend(a(j, k) for j in range(prime+1) for k in (1, 2))
        expected.extend([(a(0, 1), 1, 'Z', q), (a(0, 1), 1, 'P', a(0, 2)), (a(0, 2), 1, '-', a(prime, 1))])
        for j in range(1, prime+1):
            expected.extend([(a(j, 1), 0, '+', a(j, 2)), (a(j, 2), 0, 'P', a(j-1, 1))])
    require(len(prime_private) == len(set(prime_private)) and set(prime_private).isdisjoint(r['controls']), 'Prime private-state separation')
    require(set(p['controls']) == set(r['controls']) | set(prime_private), 'Prime private-state coverage')
    exact(p, expected, 'prime')
    require(s['controls'] == p['controls'] and s['start'] == p['start'] and s['halt'] == p['halt'] and s['class_cut'] == 0, 'Serialization metadata')
    require(len(s['branches']) == len(p['rows']), 'Serialization length')
    for branch, e in zip(s['branches'], p['rows']):
        guard = {'op': 'true'} if e['symbol'] not in ('Z', 'P', '-') else {'op': 'eq' if e['symbol'] == 'Z' else 'gt', 'counter': e['counter'], 'value': 0}
        require(branch == dict(name=e['name'], source=e['source'], target=e['target'], side=-1 if e['counter'] == 0 else 1, delta={'+': 1, '-': -1}.get(e['symbol'], 0), guard=guard), 'Serialization row')

    boundaries = set(n['controls'])
    history_runs = 0
    for c in cert['history']:
        for bit, name in enumerate(c['incoming']):
            e = nr[name]
            for h in (0, 1, 7):
                v = [2, 3, 4, h, 0]
                if e['symbol'] == 'Z':
                    v[e['counter']] = 0
                wanted = v.copy()
                wanted[e['counter']] += {'+': 1, '-': -1}.get(e['symbol'], 0)
                wanted[3] = 2*h+bit
                steps = 10*h+4+2*bit
                require(run(rg, e['source'], v, boundaries, steps) == (e['target'], tuple(wanted), steps), ('History trace', name, h))
                history_runs += 1
    # Establish the entire T=0 path using actual rows, not certificate labels.
    q, v, startup, ng = 'START', [0, 0, 0, 0, 0], [], groups(n['rows'], 'source')
    stop = read(ROOT, 'dependency/virtual3.json')['tm_cuts']['A0']
    while q != stop:
        es = [e for e in rg[q] if enabled(e, v)]
        require(len(es) == 1, 'Startup determinism')
        e = es[0]
        startup.append(edge(e))
        require(e['symbol'] in ('0', 'Z'), 'Non-constant T=0 encoding')
        q = e['target']
        require(len(startup) <= 24, 'Unexpected startup loop')
    require(Counter((i, x) for _, i, x, _ in startup) == Counter({(0, '0'): 5, (2, 'Z'): 1, (3, 'Z'): 6, (4, 'Z'): 12}), 'Startup operation census')
    pg = groups(p['rows'], 'source')
    prologue_inputs = [(l, rr, c) for l, rr, c in ((0, 0, 1), (1, 0, 1), (0, 1, 1), (2, 0, 1), (1, 1, 1), (0, 2, 1), (0, 0, 13), (0, 0, 17), (1, 0, 13), (0, 3, 1), (0, 4, 1), (0, 5, 1), (0, 3, 13))]
    prologues = []
    for l, rr, c in prologue_inputs:
        A = c*2**l*3**rr
        steps = formula(A)
        require(run(pg, 'START', (A, 0), {stop}, steps) == (stop, (A, 0), steps), ('Physical prologue', A))
        prologues.append(dict(L=l, R=rr, C=c, A=A, physical_steps=steps))
    all_T = []
    for T in range(8):
        steps = 320*2**T-296-3*T
        require(run(rg, 'START', (2, 3, T, 0, 0), {stop}, steps) == (stop, (2, 3, 0, 32*(2**T-1), 0), steps), ('T formula', T))
        all_T.append(dict(T=T, H=32*(2**T-1), five_counter_steps=steps))
    # Check the monotone embedding on actual five-counter suffix traces. This
    # finite check supplements, rather than replaces, the general proof.
    def suffix_trace(h, bit, D):
        c = records['n0001_1']
        q, regs, result = c['parts'][bit][0], [0, 0, 0, h, 0], []
        while q != c['target']:
            es = [e for e in rg[q] if enabled(e, regs)]
            require(len(es) == 1, 'Suffix determinism')
            e = es[0]
            prime, symbol = PRIMES[e['counter']], e['symbol']
            encoded = D*7**regs[3]*11**regs[4]
            cost = 1 if symbol == '0' else (prime+7)*encoded+3 if symbol == '+' else 4*encoded+(prime+3)*(encoded//prime)+3 if symbol == '-' else 4*encoded+4*(encoded//prime)+3
            result.append(((e['counter'], symbol), encoded, cost))
            regs[e['counter']] += {'+': 1, '-': -1}.get(symbol, 0)
            q = e['target']
        require(regs == [0, 0, 0, 2*h+bit, 0], 'Suffix result')
        return result
    embeddings = 0
    for h, d, oldbit, newbit, D in itertools.product(range(7), range(1, 5), (0, 1), (0, 1), (1, 6, 13)):
        oldtrace, newtrace = suffix_trace(h+d, oldbit, D), suffix_trace(h, newbit, D)
        positions = list(range(1+4*h)) + [1+4*(h+d)]
        old_double = 2+4*(h+d)+2*oldbit
        if newbit:
            positions += [2+4*(h+d), 3+4*(h+d)] if oldbit else [old_double+2, old_double+3]
        positions += list(range(old_double+6*d, old_double+6*(d+h))) + [len(oldtrace)-1]
        require(len(positions) == len(newtrace) and positions == sorted(set(positions)), 'Not an order-preserving injection')
        require(all(oldtrace[j][0] == newtrace[i][0] and oldtrace[j][1] >= newtrace[i][1] and oldtrace[j][2] >= newtrace[i][2] for i, j in enumerate(positions)), 'Non-monotone matched operation')
        require(sum(t[2] for t in oldtrace) > sum(t[2] for t in newtrace), 'No strict history-clock dominance')
        embeddings += 1
    oldp = read(OLD, 'reversible2-primitives.json')
    oldpg = groups(oldp['rows'], 'source')
    companion_source = nr['v0303z']['source']
    old_companion = run(oldpg, companion_source, (1, 0), {stop}, 28)
    new_companion = run(pg, companion_source, (1, 0), {stop}, 104)
    require(old_companion == (stop, (1, 0), 28) and new_companion == (stop, (7, 0), 104), 'Tradeoff trace')
    # The public input expression is unchanged. Compare ASTs to ignore source pins.
    functions = ('natural', 'from_counters')
    def loader_functions(root):
        return {node.name: ast.dump(node, include_attributes=False) for node in ast.parse((root/'loader.py').read_text()).body if isinstance(node, ast.FunctionDef) and node.name in functions}
    require(loader_functions(ROOT) == loader_functions(OLD), 'Loader input API changed')
    require(hashes(OLD) == original_hashes and hashes(ROOT) == current_hashes, 'Artifacts changed during audit')
    receipt = dict(status='PASS', baseline_provenance='Freshly regenerated from bundled pinned historical generator; all seven historical output hashes mandatory', scope='Independent whole-row history and prime reconstruction; all-natural global syntactic injection; signed serialization; exact relabel census and startup formula; supplementary literal traces', all_input_basis='Complete row equalities plus invariants/ranks in independent-relabel-audit.md and the independently checked macro shapes; finite traces are not the unbounded proof', counts=dict(controls=len(p['controls']), physical_rows=len(p['rows']), history_pairs=len(records), changed_pairs=len(changed), selected_zero_edges=len(ZERO), history_literal_runs=history_runs, physical_prologue_literal_runs=len(prologues), actual_row_suffix_embeddings=embeddings), changed_pairs=changed, T0_formula='76*A + 4*floor(A/5) + 24*floor(A/7) + 48*floor(A/11) + 62', T0_prologues=prologues, all_T_supplement=all_T, companion_counterexample=dict(edge='v0303z', input=[1, 0], old_result=old_companion, new_result=new_companion), frozen_sha256=original_hashes, optimized_sha256=current_hashes)
    (ROOT/'independent-relabel-receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))

def main():
    with regenerated_baseline() as baseline:
        audit(baseline)

if __name__ == '__main__':
    main()
