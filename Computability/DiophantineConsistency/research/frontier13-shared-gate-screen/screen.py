#!/usr/bin/env python3
"""Screen a bounded two-target shared-intermediate rewrite family.

Samples reject possibilities only. The two reported local identities are
separately proved by exact sparse polynomial arithmetic below.
"""
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

if not __debug__:
    raise RuntimeError('this certificate requires Python assertions enabled')

RESEARCH = Path(__file__).resolve().parent.parent
INPUTS = (
    ('adaptive-square-sums/candidate.json', '11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828', 87),
    ('adaptive-direct-ordinate86/candidate.json', 'e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f', 86),
)
P = 2305843009213693951
SEED = 459893
LITERALS = (0, 1, 2, 3, 4)


def op(kind, left, right):
    if kind == '+': return tuple((a+b) % P for a, b in zip(left, right))
    if kind == '-': return tuple((a-b) % P for a, b in zip(left, right))
    if kind == '*': return tuple(a*b % P for a, b in zip(left, right))
    raise ValueError(kind)


def cost(rows, output, changes=()):
    table = {row[0]: row for row in rows}
    for row in changes: table[row[0]] = row
    live, todo = set(), [output]
    while todo:
        name = todo.pop()
        if not isinstance(name, str) or name in live: continue
        live.add(name)
        if name in table: todo.extend(table[name][2:])
    kept = [row for name, row in table.items() if name in live]
    return len(kept), sum(row[1] == '*' for row in kept)


def live_nodes(rows, output, changes=()):
    table = {row[0]: row for row in rows}
    for row in changes: table[row[0]] = row
    live, todo = set(), [output]
    while todo:
        name = todo.pop()
        if not isinstance(name, str) or name in live: continue
        live.add(name)
        if name in table: todo.extend(table[name][2:])
    return live


def normalize(graph):
    """Previously documented G linearization: same polynomial, fewer multiplies."""
    g = copy.deepcopy(graph)
    for i, row in enumerate(g['source']):
        if row[0] == 'g44': g['source'][i] = ['g44', '-', 'q2', 'g28']
        if row[0] == 'G': g['source'][i] = ['G', '-', 'g44', 'C']
    return g


def scan(graph):
    rows, output = graph['source'], graph['output']
    inputs = graph['witnesses'] + graph['fixed_numerals']
    assert len(inputs) == len(set(inputs))
    assert 'CROSS_TEMP' not in inputs and all(r[0] != 'CROSS_TEMP' for r in rows)
    baseline = cost(rows, output)
    assert baseline[0] == len(rows)
    rng = random.Random(SEED)
    values = {n: tuple(rng.randrange(2, P-1) for _ in range(3)) for n in inputs}
    values.update({str(n): (n, n, n) for n in LITERALS})
    available = list(values)
    prefixes, needs, targets = [], [], []
    inverse = {}

    # For each target and each earlier z, find signatures t satisfying
    # target=t+z, t-z, z-t or t*z. Later target operands may depend on the
    # earlier target; preserving that target's polynomial preserves them.
    for target, kind, left, right in rows:
        assert target not in values and kind in ('+', '-', '*')
        wanted = op(kind, values[str(left)], values[str(right)])
        assert wanted != (0, 0, 0), ('zero target sample', target)
        options = {}
        for z in available:
            v = values[z]
            alternatives = [('+', op('-', wanted, v), False),
                            ('-', op('+', wanted, v), False),
                            ('-', op('-', v, wanted), True)]
            if z == '0':
                assert v == (0, 0, 0)
            else:
                assert all(v), ('zero divisor sample', target, z)
                if v not in inverse: inverse[v] = tuple(pow(x, -1, P) for x in v)
                alternatives.append(('*', op('*', wanted, inverse[v]), False))
            for final, signature, reverse in alternatives:
                options.setdefault(signature, []).append((final, z, reverse))
        prefixes.append(list(available)); needs.append(options); targets.append(wanted)
        values[target] = wanted; available.append(target)

    pairs, selfmap = {}, {}
    def add(name, previous):
        for earlier in previous + [name]:
            for kind, a, b in (('+', earlier, name), ('*', earlier, name),
                               ('-', earlier, name), ('-', name, earlier)):
                signature = op(kind, values[a], values[b])
                if signature not in pairs:
                    for final in ('+', '*'):
                        selfmap.setdefault(op(final, signature, signature), set()).add((signature, final))
                pairs.setdefault(signature, []).append((kind, a, b))

    for i, name in enumerate(prefixes[0]): add(name, prefixes[0][:i])
    counts, findings = Counter(), []
    for i, first in enumerate(rows):
        if i:
            add(rows[i-1][0], prefixes[i-1])
        aliases = {}
        for name in prefixes[i]: aliases.setdefault(values[name], []).append(name)
        for j in range(i+1, len(rows)):
            second = rows[j]
            self_i = {sig for sig, _ in selfmap.get(targets[i], set())}
            self_j = {sig for sig, _ in selfmap.get(targets[j], set())}
            signatures = ((needs[i].keys() | self_i) & (needs[j].keys() | self_j) & pairs.keys())
            for sig in signatures:
                choices_i = needs[i].get(sig, []) + [(kind, None, False) for key, kind in selfmap.get(targets[i], set()) if key == sig]
                choices_j = needs[j].get(sig, []) + [(kind, None, False) for key, kind in selfmap.get(targets[j], set()) if key == sig]
                # Either compute one new shared t or refer directly to any
                # earlier alias with the same sampled signature. Include all
                # aliases, not just one representative.
                shared = [(['CROSS_TEMP', kind, a, b], 'CROSS_TEMP') for kind, a, b in pairs[sig]]
                shared += [(None, name) for name in aliases.get(sig, ())]
                for temp, name in shared:
                    for ki, zi, ri in choices_i:
                        ai, bi = (name, name) if zi is None else ((zi, name) if ri else (name, zi))
                        for kj, zj, rj in choices_j:
                            aj, bj = (name, name) if zj is None else ((zj, name) if rj else (name, zj))
                            changes = [[first[0], ki, ai, bi], [second[0], kj, aj, bj]]
                            if temp is not None: changes.insert(0, temp)
                            counts['sampled_programs'] += 1
                            actual = cost(rows, output, changes)
                            if actual[0] < baseline[0] or (actual[0] == baseline[0] and actual[1] < baseline[1]):
                                findings.append({'first': first[0], 'second': second[0],
                                                 'changes': changes, 'gates': actual[0],
                                                 'multiplications': actual[1]})
    findings.sort(key=lambda item: json.dumps(item, sort_keys=True))
    return {'gates': baseline[0], 'multiplications': baseline[1],
            'sampled_programs': counts['sampled_programs'], 'findings': findings}


# Exact Z[q,F,alpha] proof of both local targets in each reported pattern.
def exact_identities():
    def add(a, b, sign=1):
        out = dict(a)
        for k, v in b.items(): out[k] = out.get(k, 0) + sign*v
        return {k: v for k, v in out.items() if v}
    def mul(a, b):
        out = {}
        for x, v in a.items():
            for y, w in b.items():
                k = tuple(i+j for i, j in zip(x, y)); out[k] = out.get(k, 0) + v*w
        return {k: v for k, v in out.items() if v}
    one={(0,0,0):1}; q={(1,0,0):1}; f={(0,1,0):1}; alpha={(0,0,1):1}
    qf=add(q,f,-1); c=add(qf,alpha,-1); q2=mul(q,q); fq=mul(f,q)
    old_g44=mul(qf,add(q,one,-1)); old_g=add(alpha,old_g44)
    shared=mul(q,qf)
    assert add(q2,shared,-1)==fq
    assert add(shared,c,-1)==old_g
    shared2=add(q2,fq,-1)
    assert add(shared2,qf,-1)==old_g44
    assert add(shared2,c,-1)==old_g
    # A sign error must be caught in the exact local certificate.
    assert add(shared,c)!=old_g


def main():
    exact_identities()
    result = []
    for rel, pin, size in INPUTS:
        raw = (RESEARCH / rel).read_bytes()
        assert hashlib.sha256(raw).hexdigest() == pin
        graph = json.loads(raw)
        assert len(graph['witnesses']) == 13 and len(graph['source']) == size
        by_name = {row[0]: row for row in graph['source']}
        for row in (['qm','*','J','beta'], ['q','+',1,'qm'], ['q2','*','q','q'],
                    ['qF','-','q','F'], ['C','-','qF','alpha'], ['g28','*','F','q'],
                    ['g44','*','qF','qm'], ['G','+','alpha','g44']):
            assert by_name[row[0]] == row
        assert [row[0] for row in graph['source'] if 'g44' in row[2:]] == ['G']
        original, rewritten = scan(graph), scan(normalize(graph))
        assert original['gates'] == rewritten['gates'] == size
        assert rewritten['multiplications'] == original['multiplications'] - 1
        assert not rewritten['findings']
        # The only sampled improvements in the original are the two exact
        # forms of the already documented G linearization.
        assert len(original['findings']) == 2
        assert {(x['first'], x['second']) for x in original['findings']} == {('g28','G'), ('g44','G')}
        expected_changes = [
            [['CROSS_TEMP','*','q','qF'], ['g28','-','q2','CROSS_TEMP'], ['G','-','CROSS_TEMP','C']],
            [['CROSS_TEMP','-','q2','g28'], ['g44','-','CROSS_TEMP','qF'], ['G','-','CROSS_TEMP','C']],
        ]
        assert {json.dumps(x['changes']) for x in original['findings']} == {json.dumps(x) for x in expected_changes}
        assert all(x['gates'] == size and x['multiplications'] == rewritten['multiplications'] for x in original['findings'])
        interface = set(graph['witnesses'] + graph['fixed_numerals'])
        assert interface <= live_nodes(graph['source'], graph['output'])
        assert interface <= live_nodes(normalize(graph)['source'], graph['output'])
        for finding in original['findings']:
            assert interface <= live_nodes(graph['source'], graph['output'], finding['changes'])
        result.append({'graph': rel, 'sha256': pin, 'original': original, 'normalized': rewritten})

    # Detect a genuine cross-target improvement: both xz+yz and xw+yw
    # share t=x+y. Original DAG uses seven live operations, replacement four.
    toy = {'witnesses':['x','y','z','w'], 'fixed_numerals':[],
           'source':[['a','*','x','z'], ['b','*','y','z'], ['i','+','a','b'],
                     ['c','*','x','w'], ['d','*','y','w'], ['j','+','c','d'],
                     ['out','+','i','j']], 'output':'out'}
    control = scan(toy)
    assert any(x['gates'] < control['gates'] for x in control['findings'])
    # Exercise a pre-existing alias instead of inserting a shared gate.
    alias_toy = {'witnesses':['x','y','z','w'], 'fixed_numerals':[],
                 'source':[['t','+','x','y'], ['a','*','x','z'], ['b','*','y','z'],
                           ['i','+','a','b'], ['c','*','x','w'], ['d','*','y','w'],
                           ['j','+','c','d'], ['h','+','i','j'], ['out','+','h','t']],
                 'output':'out'}
    alias_control = scan(alias_toy)
    assert any(x['gates'] < alias_control['gates'] and len(x['changes']) == 2
               for x in alias_control['findings'])
    # Exercise shared t=x+y used twice in each of two replacement targets.
    self_toy = {'witnesses':['x','y'], 'fixed_numerals':[],
                'source':[['x2','*','x','x'], ['xy','*','x','y'], ['y2','*','y','y'],
                          ['twoxy','*',2,'xy'], ['s','+','x2','twoxy'], ['i','+','s','y2'],
                          ['twox','*',2,'x'], ['twoy','*',2,'y'], ['j','+','twox','twoy'],
                          ['out','+','i','j']], 'output':'out'}
    self_control = scan(self_toy)
    assert any(x['gates'] < self_control['gates'] and len(x['changes']) == 3 and
               all(row[2] == row[3] == 'CROSS_TEMP' for row in x['changes'][1:])
               for x in self_control['findings'])
    print(json.dumps({'status':'PASS_SHARED_GATE_SCREEN', 'modulus':P, 'seed':SEED,
                      'samples':3, 'literals':list(LITERALS), 'graphs':result,
                      'positive_control_findings':len(control['findings']),
                      'alias_control_findings':len(alias_control['findings']),
                      'self_control_findings':len(self_control['findings'])}, sort_keys=True))


if __name__ == '__main__': main()
