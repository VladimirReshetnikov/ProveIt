#!/usr/bin/env python3
"""Independent finite source/graph review; imports no builder or symbolic runtime.

The CFG resolver uses leaf intervals of tree prefixes. Macro expansion uses a
small parser of the literal Lean tree definitions, not the supplied compiler.
This does not independently prove physical instruction simulation or PA.
"""
from pathlib import Path
import ast
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
INP = ROOT / 'inputs'
OLD = tuple(map(int, '10101001'))
NEW = tuple(map(int, '100101001'))

def require(condition, message):
    if not condition:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def get(name):
    return json.loads((INP / name).read_text())

def load_sites(name):
    raw = get(name)
    if isinstance(raw[0], dict):
        return [(tuple(map(int, r['path'])), r['op'], r['arg']) for r in raw]
    if len(raw[0]) == 2:
        return [(tuple(p), op[0], op[1] if len(op) == 2 else None) for p, op in raw]
    return [(tuple(p), op, arg) for p, op, arg in raw]

def resolve(sites):
    """Resolve successors independently by intervals of all prefix subtrees."""
    paths = [p for p, op, arg in sites]
    require(paths == sorted(paths) and len(set(paths)) == len(paths), 'leaf order/uniqueness')
    leaves = set(paths)
    intervals = {}
    for i, p in enumerate(paths):
        require(all(b in (0, 1) for b in p), 'nonbinary path')
        for k in range(len(p) + 1):
            prefix = p[:k]
            require(k == len(p) or prefix not in leaves, 'leaf has descendants')
            intervals.setdefault(prefix, [i, i])[1] = i
    for prefix in intervals:
        require(prefix in leaves or (prefix + (0,) in intervals and prefix + (1,) in intervals),
                'tree has a missing child')

    def ancestor(p, bit, depth):
        positions = [i for i, b in enumerate(p) if b == bit]
        require(0 < depth <= len(positions), 'invalid branch-depth command')
        return p[:positions[-depth]]

    code = []
    for i, (p, op, arg) in enumerate(sites):
        if op == 'inc':
            row = ('inc', arg, i + 1)
        elif op == 'dec':
            row = ('dec', arg, intervals[ancestor(p, 0, 1)][1] + 1, i + 1)
        elif op == 'breakTo':
            row = ('jump', i + 1 if arg == 0 else intervals[ancestor(p, 0, arg)][1] + 1)
        elif op == 'continueTo':
            row = ('jump', i if arg == 0 else intervals[ancestor(p, 1, arg)][0])
        elif op == 'halt':
            row = ('halt',)
        else:
            raise ValueError('Unknown opcode: ' + op)
        for target in targets(row):
            require(0 <= target < len(sites), 'source edge outside program')
        code.append(row)
    return code

def targets(row):
    return row[2:] if row[0] in ('inc', 'dec') else row[1:]

def read_machine(path):
    rows = {}
    for line in path.read_text().splitlines():
        line = line.split('#')[0].strip()
        if not line:
            continue
        q, b, w, d, t = line.split()
        q, b, w, t = map(int, (q, b, w, t))
        require((q, b) not in rows and b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'bad machine row')
        rows[q, b] = (w, d, t)
    states = {q for q, b in rows}
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'partial table')
    return rows

def canonical(rows, start):
    states = {q for q, b in rows}
    mapping, pending, serial = {start: 0}, [start], []
    for q in pending:
        for b in (0, 1):
            w, d, t = rows[q, b]
            if t not in states:
                nt = -1
            else:
                if t not in mapping:
                    mapping[t] = len(mapping)
                    pending.append(t)
                nt = mapping[t]
            serial.append([mapping[q], b, w, d, nt])
    return digest(json.dumps(serial, separators=(',', ':')).encode()), len(mapping)

def bisimulation(rows):
    states = sorted({q for q, b in rows})
    part = {q: 0 for q in states}
    while True:
        signatures, refined = {}, {}
        for q in states:
            key = tuple((rows[q, b][0], rows[q, b][1], part.get(rows[q, b][2], -1)) for b in (0, 1))
            signatures.setdefault(key, len(signatures))
            refined[q] = signatures[key]
        if refined == part:
            return len(signatures)
        part = refined

def parse_definitions():
    definitions = {}
    for line in (INP / 'Program.lean').read_text().splitlines():
        match = re.fullmatch(r'def (\w+) : Tree := (.*)', line)
        if not match:
            continue
        tokens = re.findall(r'\(|\)|\.\w+|\w+', match[2])
        pos = 0
        def expr():
            nonlocal pos
            tok = tokens[pos]
            pos += 1
            if tok == '(':
                out = expr()
                require(tokens[pos] == ')', 'unbalanced Tree expression')
                pos += 1
                return out
            if tok == '.node':
                return (expr(), expr())
            if tok == '.leaf':
                require(tokens[pos] == '(', 'leaf instruction syntax')
                pos += 1
                op = tokens[pos][1:]
                pos += 1
                arg = None
                if tokens[pos] != ')':
                    arg = int(tokens[pos])
                    pos += 1
                require(tokens[pos] == ')', 'instruction close')
                pos += 1
                return ('leaf', op, arg)
            require(tok in definitions, 'undefined Tree reference: ' + tok)
            return tok
        definitions[match[1]] = expr()
        require(pos == len(tokens), 'unparsed Tree expression')
    return definitions

def expand_grammar(name, definitions):
    data = get(name)
    rules = data['rules']
    def walk(item, prefix, active):
        if isinstance(item, str):
            require(item not in active, 'cyclic grammar')
            lookup = rules if item in rules else definitions
            require(item in lookup, 'undefined grammar reference')
            return walk(lookup[item], prefix, active | {item})
        if len(item) == 3 and item[0] == 'leaf':
            return [(prefix, item[1], item[2])]
        require(len(item) == 2, 'invalid grammar pair')
        return walk(item[0], prefix + (0,), active) + walk(item[1], prefix + (1,), active)
    return walk(data['root'], NEW, set())

def macro_word(name):
    data = get(name)
    names = {'node49': 'push', 'node55': 'copyD', 'node58': 'copyH',
             'node70': 'copyA', 'node65': 'cons', 'node72': 'readH',
             'node75': 'readDCons', 'node142': 'copyGuard', 'node150': 'compareGuard'}
    def walk(x):
        if x == 'node60':
            return ['incT', 'incT']
        if x == 'node61':
            return ['incT'] * 4
        if isinstance(x, str):
            return [names[x]] if x in names else walk(data['rules'][x])
        if x == ['leaf', 'inc', 1]:
            return ['incT']
        if x == ['leaf', 'breakTo', 1]:
            return ['close']
        require(len(x) == 2, 'unsupported macro leaf')
        return walk(x[0]) + walk(x[1])
    return walk(data['root'])

def emission(word, separate):
    """Free-constructor check; arithmetic aliases cannot invalidate an identity."""
    zero, one = ('z',), ('s', ('z',))
    inc = lambda a: ('s', a)
    imp = lambda a, b: ('i', a, b)
    mem = lambda a, b: inc(imp(a, b))
    univ = lambda a, b: inc(inc(imp(b, a)))
    eq = lambda a, b: inc(inc(inc(imp(a, b))))
    neg = lambda a: imp(a, one)
    conj = lambda a, b: neg(imp(a, neg(b)))
    exists = lambda a, b: neg(univ(a, neg(b)))
    t, a, d, h, x, y = map(lambda s: ('v', s), 'tadhxy')
    top, D, H, stack, fields = t, d, h, [], [y, x]
    require(word[-3:] == ['copyGuard', 'compareGuard', 'close'], 'changed guard/cleanup')
    for token in word[:-3]:
        if token == 'push':
            stack.append(top)
            top = zero
        elif token in ('copyA', 'copyD', 'copyH'):
            stack.append(top)
            top = {'copyA': a, 'copyD': D, 'copyH': H}[token]
        elif token == 'incT':
            top = inc(top)
        elif token == 'cons':
            top = imp(stack.pop(), top)
        elif token == 'readH':
            H = ('+', H, fields.pop(0))
        elif token == 'readDCons':
            D = ('+', D, fields.pop(0))
            top = imp(top, D)
        else:
            raise ValueError('Unexpected token')
    require(fields == [], 'operand reads not exhausted')
    heads = [imp(exists(D, univ(D, H)), H), imp(univ(D, univ(a, H)), univ(a, univ(D, H))),
             imp(mem(H, D), imp(eq(H, a), mem(a, D))), imp(eq(H, D), imp(mem(a, H), mem(a, D))),
             exists(D, eq(H, D)), imp(univ(D, a), imp(univ(D, imp(a, H)), univ(D, H)))]
    rho = imp(imp(imp(H, d), D), imp(imp(D, H), imp(a, H)))
    gamma = imp(a, univ(a, a))
    v = imp(mem(H, D), univ(a, mem(H, D)))
    point = imp(a, mem(a, D))
    sep = univ(D, conj(imp(mem(H, D), point), imp(mem(a, D), a)))
    Q = univ(a, imp(sep, neg(point)))
    expected = [t, univ(d, h), rho] + heads + ([gamma] if separate else [])
    wanted_top = neg(imp(v, Q)) if separate else neg(imp(gamma, imp(v, Q)))
    require(stack == expected and top == wanted_top, 'free-algebra AX result differs')
    return {'macro_items': len(word), 'pushed_including_saved_top': len(stack),
            'free_algebra_identity': True, 'guard_and_cleanup_unchanged': True}

def full_startup(rows, labels, source_path, steps=57922):
    head = -2
    target = {head - 1, head + 48} | {head + i for i, bit in enumerate(source_path) if bit}
    pos = head + 49
    for value in [0, 0, 0, 0, 0, 0, 2, 0, 0] + [1] * 26:
        pos += 1
        target.update(range(pos, pos + value + 1))
        pos += value + 1
    tape, q, h = set(), 0, 0
    for _ in range(steps):
        w, d, q = rows[q, int(h in tape)]
        (tape.add if w else tape.discard)(h)
        h += 1 if d == 'R' else -1
    require(labels[q] == 84 and h == head and tape == target, 'whole-tape startup differs')
    return {'steps': steps, 'head': h, 'native_root': labels[q], 'whole_tape_equal': True}

def main():
    for entry in json.loads((ROOT / 'input_manifest.json').read_text()):
        require(digest((INP / entry['file']).read_bytes()) == entry['sha256'], 'changed input: ' + entry['file'])
    combined = load_sites('combined_sites.json')
    C = resolve(combined)
    cinside = [i for i, (p, op, arg) in enumerate(combined) if p[:len(NEW)] == NEW]
    cset = set(cinside)
    cout = {p: i for i, (p, op, arg) in enumerate(combined) if i not in cset}
    require(len(cout) == 145 and cinside == list(range(50, 3693)), 'Combined AX/exterior split')
    return_targets = {j for i in cinside for j in targets(C[i]) if j not in cset}
    require(return_targets == {3776}, 'Combined command-return interface')
    return_path = combined[3776][0]
    enter_targets = {j for i in cout.values() for j in targets(C[i]) if j in cset}
    require(enter_targets == {50}, 'Combined AX entry interface')
    labels_old = ast.literal_eval(re.search(r'def labels : List Nat := (\[[^\n]+\])', (INP/'Conjugacy.lean').read_text())[1])
    cdense = read_machine(INP / 'combined.tm')
    cnative = {(labels_old[q], b): (w, d, labels_old[t]) for (q, b), (w, d, t) in cdense.items()}
    definitions = parse_definitions()
    old_word = [x[0] for x in re.findall(r'\(\.(\w+), (\d+), (\d+)\)', (INP/'AXProgram.lean').read_text().split('def program')[0])]
    require(len(old_word) == 201, 'baseline AX macro word')
    prior_hashes = {e['canonical_sha256'] for e in get('prior_selected196.json')['tables']}
    records = []
    for number, kind in enumerate(('diagonal', 'separate')):
        prefix = 'candidate_' + str(number) + '_'
        sites = load_sites(prefix + 'sites.json')
        S = resolve(sites)
        bypath = {p: i for i, (p, op, arg) in enumerate(sites)}
        inside = [i for i, (p, op, arg) in enumerate(sites) if p[:len(NEW)] == NEW]
        inset = set(inside)
        outside = {p: i for i, (p, op, arg) in enumerate(sites) if i not in inset}
        require(set(outside) == set(cout), 'exterior source addresses changed')
        for p, i in cout.items():
            ni = outside[p]
            require(sites[ni][1:] == combined[i][1:], 'exterior opcode changed')
            narg = 2 if C[i][0] in ('inc', 'dec') else 1
            mapped = tuple(inside[0] if j in cset else outside[combined[j][0]] for j in targets(C[i]))
            require(S[ni] == C[i][:narg] + mapped, 'exterior resolved edge changed')
        reference = load_sites(kind + '_sites.json')
        R = resolve(reference)
        supplied = get(kind + '_sites.json')
        require(all(list(row) == supplied[i]['instruction'] for i, row in enumerate(R)), 'reference CFG recomputation differs')
        ref_inside = [i for i, (p, op, arg) in enumerate(reference) if p[:len(OLD)] == OLD]
        ref_set = set(ref_inside)
        require(len(inside) == len(ref_inside), 'AX length changed')
        require([sites[i] for i in inside] == expand_grammar(prefix + 'grammar.json', definitions), 'literal macro expansion differs')
        ref_exits = {j for i in ref_inside for j in targets(R[i]) if j not in ref_set}
        require(len(ref_exits) == 1, 'reference AX has multiple command exits')
        for oi, ni in zip(ref_inside, inside):
            opath, op, arg = reference[oi]
            require(sites[ni] == (NEW + opath[len(OLD):], op, arg), 'AX primitive source binding differs')
            narg = 2 if R[oi][0] in ('inc', 'dec') else 1
            mapped = tuple(j - ref_inside[0] + inside[0] if j in ref_set else bypath[return_path] for j in targets(R[oi]))
            require(S[ni] == R[oi][:narg] + mapped, 'AX resolved edge/return binding differs')
        word = macro_word(prefix + 'grammar.json')
        expected_word = old_word[:121] + ['copyA'] * 3 + ['cons', 'incT', 'incT', 'cons'] + old_word[138:]
        if kind == 'separate':
            require(expected_word[184] == 'cons', 'wrong separated-head deletion position')
            del expected_word[184]
        require(word == expected_word, 'macro word differs from specified calculus change')
        emitted = emission(word, kind == 'separate')
        dense = read_machine(INP / (prefix + 'machine.tm'))
        native = read_machine(INP / (prefix + 'machine.native.tm'))
        labels = get(prefix + 'labels.json')
        require(len(labels) == len(set(labels)) == 197 and labels[0] == 74 and labels[-1] == 254, 'bad dense/native map')
        require(set(dense) == {(q,b) for q in range(196) for b in (0,1)}, 'dense working-state domain')
        require({(labels[q], b):(w,d,labels[t]) for (q,b),(w,d,t) in dense.items()} == native, 'dense/native conjugacy differs')
        fixed = {key for key in native if key[0] < 1300}
        require(len(fixed) == 268, 'fixed exterior control count')
        changes = [key for key in sorted(fixed) if native[key] != cnative[key]]
        require(changes == [(101,1)], 'fixed machine controls changed outside AX-entry redirect')
        h, reachable = canonical(dense, 0)
        require(reachable == 196 and h not in prior_hashes, 'old graph or unreachable working state')
        records.append({'candidate': number, 'kind': kind, 'source_sites': len(sites),
                        'AX_sites': len(inside), 'exterior_sites': len(outside),
                        'all_source_edges_checked': sum(map(lambda row:len(targets(row)), S)),
                        'command_return_ordinal': bypath[return_path], 'macro_emission': emitted,
                        'working_states': len(dense)//2, 'graph_reachable_states': reachable,
                        'action_bisimulation_classes': bisimulation(dense), 'canonical_sha256': h,
                        'table_sha256': digest((INP/(prefix+'machine.tm')).read_bytes()),
                        'startup': full_startup(dense, labels, sites[25][0])})
    require(records[0]['canonical_sha256'] != records[1]['canonical_sha256'], 'new graphs coincide')
    print(json.dumps({'status':'PASS', 'imports_builder_or_symbolic_executor':False,
                     'scope':'Exact component source, resolved-CFG, emitter, conjugacy, startup, and graph facts. Physical runtime contracts and arithmetic interpretation remain separately proved components.',
                     'records':records}, indent=2))

if __name__ == '__main__':
    main()
