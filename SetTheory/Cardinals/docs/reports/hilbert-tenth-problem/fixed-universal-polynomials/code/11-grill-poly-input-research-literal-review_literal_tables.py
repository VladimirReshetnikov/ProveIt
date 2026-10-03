# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Independent finite audit; parses frozen upstream literals but never executes them.
Uses only the literal packet for simulations. No builder imports.
"""
from pathlib import Path
from collections import Counter, deque
import ast, hashlib, json, random
P = Path(__file__).resolve().parent
packet = json.loads((P / 'literal_tables.json').read_text())
upstream = ast.parse((P / 'upstream_u15_builder.py.txt').read_text())
assignment = next((n for n in upstream.body if isinstance(n, ast.Assign) and any((isinstance(t, ast.Name) and t.id == 'TABLES' for t in n.targets))))
source = ast.literal_eval(assignment.value)['15,2']
source = {a: row.split() for a, row in source.items()}
if not packet['u15_table_tokens'] == source:
    raise RuntimeError('Invariant failed at original source line 13')
if not (source['b'][9] == '-' and sum((t != '-' for row in source.values() for t in row)) == 29):
    raise RuntimeError('Invariant failed at original source line 14')
expected_states = []
for u in range(1, 16):
    for read, a in enumerate(('c', 'b')):
        token = source[a][u - 1]
        rec = {'id': 2 * (u - 1) + read, 'u15_state': u, 'read': read, 'accepting': token == '-'}
        if token != '-':
            target = int(token[2:])
            rec.update(write=int(token[0] == 'b'), direction=token[1], next_if_zero=2 * target - 2, next_if_one=2 * target - 1)
        expected_states.append(rec)
if not packet['refined_states'] == expected_states:
    raise RuntimeError('Invariant failed at original source line 23')
if not [s['id'] for s in expected_states if s['accepting']] == [19]:
    raise RuntimeError('Invariant failed at original source line 24')
if not packet['genera']['input_contract']['start_refined_state'] == 0:
    raise RuntimeError('Invariant failed at original source line 25')
T = packet['tag']
ta = {r['name']: r['id'] for r in T['alphabet']}
tn = {v: k for k, v in ta.items()}
if not len(ta) == len(tn) == len(T['alphabet']) == 570:
    raise RuntimeError('Invariant failed at original source line 27')
if not sorted(tn) == list(range(570)):
    raise RuntimeError('Invariant failed at original source line 28')
rows = {p['symbol']: p for p in T['productions']}
if not (len(rows) == len(T['productions']) == 570 and set(rows) == set(tn)):
    raise RuntimeError('Invariant failed at original source line 30')
tr = {tn[i]: [tn[k] for k in row['output']] for i, row in rows.items()}
roles = {tn[i]: row['role'] for i, row in rows.items()}
expected = {}
eroles = {}

def check(lhs, rhs, role):
    if not (lhs not in expected or expected[lhs] == rhs):
        raise RuntimeError('Invariant failed at original source line 35')
    if not tr[lhs] == rhs:
        raise RuntimeError((lhs, tr[lhs], rhs))
    if not roles[lhs] == role:
        raise RuntimeError((lhs, roles[lhs], role))
    expected[lhs] = rhs
    eroles[lhs] = role
for st in expected_states:
    i = st['id']
    n = lambda a: f'{a}:{i:02d}'
    x = n('x')
    if st['accepting']:
        check(n('A'), ['HALT'], 'accepting_head')
        for a in ('a', 'B', 'b'):
            check(n(a), ['INERT', 'INERT'], 'halt_state_inert')
    else:
        w = st['write']
        left = st['direction'] == 'L'
        if left:
            check(n('A'), [n('L'), x], 'left_prepare')
            check(n('a'), [n('l'), x], 'left_prepare')
            check(n('B'), [n('C'), x] + [n('c'), x] * w, 'left_double')
            check(n('b'), [n('c'), x] * 2, 'left_double')
            check(n('L'), [n('S')], 'left_shrink')
            check(n('l'), [n('s')], 'left_shrink')
        else:
            check(n('A'), [n('C'), x] + [n('c'), x] * w, 'right_double')
            check(n('a'), [n('c'), x] * 2, 'right_double')
            check(n('B'), [n('S')], 'right_shrink')
            check(n('b'), [n('s')], 'right_shrink')
        for a, pair in {'C': ['D1', 'D0'], 'c': ['d1', 'd0'], 'S': ['T1', 'T0'], 's': ['t1', 't0']}.items():
            check(n(a), [n(t) for t in pair], 'parity_prepare')
        for bit in (0, 1):
            j = st['next_if_one' if bit else 'next_if_zero']
            s = lambda a: f'{a}:{j:02d}'
            xx = s('x')
            ah, al, bh, bl = ('Bp', 'bp', 'A', 'a') if left else ('A', 'a', 'B', 'b')
            check(n('D' + str(bit)), ([xx] if bit == 0 else []) + [s(ah), xx], 'parity_select')
            check(n('d' + str(bit)), [s(al), xx], 'parity_select')
            check(n('T' + str(bit)), [s(bh), xx], 'parity_finish')
            check(n('t' + str(bit)), [s(bl), xx], 'corrected_even_finish' if bit == 0 else 'parity_finish')
            if left:
                check(s('Bp'), [s('B'), xx], 'left_rotate')
                check(s('bp'), [s('b'), xx], 'left_rotate')
    check(n('x'), ['INERT', 'INERT'], 'unreachable_filler_totalization')
check('INERT', ['INERT', 'INERT'], 'inert')
check('HALT', ['INERT', 'INERT'], 'ignored_after_acceptance')
if not (expected == tr and eroles == roles):
    raise RuntimeError('Invariant failed at original source line 66')
if not (T['deletion'] == 2 and T['accepting_symbol'] == ta['HALT'] and (T['inert_symbol'] == ta['INERT'])):
    raise RuntimeError('Invariant failed at original source line 67')
if not [(a, w) for a, w in tr.items() if 'HALT' in w] == [('A:19', ['HALT'])]:
    raise RuntimeError('Invariant failed at original source line 68')
for i in range(30):
    if not T['canonical_symbols'][str(i)] == {k: ta[f'{k}:{i:02d}'] for k in ('A', 'a', 'B', 'b', 'x')}:
        raise RuntimeError('Invariant failed at original source line 70')
if not T['halt_event'] == {'kind': 'fresh_H_emitted_by_accepting_head', 'source': ta['A:19'], 'accepting_refined_state': 19, 'not_short_word_halting': True}:
    raise RuntimeError('Invariant failed at original source line 71')
G = packet['genera']
ga = {r['name']: r['id'] for r in G['alphabet']}
gn = {v: k for k, v in ga.items()}
gr = {r['id']: r for r in G['alphabet']}
if not len(ga) == len(gn) == len(gr) == len(G['alphabet']) == 1013:
    raise RuntimeError('Invariant failed at original source line 73')
if not sorted(gr) == list(range(1013)):
    raise RuntimeError('Invariant failed at original source line 74')
if not (G['modulus'] == 2 and G['initial_phase'] == 0):
    raise RuntimeError('Invariant failed at original source line 75')
originals = set(tr) - {'HALT'}
padding = 'DUMMY'
want_pairs = {(padding, padding)}
for name in originals:
    w = tr[name] + [padding] * (4 - len(tr[name]))
    want_pairs |= {tuple(w[:2]), tuple(w[2:])}
actual_pairs = {tuple((gn[x] for x in r['expands'])): r['id'] for r in gr.values() if r['kind'] == 'pair'}
if not len(actual_pairs) == len(want_pairs) == 442:
    raise RuntimeError('Invariant failed at original source line 81')
if not set(actual_pairs) == want_pairs:
    raise RuntimeError('Invariant failed at original source line 82')
if not Counter((r['kind'] for r in gr.values())) == {'original': 569, 'dummy': 1, 'pair': 442, 'halt': 1}:
    raise RuntimeError('Invariant failed at original source line 83')
for pair, pid in actual_pairs.items():
    r = gr[pid]
    v = [ga[x] for x in pair]
    if not (r['width'] == 0 and r['productions'] == [v, v]):
        raise RuntimeError('Invariant failed at original source line 86')
for name in originals:
    r = gr[ga[name]]
    w = tr[name] + [padding] * (4 - len(tr[name]))
    dd = actual_pairs[padding, padding]
    if not (r['kind'] == 'original' and r['width'] == 1):
        raise RuntimeError('Invariant failed at original source line 89')
    if not r['productions'] == [[actual_pairs[tuple(w[:2])], actual_pairs[tuple(w[2:])]], [dd, dd]]:
        raise RuntimeError('Invariant failed at original source line 90')
if not (gr[ga[padding]]['width'] == 0 and gr[ga[padding]]['productions'] == [[ga[padding], ga[padding]]] * 2):
    raise RuntimeError('Invariant failed at original source line 91')
if not (gr[ga['HALT']]['width'] == 0 and gr[ga['HALT']]['productions'] == [[ga['INERT'], ga['INERT']]] * 2):
    raise RuntimeError('Invariant failed at original source line 92')
if not (gr[ga['HALT']]['ignored_by_halt_semantics'] and G['ignored_halt_row_is_total']):
    raise RuntimeError('Invariant failed at original source line 93')
if not all((len(p) == 2 and all((x in gr for x in p)) for r in gr.values() for p in r['productions'])):
    raise RuntimeError('Invariant failed at original source line 94')
if not sorted(G['original_symbols']) == sorted((ga[x] for x in originals)):
    raise RuntimeError('Invariant failed at original source line 95')
if not (G['dummy_symbol'] == ga[padding] and G['halt_symbol'] == ga['HALT'] and (G['inert_symbol'] == ga['INERT'])):
    raise RuntimeError('Invariant failed at original source line 96')
for i in range(30):
    if not G['canonical_symbols'][str(i)] == {k: ga[f'{k}:{i:02d}'] for k in ('A', 'a', 'B', 'b', 'x')}:
        raise RuntimeError('Invariant failed at original source line 98')
hpairs = [pid for pair, pid in actual_pairs.items() if 'HALT' in pair]
if not (len(hpairs) == 1 and ('HALT', padding) in actual_pairs):
    raise RuntimeError('Invariant failed at original source line 100')
if not G['halt_metadata'] == dict(accepting_refined_state=19, accepting_head=ga['A:19'], halt_pair=hpairs[0], first_H_layer='pair_expansion', unique_H_on_valid_canonical_runs=True, hypothetical_prefix_cannot_emit_H=True, initial_H_forbidden=True, multiple_H_outside_contract=True):
    raise RuntimeError('Invariant failed at original source line 101')
if not [(n, p) for n, r in gr.items() if r['kind'] != 'pair' for p in r['productions'] if ga['HALT'] in p] == []:
    raise RuntimeError('Invariant failed at original source line 102')
if not sum((hpairs[0] in p for r in gr.values() for p in r['productions'])) == 1:
    raise RuntimeError('Invariant failed at original source line 103')
counts = packet['counts']
if not counts['tag_symbols'] == counts['tag_productions'] == 570:
    raise RuntimeError('Invariant failed at original source line 104')
if not (counts['genera_symbols'] == 1013 and counts['genera_nonhalt_symbols'] == 1012):
    raise RuntimeError('Invariant failed at original source line 105')
if not (counts['genera_production_rows'] == 2026 and counts['genera_nonhalt_production_rows'] == 2024):
    raise RuntimeError('Invariant failed at original source line 106')
if not (counts['genera_pair_symbols'] == 442 and counts['genera_width_zero'] == 444 and (counts['genera_width_one'] == 569)):
    raise RuntimeError('Invariant failed at original source line 107')
if not (counts['refined_left'] == 15 and counts['refined_right'] == 14):
    raise RuntimeError('Invariant failed at original source line 108')
if not (counts['u15_states'] == 15 and counts['u15_instructions'] == 29 and (counts['refined_states'] == 30) and (counts['refined_nonhalt_instructions'] == 29)):
    raise RuntimeError('Invariant failed at original source line 109')
if not counts['tag_output_length_histogram'] == {str(k): v for k, v in sorted(Counter(map(len, tr.values())).items())}:
    raise RuntimeError('Invariant failed at original source line 110')
if not counts['tag_role_counts'] == dict(Counter(roles.values())):
    raise RuntimeError('Invariant failed at original source line 111')
if not (counts['corrected_grill_phase_count_if_emitted'] == 397488 and counts['corrected_grill_E_width_for_initial_symbols'] == 198744):
    raise RuntimeError('Invariant failed at original source line 112')
if not counts['arithmetic_history_emitted'] is False:
    raise RuntimeError('Invariant failed at original source line 113')

def canonical(i, m, n):
    s = lambda k: f'{k}:{i:02d}'
    return [s('A'), s('x')] + [s('a'), s('x')] * m + [s('B'), s('x')] + [s('b'), s('x')] * n

def independent_tape_step(i, m, n):
    u, read = (i // 2 + 1, i % 2)
    tape = {0: read}
    for value, side in ((m, -1), (n, 1)):
        offset = 1
        while value:
            tape[side * offset] = value % 2
            value //= 2
            offset += 1
    token = source[('c', 'b')[read]][u - 1]
    if not token != '-':
        raise RuntimeError('Invariant failed at original source line 127')
    tape[0] = int(token[0] == 'b')
    head = {'R': 1, 'L': -1}[token[1]]
    nextstate = 2 * (int(token[2:]) - 1) + tape.get(head, 0)
    leftvalue = sum((bit * (1 << head - pos - 1) for pos, bit in tape.items() if pos < head))
    rightvalue = sum((bit * (1 << pos - head - 1) for pos, bit in tape.items() if pos > head))
    return (nextstate, leftvalue, rightvalue)
macro_cases = steps_total = 0
minimum = 10 ** 9
max_steps = 0
all_active = set()
halt_incoming = 0
for i in range(30):
    if i == 19:
        continue
    for m in range(25):
        for n in range(25):
            j, mm, nn = independent_tape_step(i, m, n)
            want = canonical(j, mm, nn)
            q = deque(canonical(i, m, n))
            steps = 0
            while True:
                if not len(q) >= 2:
                    raise RuntimeError((i, m, n, steps, 'short queue'))
                first = q.popleft()
                q.popleft()
                if not (first != 'HALT' and (not first.startswith('x:')) and (first != 'INERT')):
                    raise RuntimeError((i, m, n, first))
                if first.startswith('A:'):
                    if not steps == 0:
                        raise RuntimeError((i, m, n, steps, 'premature canonical head', first))
                all_active.add(first)
                q.extend(tr[first])
                steps += 1
                minimum = min(minimum, len(q))
                if list(q) == want:
                    break
                if not steps < 5000:
                    raise RuntimeError((i, m, n, steps, 'no boundary'))
            if not (len(q) >= 4 and 'HALT' not in q):
                raise RuntimeError('Invariant failed at original source line 146')
            if j == 19:
                halt_incoming += 1
                q.popleft()
                q.popleft()
                q.extend(tr['A:19'])
                if not list(q).count('HALT') == 1:
                    raise RuntimeError('Invariant failed at original source line 149')
                if not all((x not in ('A:19', 'Bp:19') for x in q)):
                    raise RuntimeError('Invariant failed at original source line 150')
            steps_total += steps
            macro_cases += 1
            max_steps = max(max_steps, steps)
unused = {'HALT', 'INERT', 'A:19', 'a:19', 'B:19', 'b:19'} | {f'x:{i:02d}' for i in range(30)}
if not all_active == set(tr) - unused:
    raise RuntimeError('Invariant failed at original source line 154')

def norm_gen(word, phase):
    out = []
    for name in word:
        r = gr[ga[name]]
        out.extend((gn[x] for x in r['productions'][phase]))
        phase = (phase + r['width']) % 2
    return (out, phase)

def unnorm_gen(word, phase):
    out = []
    for name in word:
        if name == padding:
            continue
        if not name != 'HALT':
            raise RuntimeError('Invariant failed at original source line 167')
        if phase == 0:
            out.extend(tr[name])
        phase ^= 1
    return (out, phase)

def check_projection(word, phase):
    expected, p = unnorm_gen(word, phase)
    layer1, p1 = norm_gen(word, phase)
    layer2, p2 = norm_gen(layer1, p1)
    if not ([x for x in layer2 if x != padding] == expected and p2 == p):
        raise RuntimeError((word, phase))
    if not all((gr[ga[x]]['kind'] in ('pair', 'dummy') for x in layer1)):
        raise RuntimeError('Invariant failed at original source line 175')
    return (layer2, p2)
projection_cases = 0
for name in sorted(originals):
    for phase in (0, 1):
        for word in ([name], [padding, name], [name, padding], [padding, name, padding]):
            check_projection(word, phase)
            projection_cases += 1
for phase in (0, 1):
    check_projection([padding] * 3, phase)
    projection_cases += 1
rng = random.Random(271828)
base = sorted(originals) + [padding]
for _ in range(1000):
    check_projection([rng.choice(base) for _ in range(rng.randrange(1, 30))], rng.randrange(2))
    projection_cases += 1
row_trace_cases = 0
max_trace_word = 0
for i in range(30):
    for m, n in ((0, 0), (0, 1), (1, 0), (1, 1), (2, 3), (3, 2)):
        word = canonical(i, m, n)
        phase = 0
        for _ in range(3):
            if 'HALT' in word:
                break
            word, phase = check_projection(word, phase)
            row_trace_cases += 1
            max_trace_word = max(max_trace_word, len(word))
halt_runs = 0
max_halt_layer = 0
max_halt_word = 0
prefix_symbols = 0
for i in (19, 17):
    for m in range(4):
        if i == 17 and m % 2 == 0:
            continue
        for n in range(4):
            word = canonical(i, m, n)
            phase = 0
            layers = 0
            while 'HALT' not in word:
                word, phase = norm_gen(word, phase)
                layers += 1
                if not (layers <= 18 and word):
                    raise RuntimeError((i, m, n, layers))
            if not word.count('HALT') == 1:
                raise RuntimeError((i, m, n, 'multiple H'))
            hpos = word.index('HALT')
            prefix = word[:hpos]
            if not all((gr[ga[x]]['kind'] in ('original', 'dummy') for x in prefix)):
                raise RuntimeError('Invariant failed at original source line 210')
            hypothetic, _ = norm_gen(prefix, phase)
            if not 'HALT' not in hypothetic:
                raise RuntimeError('Invariant failed at original source line 211')
            halt_runs += 1
            max_halt_layer = max(max_halt_layer, layers)
            max_halt_word = max(max_halt_word, len(word))
            prefix_symbols += len(prefix)
manifest = json.loads((P / 'source_manifest.json').read_text())
for f in manifest['files']:
    b = (P / f['file']).read_bytes()
    if not (len(b) == f['bytes'] and hashlib.sha256(b).hexdigest() == f['sha256']):
        raise RuntimeError('Invariant failed at original source line 216')
if not hashlib.sha256((P / 'build_literal.py').read_bytes()).hexdigest() == manifest['builder_sha256']:
    raise RuntimeError('Invariant failed at original source line 217')
if not hashlib.sha256((P / 'literal_tables.json').read_bytes()).hexdigest() == manifest['literal_tables_sha256']:
    raise RuntimeError('Invariant failed at original source line 218')
result = dict(status='PASS', upstream_executed=False, u15_primary_image_manually_checked=True, literal_sha256=manifest['literal_tables_sha256'], builder_sha256=manifest['builder_sha256'], static_tag_rules_checked=len(tr), static_genera_phase_rules_checked=2 * len(gr), pairs_unique=len(actual_pairs), tag_macro_cases=macro_cases, tag_steps=steps_total, macro_M_range=[0, 24], macro_N_range=[0, 24], actual_nonhalt_rows=29, minimum_poststep_preaccept_queue_length=minimum, max_macro_steps=max_steps, distinct_active_tag_symbols=len(all_active), tested_macros_entering_accept=halt_incoming, two_generation_projection_cases=projection_cases, consecutive_real_row_projection_cases=row_trace_cases, maximum_row_trace_word_length=max_trace_word, normalized_first_H_runs=halt_runs, maximum_normalized_layers_to_H=max_halt_layer, maximum_first_H_word_length=max_halt_word, hypothetical_prefix_symbols_checked=prefix_symbols, no_correction_found=True, scope='Finite literal table and bounded semantic audit; no arithmetic or history circuit emitted')
(P / 'review_literal_tables_result.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
