"""Four-bit records, exact binary control quotient, and compact paired Wang code.

Every stage emits a finite literal source. The default is illustrative,
not a universal transition table or a universal arithmetic bound.
"""
import argparse
from collections import Counter, deque
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import wang_b_erasing_bridge_compiler as records

bridge = records.bridge
recoder = records.recoder
actions = bridge.actions
DEFAULT = records.DEFAULT
HALT = records.HALT
BLOCK, LEFT, RIGHT = 4, 2, 6
LOW_DECODE = (0, 1, 3, 5, 2, 9, 7, 13)


def decode_block(v):
    assert type(v) is int and 0 <= v < 16
    return LOW_DECODE[v & 7]+16*(v >> 3)


ENCODE_BLOCK = {decode_block(v): v for v in range(16)}
assert len(ENCODE_BLOCK) == 16


def abstract(table):
    """Finite alphabet restriction/relabeling of the frozen record protocol."""
    table = records.norm(table)
    if not table:
        return {}, HALT
    rows, todo = {}, deque([('start', 0)])
    while todo:
        state = todo.popleft()
        if state in rows or state == HALT:
            continue
        row = []
        for v in range(16):
            w, move, target = records.macro_step(table, state, decode_block(v))
            new = ENCODE_BLOCK[w]  # The sixteen-symbol image is closed.
            assert new | v == new and move in (-1, 0, 1)
            row.append((new, move, target))
        rows[state] = tuple(row)
        todo.extend(t for _, _, t in row if t not in rows and t != HALT)
    return rows, ('start', 0)


def binary_raw(table):
    return _binary_raw(records.norm(table))


@lru_cache(None)
def _binary_raw(table):
    macro, start = abstract(table)
    if start == HALT:
        return (), {}, macro
    target = lambda q: HALT if q == HALT else ('read', q, 0, 0)
    root = target(start)
    rules, todo = {}, deque([root])
    def walk(steps, q):
        return target(q) if steps == 0 else ('walk', steps, q)
    def action(v, w, move, q):
        if (v & 7) == (w & 7):
            steps = 4*move-3
            sign = 1 if steps > 0 else -1
            return (w >> 3, sign, walk(steps-sign, q))
        return (w >> 3, -1, ('write', w, 2, move, q))
    while todo:
        state = todo.popleft()
        if state in rules or state == HALT:
            continue
        if state[0] == 'read':
            _, q, pos, sofar = state
            row = []
            for b in (0, 1):
                v = sofar+(b << pos)
                row.append((b, 1, ('read', q, pos+1, v)) if pos < 3
                           else action(v, *macro[q][v]))
        elif state[0] == 'walk':
            _, steps, q = state
            move = 1 if steps > 0 else -1
            row = [(b, move, walk(steps-move, q)) for b in (0, 1)]
        else:
            _, w, pos, move, q = state
            if pos:
                direction, nxt = -1, ('write', w, pos-1, move, q)
            elif move:
                direction, nxt = move, walk(3*move, q)
            else:
                direction, nxt = 1, walk(-1, q)
            row = [(b | ((w >> pos) & 1), direction, nxt) for b in (0, 1)]
        rules[state] = tuple(row)
        todo.extend(q for _, _, q in row if q not in rules and q != HALT)
    ids = {s: i for i, s in enumerate(rules)}
    ids[HALT] = len(ids)
    out = tuple(tuple((b, 'R' if d == 1 else 'L', ids[q]) for b, d, q in row)
                for row in rules.values())
    assert ids[root] == 0
    bridge.normalize(out)
    return out, ids, macro


def control_quotient(table):
    """All-row Mealy bisimulation: identical writes, moves and target classes."""
    table = bridge.normalize(table)
    h = len(table)
    if not h:
        return (), (0,)
    classes = [0]*h+[1]
    for _ in range(h+1):
        signatures = [(classes[i], tuple((w, d, classes[q]) for w, d, q in row))
                      for i, row in enumerate(table)]+[('HALT',)]
        tags, new = {}, []
        for sig in signatures:
            new.append(tags.setdefault(sig, len(tags)))
        refinement = {}
        for i, c in enumerate(new):
            assert refinement.setdefault(c, classes[i]) == classes[i]
        if new == classes:
            break
        classes = new
    else:
        raise AssertionError('partition refinement did not terminate')
    order = sorted(set(classes[:h]), key=lambda c: classes.index(c))
    labels = {c: i for i, c in enumerate(order)}
    labels[classes[h]] = len(order)
    mapping = tuple(labels[c] for c in classes)
    result = tuple(tuple((w, d, mapping[q]) for w, d, q in table[classes.index(c)])
                   for c in order)
    assert mapping[0] == 0 and mapping[h] == len(result)
    assert all(mapping[i] < len(result) for i in range(h))
    for i, row in enumerate(table):
        assert result[mapping[i]] == tuple((w, d, mapping[q]) for w, d, q in row)
    return result, mapping


def binary(table):
    return _binary(records.norm(table))


@lru_cache(None)
def _binary(table):
    raw, ids, macro = binary_raw(table)
    quotient, mapping = control_quotient(raw)
    return quotient, {s: mapping[i] for s, i in ids.items()}, macro


def compile_wang(table):
    """Variable-length paired-tape expansion of an arbitrary non-erasing TM.

Pair0 is physical10, pair1 is11; entry is at the first bit. Labels are
one-based actual instruction addresses. Every branch targets a marked
first bit. A final M supplies the unique Wang fall-through halt.
"""
    table = bridge.normalize(table)
    blocks, labels, pc = [], [], 1
    for (w0, d0, t0), (_, d1, t1) in table:
        step0 = ['R'] if d0 == 'R' else ['L']*3
        step1 = ['R'] if d1 == 'R' else ['L']*3
        if d0 == d1 and t0 == t1:
            code = ([d0]*2+['M', ('to', t0)] if w0 == 0 else
                    ['R', 'M']+step0+['M', ('to', t0)])
        else:
            zero = (['M'] if w0 else [])+step0+['M', ('to', t0)]
            code = ['R', ('one', 2+len(zero))]+zero+step1+['M', ('to', t1)]
        labels.append(pc)
        blocks.append(code)
        pc += len(code)
    labels.append(pc)
    program = []
    for start, code in zip(labels, blocks):
        for instruction in code:
            if isinstance(instruction, tuple):
                kind, value = instruction
                instruction = ('J', labels[value] if kind == 'to' else start+value)
            program.append(instruction)
    program.append('M')
    return actions.parent.normalize(program), tuple(labels)


def word(x, n):
    assert 0 < x < 2**n
    blocks = [LEFT]+[1+2*((x >> i) & 1)+4*(i == 0) for i in range(n)]+[RIGHT]
    return {4*i+j for i, v in enumerate(blocks) for j in range(4) if (v >> j) & 1}


def paired_word(x, n):
    tape = word(x, n)
    return sum((1+2*int(i in tape)) << (2*i) for i in range(4*(n+2)))


def loader():
    old = recoder.build(width=8)
    extra = [('frame_repunit_multiple', '*', 255, 'frame_repunit'),
             ('frame_repeat', '*', 8182272, 'frame_repunit'),
             ('frame_data', '*', 2048, 'z'),
             ('frame_sum', '+', 'frame_repeat', 'frame_data'),
             ('frame_input', '+', 'frame_sum', 40285)]
    return dict(old, source=list(old['source'])+extra, parameters=['x'],
        auxiliaries=['z']+list(old['auxiliaries'])+['frame_repunit'],
        comparisons=list(old['comparisons'])+[('frame_repunit_multiple', 'modulus')],
        operations=old['operations']+5, multiplications=old['multiplications']+3,
        additions_subtractions=old['additions_subtractions']+2,
        witnesses=old['witnesses']+2, equations=old['equations']+1,
        input_output='frame_input')


def build(table=DEFAULT):
    table = records.norm(table)
    bt, _, _ = binary(table)
    program, labels = compile_wang(bt)
    child = actions.build(program, literal_input=True, form='units')
    load = loader()
    rn = lambda v: ('x' if v == 'x' else 'rec__'+v) if isinstance(v, str) else v
    wn = lambda v: ('rec__frame_input' if v == 'input' else 'wang__'+v) if isinstance(v, str) else v
    rename = lambda s, f: [(f(n), op, f(a), f(b)) for n, op, a, b in s]
    source = rename(load['source'], rn)+rename(child['source'], wn)
    auxiliaries = [rn(v) for v in load['auxiliaries']]+[wn(v) for v in child['auxiliaries']]
    comparisons = [(rn(a), rn(b)) for a, b in load['comparisons']]+[
        (wn(a), wn(b)) for a, b in child['comparisons']]
    actions.scale.checked_source(source, ['x'], auxiliaries)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    return dict(source=source, parameters=['x'], auxiliaries=auxiliaries,
        comparisons=comparisons, operations=len(source), multiplications=counts['M'],
        additions_subtractions=counts['A'], equations=len(comparisons), witnesses=len(auxiliaries),
        loader_packet=load, wang_packet=child, tm_table=table, binary_table=bt,
        program=program, state_labels=labels,
        scope='This fixed erasing binary TM on ordinary positive input; no universal table.')


def polynomial_source(packet):
    load, child = packet['loader_packet'], packet['wang_packet']
    ls, lo = recoder.polynomial_source(load)
    ws, wo = actions.polynomial_source(child)
    rn = lambda v: ('x' if v == 'x' else 'rec__'+v) if isinstance(v, str) else v
    wn = lambda v: ('rec__frame_input' if v == 'input' else 'wang__'+v) if isinstance(v, str) else v
    rename = lambda s, f: [(f(n), op, f(a), f(b)) for n, op, a, b in s]
    source = rename(ls, rn)+rename(ws, wn)+[
        ('complete_recoder_square', '*', rn(lo), rn(lo)),
        ('complete_wang_square', '*', wn(wo), wn(wo)),
        ('complete_output', '+', 'complete_recoder_square', 'complete_wang_square')]
    actions.scale.checked_source(source, packet['parameters'], packet['auxiliaries'])
    return source, 'complete_output'


def closed_source(source, output):
    rows = {n: (a, b) for n, _, a, b in source}
    seen, todo = set(), [output]
    while todo:
        name = todo.pop()
        if not isinstance(name, str) or name not in rows or name in seen:
            continue
        seen.add(name)
        todo.extend(rows[name])
    assert seen == set(rows)
    return len(seen)


def ledger(packet):
    source, output = polynomial_source(packet)
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    child = packet['wang_packet']
    degree = actions.parent.bounds(child)['degree_upper_bound']
    raw, _, macro = binary_raw(packet['tm_table'])
    result = dict(certificate=packet['operations'], polynomial=len(source),
        M=count['M'], A=count['A'], comparisons=packet['equations'],
        witnesses=packet['witnesses'], parameters=1,
        degree_upper_bound=2*max(348, degree),
        source_sha256=hashlib.sha256(repr(source).encode()).hexdigest(),
        output_ancestors=closed_source(source, output),
        record_controls=len(macro), binary_states_before_quotient=len(raw),
        binary_states=len(packet['binary_table']), wang_instructions=len(packet['program']),
        wang_jumps=sum(isinstance(i, tuple) for i in packet['program']),
        wang_edges=len(child['edges']), child_polynomial=len(actions.polynomial_source(child)[0]),
        child_degree_upper_bound=degree)
    assert len(packet['auxiliaries']) == len(set(packet['auxiliaries']))
    return result


def binary_step(table, state, tape, head):
    write, direction, target = table[state][int(head in tape)]
    if write:
        tape.add(head)
    else:
        tape.discard(head)
    return target, head+(1 if direction == 'R' else -1)


def wang_step(program, pc, tape, head):
    instruction = program[pc-1]
    if instruction == 'M':
        tape.add(head)
    elif instruction == 'L':
        head -= 1
    elif instruction == 'R':
        head += 1
    elif head in tape:
        return instruction[1], head
    return pc+1, head


def record_trace(table, x, n, limit, *, with_wang=False):
    """Whole physical tapes against a separately executed erasing source TM."""
    table = records.norm(table)
    raw, ids, _ = binary_raw(table)
    qt, mapping = control_quotient(raw)
    program, labels = compile_wang(qt)
    physical = word(x, n)
    state = binary_state = quotient_state = head = physical_head = 0
    source_tape = {i for i in range(n) if (x >> i) & 1}
    left, size, origin = 0, n, 0
    totals = Counter(runs=1, wang_runs=int(with_wang))
    initialized = set(range(4*(n+2)))
    wtape = {2*i for i in initialized} | {2*i+1 for i in physical}
    pc, wh = 1, 0
    for _ in range(limit):
        if state == len(table):
            break
        read = int(head in source_tape)
        write, direction, target = table[state][read]
        totals['erasures'] += int(read == 1 and write == 0)
        state, head = binary_step(table, state, source_tape, head)
        assert state == target
        totals['negative_head_steps'] += int(head < 0)
        expected = set(physical)
        expected.update(origin+4*i+3 for i in range(size+1))
        next_origin = origin+4*(size+2)
        left -= 1
        size += 2
        new_blocks = [LEFT]+[1+2*int(left+i in source_tape)+4*int(left+i == head)
                             for i in range(size)]+[RIGHT]
        expected.update(next_origin+4*i+j for i, v in enumerate(new_blocks)
                        for j in range(4) if (v >> j) & 1)
        target_state = ids[HALT] if state == len(table) else ids[('read', ('start', state), 0, 0)]
        local = 0
        while binary_state != target_state or physical_head != next_origin:
            bit = int(physical_head in physical)
            w, di, to = raw[binary_state][bit]
            assert qt[quotient_state][bit] == (w, di, mapping[to])
            assert w >= bit
            binary_state, physical_head = binary_step(raw, binary_state, physical, physical_head)
            quotient_state = mapping[binary_state]
            if with_wang:
                entered = 0
                while not entered or pc != labels[quotient_state] or wh != 2*physical_head:
                    assert pc <= len(program)
                    pc, wh = wang_step(program, pc, wtape, wh)
                    entered += 1
                    assert entered <= 13
                totals['wang_steps'] += entered
                initialized.add(physical_head)
            local += 1
            assert local < 200000
        assert physical == expected, 'complete old records/new record/exterior disagree'
        assert quotient_state == mapping[target_state]
        if with_wang:
            assert wtape == {2*i for i in initialized} | {2*i+1 for i in physical}
        origin = next_origin
        totals.update(source_steps=1, binary_steps=local)
    if state == len(table):
        assert binary_state == len(raw) and quotient_state == len(qt)
        totals['halts'] += 1
        if with_wang:
            before = set(wtape)
            pc, wh = wang_step(program, pc, wtape, wh)
            assert pc == len(program)+1 and wtape == before and wh == 2*physical_head
            totals['wang_steps'] += 1
    else:
        assert binary_state < len(raw) and quotient_state < len(qt)
    return totals


def local_audits():
    rng = random.Random(4408)
    raw, ids, macro = binary_raw(DEFAULT)
    quotient, mapping = control_quotient(raw)
    cases = steps = maximum = 0
    for state, row in macro.items():
        for v, (w, move, target) in enumerate(row):
            tape = {i for i in range(-8, 12) if i not in range(4) and rng.randrange(2)}
            tape.update(i for i in range(4) if (v >> i) & 1)
            expected = (tape-set(range(4))) | {i for i in range(4) if (w >> i) & 1}
            bs = ids[('read', state, 0, 0)]
            qs, head = mapping[bs], 0
            end = ids[HALT] if target == HALT else ids[('read', target, 0, 0)]
            local = 0
            while not local or bs != end or head != 4*move:
                read = int(head in tape)
                ww, dd, tt = raw[bs][read]
                assert quotient[qs][read] == (ww, dd, mapping[tt])
                bs, head = binary_step(raw, bs, tape, head)
                qs = mapping[bs]
                local += 1
                assert local <= 12
            assert tape == expected
            cases += 1
            steps += local
            maximum = max(maximum, local)
    # Every total one-state non-erasing row pair, all reads, new/old neighbours,
    # and odd/even physical shifts; this interpreter never calls the compiler.
    wang_cases = wang_steps = 0
    zero = [(w, d, t) for w in (0, 1) for d in 'LR' for t in (0, 1)]
    one = [(1, d, t) for d in 'LR' for t in (0, 1)]
    for a in zero:
        for b in one:
            table = ((a, b),)
            program, labels = compile_wang(table)
            for read in (0, 1):
                for neighbour in (None, 0, 1):
                    for shift in (-3, 0, 5):
                        write, direction, target = table[0][read]
                        nh = 1 if direction == 'R' else -1
                        initialized = {0} if neighbour is None else {0, nh}
                        tape = ({0} if read else set()) | ({nh} if neighbour == 1 else set())
                        wt = {shift+2*i for i in initialized} | {shift+2*i+1 for i in tape}
                        state, head = binary_step(table, 0, tape, 0)
                        pc, wh, count = 1, shift, 0
                        while not count or pc != labels[state] or wh != shift+2*head:
                            pc, wh = wang_step(program, pc, wt, wh)
                            count += 1
                            assert count <= 13
                        initialized.add(head)
                        assert wt == {shift+2*i for i in initialized} | {shift+2*i+1 for i in tape}
                        wang_cases += 1
                        wang_steps += count
    assert compile_wang(()) == (('M',), (1,))
    return dict(block_cases=cases, block_binary_steps=steps, maximum_block_steps=maximum,
                all_row_quotient_checks=2*len(raw), compact_wang_cases=wang_cases,
                compact_wang_steps=wang_steps)


def loader_oracle(values):
    base = recoder.build(width=8)
    raw = recoder.generic.recoder(8)
    sub = {n: values[n] for n in base['parameters']+base['auxiliaries']}
    env = bridge.execute(raw['source'], recoder.lift(base, sub))
    value = lambda v: env[v] if isinstance(v, str) else v
    residuals = {tuple(pair): value(pair[0])-value(pair[1]) for pair in raw['comparisons']}
    product = 1
    for record, name in zip(base['factor_residuals'], base['unit_factors']):
        factor = 1+record['multiplier']*residuals[tuple(record['pair'])]
        if name in base['auxiliary_strong_corrections']:
            correction = base['auxiliary_strong_corrections'][name]
            factor -= residuals[tuple(correction['pair'])]*env[correction['gap']]
        product *= factor
    omitted = set(map(tuple, base['removed_parent_comparisons']))
    retained = [v for k, v in residuals.items() if k not in omitted]
    retained.append(255*values['frame_repunit']-(env['Q']-1))
    return product*(1+sum(v*v for v in retained))-1


def loader_audit():
    packet = loader()
    source, output = recoder.polynomial_source(packet)
    rng = random.Random(48408)
    for case in range(128):
        vals = {n: rng.randrange(1, 5) if case < 64 else rng.randrange(-3, 5)
                for n in packet['parameters']+packet['auxiliaries']}
        env = bridge.execute(source, vals)
        assert env[output] == loader_oracle(vals)
        assert env['frame_input'] == 40285+8182272*vals['frame_repunit']+2048*vals['z']
    words = 0
    for n in range(2, 11):
        for x in range(1, 1 << n):
            Q = 1 << (8*n)
            r = (Q-1)//255
            z = sum(((x >> i) & 1) << (8*i) for i in range(n))
            assert paired_word(x, n) == 40285+8182272*r+2048*z
            words += 1
    inherited = recoder.degree_audit(recoder.build(width=8))
    assert inherited['exact_degree'] == 348
    degrees = {n: 1 for n in packet['parameters']+packet['auxiliaries']}
    val = lambda v: degrees[v] if isinstance(v, str) else 0
    for name, op, a, b in packet['source']:
        degrees[name] = val(a)+val(b) if op == '*' else max(val(a), val(b))
    assert degrees['modulus'] == 8 and degrees['frame_input'] == 1
    assert inherited['outer_residual_degree'] >= 8
    count = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    assert len(source) == 189 and count == {'M': 93, 'A': 96}
    return dict(polynomial=len(source), M=count['M'], A=count['A'], certificate=packet['operations'],
        equations=packet['equations'], witnesses=packet['witnesses'], degree_upper_bound=348,
        exact_words=words, raw_parent_output_identities=128, signed_cases=64,
        frame_input_degree=1, source_sha256=hashlib.sha256(repr(source).encode()).hexdigest())


def composition_audit(packet, cases=16):
    source, output = polynomial_source(packet)
    lp, wp = packet['loader_packet'], packet['wang_packet']
    ls, lo = recoder.polynomial_source(lp)
    ws, wo = actions.polynomial_source(wp)
    raw = actions.parent.compile_raw(wp['program'], literal_input=True)
    rng = random.Random(84236+len(wp['program']))
    for case in range(cases):
        values = {n: rng.randrange(1, 4) if case < cases//2 else rng.randrange(-2, 4)
                  for n in packet['parameters']+packet['auxiliaries']}
        # P=1 keeps the large-program signed audit bounded off zero.
        for name in wp['auxiliaries']:
            if name.startswith('edge') and name.endswith('_hat'):
                values['wang__'+name] = 1
        lv = {n: values['x' if n == 'x' else 'rec__'+n] for n in lp['parameters']+lp['auxiliaries']}
        le = bridge.execute(ls, lv)
        assert le[lo] == loader_oracle(lv)
        cv = {n: values['wang__'+n] for n in wp['auxiliaries']}
        cv['input'] = le['frame_input']
        ce = bridge.execute(ws, cv)
        lifted = actions.raw_lift(wp, cv)
        residuals, _, _ = actions.parent.independent_raw(raw, lifted)
        oracle, _, _ = actions.parent.unit_raw_oracle(wp, cv, raw, residuals, lifted)
        assert ce[wo] == oracle
        env = bridge.execute(source, values)
        assert env[output] == le[lo]**2+oracle**2
        for name, _, _, _ in ls:
            assert env['x' if name == 'x' else 'rec__'+name] == le[name]
        for name, _, _, _ in ws:
            assert env['wang__'+name] == ce[name]
    return dict(complete_raw_oracle_identities=cases, signed_cases=cases//2,
                scope='Full source identities with bounded off-zero edge words, not Pell zeros.')


def verify():
    rng = random.Random(448377)
    totals = Counter()
    choices = [(w, d, q) for w in (0, 1) for d in 'LR' for q in (0, 1)]
    for a in choices:
        for b in choices:
            table = ((a, b),)
            for x in (1, 2, 5):
                for n in (3, 5):
                    totals.update(record_trace(table, x, n, 5, with_wang=(x == 2 and n == 3)))
    for h in (2, 3, 4):
        for _ in range(6):
            table = tuple(tuple((rng.randrange(2), rng.choice('LR'), rng.randrange(h+1))
                                for _ in (0, 1)) for _ in range(h))
            for j in range(3):
                x = rng.randrange(1, 32)
                totals.update(record_trace(table, x, x.bit_length()+2, 7, with_wang=(j == 0)))
    totals.update(record_trace((), 3, 3, 1, with_wang=True))
    invalid = [(((0, 'S', 0), (1, 'R', 1)),), (((0, 'R', 2), (1, 'R', 1)),), (((0, 'R', 1),),)]
    for table in invalid:
        try:
            binary(table)
        except AssertionError:
            pass
        else:
            raise AssertionError('malformed ordinary table accepted')
    ledgers, audits = [], []
    for table in ((), DEFAULT):
        packet = build(table)
        ledgers.append(ledger(packet))
        audits.append(composition_audit(packet))
    assert ledgers[1]['polynomial'] == 41286
    return dict(status='PASS_COMPACT_ERASING_TM_WANG_BRIDGE', local=local_audits(),
        differential=dict(totals), loader=loader_audit(), ledgers=ledgers,
        composition_audits=audits, malformed_rejections=len(invalid),
        scope='Actual fixed-machine compiler and complete illustrative source; no universal table or universal bound.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert result == json.loads(path.read_text()), 'receipt mismatch'
    print(result['status'])
    print(result['ledgers'][1])
    print(result['differential'])
