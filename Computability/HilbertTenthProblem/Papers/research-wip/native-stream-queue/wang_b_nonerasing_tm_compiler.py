"""Literal Theorem 7 TM-to-Wang expansion with a paid ordinary-input pair map.

TM states are 0,...,h, with start 0 and sole halt h. A table has h rows,
each containing (write, direction, next_state) for reads 0 and 1. The
empty table starts halted. Nonhalting rows must be total and non-erasing.
No universal table or ordinary-to-non-erasing compiler is supplied.
"""
import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

import native_binary_input_dilation_unit179 as recoder
import wang_b_computed_actions as actions

PRIMARY = 'https://mural.maynoothuniversity.ie/id/eprint/12409/1/Woods_Wang_2014.pdf'
DEFAULT = (((1, 'R', 1), (1, 'L', 1)),)
execute = actions.execute


def normalize(table):
    table = tuple(tuple(tuple(t) for t in row) for row in table)
    h = len(table)
    for row in table:
        assert len(row) == 2, 'both read symbols need a transition'
        for read, transition in enumerate(row):
            assert len(transition) == 3
            write, direction, target = transition
            assert write in (0, 1) and (read == 0 or write == 1), 'erasing transition'
            assert direction in ('L', 'R'), 'stationary moves are outside this exact expansion'
            assert type(target) is int and 0 <= target <= h
    return table


def compile_tm(table=DEFAULT):
    table = normalize(table)
    program = []
    for i, row in enumerate(table):
        program += ['R', ('J', 13*i+9)]
        write, direction, target = row[0]
        if direction == 'R':
            zero = ['R', 'M', 'M', 'M', 'M'] if write == 0 else ['M', 'R', 'M', 'M', 'M']
        else:
            zero = ['L', 'L', 'L', 'M', 'M'] if write == 0 else ['M', 'L', 'L', 'L', 'M']
        program += zero + [('J', 13*target+1)]
        _, direction, target = row[1]
        program += (['R', 'M', 'M', 'M'] if direction == 'R' else ['L', 'L', 'L', 'M'])
        program.append(('J', 13*target+1))
    program.append('M')
    program = actions.parent.normalize(program)
    assert len(program) == 13*len(table)+1
    assert sum(isinstance(i, tuple) for i in program) == 3*len(table)
    return program


def pair_integer(x, n):
    assert n >= max(2, x.bit_length()) and x > 0
    return sum((1+2*((x >> j) & 1)) << (2*j) for j in range(n))


def rename_source(source, rename):
    return [(rename(n), op, rename(a), rename(b)) for n, op, a, b in source]


def build(table=DEFAULT, *, ordinary_input=True, form='units'):
    table = normalize(table)
    program = compile_tm(table)
    wang = actions.build(program, literal_input=True, form=form)
    if not ordinary_input:
        return dict(wang, tm_table=table, ordinary_tm_input=False,
                    scope='Literal Wang input; TM interpretation requires the stated pair encoding.')
    rp = recoder.build(width=2)
    # All original recoder comparisons/factors remain. The additional row
    # is included inside its own complete integer-product finalizer.
    rp = dict(rp, source=list(rp['source'])+[
        ('pair_repunit_times3', '*', 3, 'pair_repunit'),
        ('pair_twice_z', '+', 'z', 'z'),
        ('pair_input', '+', 'pair_repunit', 'pair_twice_z')],
        comparisons=list(rp['comparisons'])+[('pair_repunit_times3', 'modulus')],
        auxiliaries=list(rp['auxiliaries'])+['pair_repunit'],
        operations=rp['operations']+3, multiplications=rp['multiplications']+1,
        additions_subtractions=rp['additions_subtractions']+2,
        equations=rp['equations']+1, witnesses=rp['witnesses']+1)
    rn = lambda v: ('x' if v == 'x' else 'rec__'+v) if isinstance(v, str) else v
    wn = lambda v: ('rec__pair_input' if v == 'input' else 'wang__'+v) if isinstance(v, str) else v
    source = rename_source(rp['source'], rn)+rename_source(wang['source'], wn)
    aux = ['rec__z']+[rn(v) for v in rp['auxiliaries']]+[wn(v) for v in wang['auxiliaries']]
    comparisons = [(rn(a), rn(b)) for a, b in rp['comparisons']]+[(wn(a), wn(b)) for a, b in wang['comparisons']]
    actions.scale.checked_source(source, ['x'], aux)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    return dict(source=source, parameters=['x'], auxiliaries=aux, comparisons=comparisons,
        operations=len(source), multiplications=counts['M'], additions_subtractions=counts['A'],
        equations=len(comparisons), witnesses=len(aux), ordinary_tm_input=True,
        tm_table=table, program=program, form=form, recoder_packet=rp, wang_packet=wang,
        scope='Halting of this fixed non-erasing binary TM on ordinary positive binary x.')


def polynomial_source(packet):
    if not packet['ordinary_tm_input']:
        return actions.polynomial_source(packet)
    rp, wp = packet['recoder_packet'], packet['wang_packet']
    rs, ro = recoder.polynomial_source(rp)
    ws, wo = actions.polynomial_source(wp)
    rn = lambda v: ('x' if v == 'x' else 'rec__'+v) if isinstance(v, str) else v
    wn = lambda v: ('rec__pair_input' if v == 'input' else 'wang__'+v) if isinstance(v, str) else v
    source = rename_source(rs, rn)+rename_source(ws, wn)+[
        ('tm_recoder_square', '*', rn(ro), rn(ro)),
        ('tm_wang_square', '*', wn(wo), wn(wo)),
        ('tm_output', '+', 'tm_recoder_square', 'tm_wang_square')]
    assert len(rs) == 185 and len(source) == len(ws)+188
    actions.scale.checked_source(source, packet['parameters'], packet['auxiliaries'])
    return source, 'tm_output'


def ledger(packet):
    source, _ = polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    result = dict(certificate=packet['operations'], comparisons=packet['equations'],
        witnesses=packet['witnesses'], parameters=len(packet['parameters']),
        polynomial=len(source), M=counts['M'], A=counts['A'])
    wp = packet['wang_packet'] if packet['ordinary_tm_input'] else packet
    bound = actions.parent.bounds(wp)['degree_upper_bound']
    result['degree_upper_bound'] = 2*max(186, bound) if packet['ordinary_tm_input'] else bound
    result.update(tm_nonhalting_states=len(packet['tm_table']), wang_instructions=len(packet['program']),
                  jump_instructions=3*len(packet['tm_table']), edges=len(actions.parent.edges(packet['program'])))
    return result


def tm_step(table, state, tape, head):
    """Separate ordinary TM semantics: no Wang program or encoded tape."""
    assert state < len(table)
    write, direction, target = table[state][int(head in tape)]
    tape = set(tape)
    if write: tape.add(head)
    else: tape.discard(head)
    return target, tape, head+(1 if direction == 'R' else -1)


def wang_step(program, pc, tape, head):
    """Direct physical-set Wang interpreter, permitting negative positions."""
    instruction = program[pc-1]
    tape = set(tape)
    if instruction == 'M': tape.add(head)
    elif instruction == 'L': head -= 1
    elif instruction == 'R': head += 1
    elif head in tape: return instruction[1], tape, head
    return pc+1, tape, head


def differential(table, tape, head, initialized, limit=40):
    table = normalize(table); program = compile_tm(table)
    tape = set(tape); initialized = set(initialized)
    assert tape | {head} <= initialized
    wtape = {2*i for i in initialized} | {2*i+1 for i in tape}
    state = 0; pc = 1; wh = 2*head
    steps = microsteps = left_extensions = right_extensions = 0
    cases = Counter()
    while state < len(table) and steps < limit:
        read = int(head in tape); write, direction, target = table[state][read]
        cases[f'{read}{write}{direction}'] += 1
        ns, nt, nh = tm_step(table, state, tape, head)
        if nh not in initialized:
            left_extensions += nh < min(initialized)
            right_extensions += nh > max(initialized)
        initialized.add(nh)
        expected = 8 if read == 0 else 7
        for _ in range(expected):
            pc, wtape, wh = wang_step(program, pc, wtape, wh); microsteps += 1
        state, tape, head = ns, nt, nh; steps += 1
        assert pc == 13*state+1 and wh == 2*head
        assert wtape == {2*i for i in initialized} | {2*i+1 for i in tape}
        assert wh in wtape
    if state == len(table):
        before = set(wtape)
        pc, wtape, wh = wang_step(program, pc, wtape, wh); microsteps += 1
        assert pc == len(program)+1 and wtape == before and wh == 2*head
    else: assert pc <= len(program)
    return dict(tm_steps=steps, wang_steps=microsteps, halted=state == len(table),
                left_extensions=left_extensions, right_extensions=right_extensions, cases=dict(cases))


def source_oracle(packet, values):
    """Independent raw-parent residual oracles, then explicit conjunction."""
    rp, wp = packet['recoder_packet'], packet['wang_packet']
    rv = {v:values['x' if v == 'x' else 'rec__'+v] for v in rp['parameters']+rp['auxiliaries']}
    recbase = recoder.build(width=2)
    old = recoder.radix4.build()
    lifted = recoder.lift(recbase, {k:v for k,v in rv.items() if k != 'pair_repunit'})
    oldenv = execute(old['source'], lifted)
    rr = dict(zip(old['comparisons'], recoder.radix4.independent(lifted)))
    product = 1
    for record, name in zip(recbase['factor_residuals'], recbase['unit_factors']):
        f = 1+record['multiplier']*rr[tuple(record['pair'])]
        if name in recbase['auxiliary_strong_corrections']:
            c = recbase['auxiliary_strong_corrections'][name]
            f -= rr[tuple(c['pair'])]*oldenv[c['gap']]
        product *= f
    omitted = set(map(tuple, recbase['removed_parent_comparisons']))
    res = [r for pair, r in rr.items() if pair not in omitted]
    res.append(3*rv['pair_repunit']-(oldenv['Q']-1))
    rec_out = product*(1+sum(r*r for r in res))-1
    y = rv['pair_repunit']+2*rv['z']
    wv = {v:y if v == 'input' else values['wang__'+v] for v in wp['parameters']+wp['auxiliaries']}
    raw = actions.parent.compile_raw(wp['program'], literal_input=True)
    restored = actions.raw_lift(wp, wv)
    wr, _, _ = actions.parent.independent_raw(raw, restored)
    if wp['form'] == 'units':
        wang_out, _, _ = actions.parent.unit_raw_oracle(wp, wv, raw, wr, restored)
    else: wang_out = sum(r*r for r in wr)
    return rec_out*rec_out+wang_out*wang_out


def verify():
    rng = random.Random(201413)
    totals = Counter(); rule_cases = Counter()
    # Exhaust all six rule types, both ordinary and never-initialized neighbours.
    local = 0
    for read in (0, 1):
        for write in ((0, 1) if read == 0 else (1,)):
            for direction in ('L', 'R'):
                for neighbour in (None, 0, 1):
                    rows = [(0, 'R', 1), (1, 'R', 1)]
                    rows[read] = (write, direction, 1)
                    tape = {0} if read else set()
                    at = 1 if direction == 'R' else -1
                    initialized = {0} if neighbour is None else {0, at}
                    if neighbour == 1: tape.add(at)
                    differential((tuple(rows),), tape, 0, initialized, 1); local += 1
    for h in range(6):
        for machine in range(16):
            table = tuple(((rng.randrange(2), rng.choice('LR'), rng.randrange(h+1)),
                           (1, rng.choice('LR'), rng.randrange(h+1))) for _ in range(h))
            for _ in range(4):
                lo, hi = -rng.randrange(1, 5), rng.randrange(1, 6)
                tape = {i for i in range(lo, hi+1) if rng.randrange(2)}
                result = differential(table, tape, rng.randrange(lo, hi+1), range(lo, hi+1), 32)
                rule_cases.update(result.pop('cases')); totals.update(result); totals['runs'] += 1
    assert set(rule_cases) == {'00L', '00R', '01L', '01R', '11L', '11R'}
    assert totals['left_extensions'] and totals['right_extensions']
    pair_cases = 0
    for n in range(2, 11):
        for x in range(1, 1 << n):
            z = recoder.radix4.spread(x); r = ((1 << (2*n))-1)//3
            y = pair_integer(x, n)
            assert y == r+2*z and 3*r == (1 << (2*n))-1
            assert all(((y >> (2*j)) & 3) == 1+2*((x >> j) & 1) for j in range(n))
            pair_cases += 1
    tables = [(), DEFAULT, (((0, 'L', 0), (1, 'R', 1)),),
              (((1, 'R', 1), (1, 'L', 1)), ((0, 'L', 2), (1, 'R', 2)))]
    ledgers = []; identities = signed = 0
    for table in tables:
        for form in ('raw', 'scaled', 'projected', 'units'):
            encoded = build(table, ordinary_input=False, form=form)
            packet = build(table, form=form); source, output = polynomial_source(packet)
            for case in range(12):
                pos = case < 6
                values = {v:rng.randrange(1, 4) if pos else rng.randrange(-2, 4)
                          for v in packet['parameters']+packet['auxiliaries']}
                assert execute(source, values)[output] == source_oracle(packet, values)
                identities += 1; signed += not pos
            for p in (encoded, packet):
                ledgers.append(dict(table=table, form=form, ordinary_input=p['ordinary_tm_input'], **ledger(p)))
    # Padded physical input traces: extra initialized zero pairs do not change TM semantics.
    padding = halted_outer = outer_rows = 0
    for table in tables:
        for x in range(1, 17):
            for n in (max(2, x.bit_length()), max(2, x.bit_length())+2):
                tape = {j for j in range(x.bit_length()) if (x >> j) & 1}
                differential(table, tape, 0, range(n), 24); padding += 1
                # Use the parent's already-tested packing only after a physical
                # trace determines a sufficient independent spatial shift.
                program = compile_tm(table); cells = {j for j in range(2*n) if (pair_integer(x,n) >> j) & 1}
                pc = 1; head = 0; minhead = 0; steps = 0
                while pc <= len(program) and steps < 200:
                    pc, cells, head = wang_step(program, pc, cells, head)
                    minhead = min(minhead, head); steps += 1
                if pc <= len(program): continue
                shift = max(0, -minhead)+1; head0 = 1 << shift
                raw = actions.parent.compile_raw(program, literal_input=True)
                vals, trace = actions.parent.positive_history(program, pair_integer(x,n)*head0, head0,
                                                               limit=200, literal_input=True)
                rr, words, nv = actions.parent.independent_raw(raw, vals)
                assert rr[:8] == [0]*8 and words[0] & words[1] == words[2]
                new = actions.build(program, literal_input=True, form='raw')
                v = actions.project_from_parent(new, vals)
                env = execute(new['source'], v)
                at = lambda a:env[a] if isinstance(a,str) else a
                assert all(at(a) == at(b) for a,b in new['comparisons'][:4])
                assert actions.lift_to_parent(new, v) == vals
                halted_outer += 1; outer_rows += len(trace['rows'])
    rejected = 0
    for bad in ((((0, 'R', 1), (0, 'L', 1)),), (((0, 'S', 1), (1, 'R', 1)),),
                (((0, 'R', 2), (1, 'R', 1)),), (((0, 'R', 1),),)):
        try: compile_tm(bad)
        except AssertionError: rejected += 1
        else: raise AssertionError('invalid table accepted')
    default = build(); ds, do = polynomial_source(default)
    digest = hashlib.sha256(json.dumps(ds, separators=(',', ':')).encode()).hexdigest()
    return dict(status='PASS_WANG_B_NONERASING_TM_COMPILER', primary=PRIMARY,
        default_table=DEFAULT, default_program=compile_tm(), default=ledger(default),
        default_source_sha256=digest, default_output=do, ledgers=ledgers,
        differential=dict(local_rule_cases=local, **dict(totals), rules=dict(rule_cases)),
        pair_map=dict(exact_cases=pair_cases, padded_trace_cases=padding, physical_digit_order='least-significant bit first'),
        whole_source=dict(raw_oracle_identities=identities, signed=signed, positive=identities-signed),
        outer_histories=dict(halted_instances=halted_outer, chronological_rows=outer_rows,
            full_Pell_zeros_materialized=False), invalid_tables_rejected=rejected,
        scope='Complete ordinary positive input for an arbitrary fixed total non-erasing binary TM. No numerical universal table or ordinary-to-non-erasing compiler.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--write', action='store_true')
    args = parser.parse_args(); result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result, indent=2)+'\n')
    else: assert result == json.loads(path.read_text()), 'receipt mismatch'
    print(result['status'])
