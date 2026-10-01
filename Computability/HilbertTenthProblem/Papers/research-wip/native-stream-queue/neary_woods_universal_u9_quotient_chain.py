"""Explicit U9 control quotient, unreachable padding and paid tag polynomial.

The padding changes only the fixed transducer/CTS description. Both the
quotient and padding preserve the actual circular tape and halting event.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import binary_clockwise_control_quotient as quotient
import neary_woods_universal_u9_tag_chain as previous

compiler = previous.compiler
schedule = previous.schedule
D = 18423516044994052458248039479040
PAD = 14
CHAIN = (
    (2, 1, 1),
    (4, 2, 2),
    (5, 4, 1),
    (10, 5, 5),
    (20, 10, 10),
    (21, 20, 1),
    (42, 21, 21),
    (84, 42, 42),
    (168, 84, 84),
    (169, 168, 1),
    (338, 169, 169),
    (676, 338, 338),
    (1352, 676, 676),
    (2704, 1352, 1352),
    (5408, 2704, 2704),
    (10816, 5408, 5408),
    (21632, 10816, 10816),
    (21653, 21632, 21),
    (43306, 21653, 21653),
    (64959, 21653, 43306),
    (129918, 64959, 64959),
    (259836, 129918, 129918),
    (519672, 259836, 259836),
    (584631, 519672, 64959),
    (1169262, 584631, 584631),
    (2338524, 1169262, 1169262),
    (4677048, 2338524, 2338524),
    (9354096, 4677048, 4677048),
    (18708192, 9354096, 9354096),
    (37416384, 18708192, 18708192),
    (37438037, 37416384, 21653),
    (74876074, 37438037, 37438037),
    (112314111, 37438037, 74876074),
    (224628222, 112314111, 112314111),
    (336942333, 112314111, 224628222),
    (411818407, 74876074, 336942333),
    (486694481, 74876074, 411818407),
    (973388962, 486694481, 486694481),
    (1946777924, 973388962, 973388962),
    (3893555848, 1946777924, 1946777924),
    (7787111696, 3893555848, 3893555848),
    (15574223392, 7787111696, 7787111696),
    (31148446784, 15574223392, 15574223392),
    (62296893568, 31148446784, 31148446784),
    (124593787136, 62296893568, 62296893568),
    (249187574272, 124593787136, 124593787136),
    (249674268753, 249187574272, 486694481),
    (499348537506, 249674268753, 249674268753),
    (998697075012, 499348537506, 499348537506),
    (1997394150024, 998697075012, 998697075012),
    (3994788300048, 1997394150024, 1997394150024),
    (7989576600096, 3994788300048, 3994788300048),
    (7989913542429, 7989576600096, 336942333),
    (15979827084858, 7989913542429, 7989913542429),
    (31959654169716, 15979827084858, 15979827084858),
    (63919308339432, 31959654169716, 31959654169716),
    (127838616678864, 63919308339432, 63919308339432),
    (255677233357728, 127838616678864, 127838616678864),
    (255677645176135, 255677233357728, 411818407),
    (511355290352270, 255677645176135, 255677645176135),
    (1022710580704540, 511355290352270, 511355290352270),
    (2045421161409080, 1022710580704540, 1022710580704540),
    (4090842322818160, 2045421161409080, 2045421161409080),
    (8181684645636320, 4090842322818160, 4090842322818160),
    (8181684683074357, 8181684645636320, 37438037),
    (16363369366148714, 8181684683074357, 8181684683074357),
    (32726738732297428, 16363369366148714, 16363369366148714),
    (65453477464594856, 32726738732297428, 32726738732297428),
    (130906954929189712, 65453477464594856, 65453477464594856),
    (261813909858379424, 130906954929189712, 130906954929189712),
    (523627819716758848, 261813909858379424, 261813909858379424),
    (1047255639433517696, 523627819716758848, 523627819716758848),
    (2094511278867035392, 1047255639433517696, 1047255639433517696),
    (4189022557734070784, 2094511278867035392, 2094511278867035392),
    (8378045115468141568, 4189022557734070784, 4189022557734070784),
    (16756090230936283136, 8378045115468141568, 8378045115468141568),
    (33512180461872566272, 16756090230936283136, 16756090230936283136),
    (67024360923745132544, 33512180461872566272, 33512180461872566272),
    (134048721847490265088, 67024360923745132544, 67024360923745132544),
    (134048721847602579199, 134048721847490265088, 112314111),
    (268097443695205158398, 134048721847602579199, 134048721847602579199),
    (536194887390410316796, 268097443695205158398, 268097443695205158398),
    (1072389774780820633592, 536194887390410316796, 536194887390410316796),
    (2144779549561641267184, 1072389774780820633592, 1072389774780820633592),
    (2144779549561678705221, 2144779549561641267184, 37438037),
    (4289559099123357410442, 2144779549561678705221, 2144779549561678705221),
    (8579118198246714820884, 4289559099123357410442, 4289559099123357410442),
    (17158236396493429641768, 8579118198246714820884, 8579118198246714820884),
    (34316472792986859283536, 17158236396493429641768, 17158236396493429641768),
    (68632945585973718567072, 34316472792986859283536, 34316472792986859283536),
    (68632945585973756005109, 68632945585973718567072, 37438037),
    (137265891171947512010218, 68632945585973756005109, 68632945585973756005109),
    (274531782343895024020436, 137265891171947512010218, 137265891171947512010218),
    (549063564687790048040872, 274531782343895024020436, 274531782343895024020436),
    (1098127129375580096081744, 549063564687790048040872, 549063564687790048040872),
    (2196254258751160192163488, 1098127129375580096081744, 1098127129375580096081744),
    (4392508517502320384326976, 2196254258751160192163488, 2196254258751160192163488),
    (8785017035004640768653952, 4392508517502320384326976, 4392508517502320384326976),
    (17570034070009281537307904, 8785017035004640768653952, 8785017035004640768653952),
    (35140068140018563074615808, 17570034070009281537307904, 17570034070009281537307904),
    (35140068140018563186929919, 35140068140018563074615808, 112314111),
    (70280136280037126373859838, 35140068140018563186929919, 35140068140018563186929919),
    (140560272560074252747719676, 70280136280037126373859838, 70280136280037126373859838),
    (281120545120148505495439352, 140560272560074252747719676, 140560272560074252747719676),
    (562241090240297010990878704, 281120545120148505495439352, 281120545120148505495439352),
    (1124482180480594021981757408, 562241090240297010990878704, 562241090240297010990878704),
    (2248964360961188043963514816, 1124482180480594021981757408, 1124482180480594021981757408),
    (4497928721922376087927029632, 2248964360961188043963514816, 2248964360961188043963514816),
    (4497928721922376088413724113, 4497928721922376087927029632, 486694481),
    (8995857443844752176827448226, 4497928721922376088413724113, 4497928721922376088413724113),
    (17991714887689504353654896452, 8995857443844752176827448226, 8995857443844752176827448226),
    (35983429775379008707309792904, 17991714887689504353654896452, 17991714887689504353654896452),
    (71966859550758017414619585808, 35983429775379008707309792904, 35983429775379008707309792904),
    (71966859550758017415031404215, 71966859550758017414619585808, 411818407),
    (143933719101516034830062808430, 71966859550758017415031404215, 71966859550758017415031404215),
    (287867438203032069660125616860, 143933719101516034830062808430, 143933719101516034830062808430),
    (575734876406064139320251233720, 287867438203032069660125616860, 287867438203032069660125616860),
    (1151469752812128278640502467440, 575734876406064139320251233720, 575734876406064139320251233720),
    (2302939505624256557281004934880, 1151469752812128278640502467440, 1151469752812128278640502467440),
    (4605879011248513114562009869760, 2302939505624256557281004934880, 2302939505624256557281004934880),
    (9211758022497026229124019739520, 4605879011248513114562009869760, 4605879011248513114562009869760),
    (18423516044994052458248039479040, 9211758022497026229124019739520, 9211758022497026229124019739520),
)


def pad_control(old, padding=PAD):
    assert isinstance(padding, int) and padding >= 0
    old_halt = old['halt']
    new_halt = old_halt+padding
    assert old['start'] == 1
    assert set(old['transitions']) == {(q, b) for q in range(1, old_halt) for b in '01'}
    lift = lambda q: new_halt if q == old_halt else q
    rules = {(q, b): (w, lift(t)) for (q, b), (w, t) in old['transitions'].items()}
    for q in range(old_halt, new_halt):
        for b in '01':
            rules[q, b] = (b, q)
    assert set(rules) == {(q, b) for q in range(1, new_halt) for b in '01'}
    for (q, b), (w, t) in old['transitions'].items():
        assert rules[lift(q), b] == (w, lift(t))
    seen, todo = {1}, [1]
    while todo:
        q = todo.pop()
        if q == new_halt:
            continue
        for b in '01':
            t = rules[q, b][1]
            if t not in seen:
                seen.add(t)
                todo.append(t)
    assert seen == set(range(1, old_halt)) | {new_halt}
    assert sum(len(w) == 2 for w, _ in rules.values()) == sum(
        len(w) == 2 for w, _ in old['transitions'].values())
    return dict(start=1, halt=new_halt, old_halt=old_halt, padding=padding,
                transitions=rules, unreachable=tuple(range(old_halt, new_halt)))


@lru_cache(None)
def components():
    old = quotient.build('u9')
    assert old['halt'] == 1611 and old['cts_table']['T2'] == 64
    padded = pad_control(old)
    assert padded['halt'] == 1625
    metadata = previous.metadata.metadata
    table = metadata.cts_table(padded['halt'], padded['transitions'])
    summary = metadata.row_summary(table)
    counts = metadata.track_counts(table['p'], table['total_length'], summary['maximum'])
    assert D == 128*table['z']*counts['bit_block_length']
    wire = [[q, b, w, t] for (q, b), (w, t) in sorted(padded['transitions'].items())]
    oldwire = [[q, b, w, t] for (q, b), (w, t) in sorted(old['transitions'].items())]
    recipe = dict(machine='U9 reachable-control quotient with14 unreachable copying states',
        original_binary_states=old['original_states'], reachable_original_states=old['reachable_states'],
        quotient_states=old['halt'], padded_states=padded['halt'], padding=PAD,
        old_accepting_label=old['halt'], accepting_label=padded['halt'],
        quotient_sha256=hashlib.sha256(json.dumps(oldwire, separators=(',', ':')).encode()).hexdigest(),
        padded_table_sha256=hashlib.sha256(json.dumps(wire, separators=(',', ':')).encode()).hexdigest(),
        cts_sparse_table_sha256=summary['sparse_table_sha256'],
        binary_start='class of read(run(u1),empty_prefix), label1',
        Q=table['Q'], z=table['z'], p=table['p'], halt=table['halt'],
        beta=counts['beta'], s=counts['s'],
        u_definition='Interleave the fixed tracks; imported production_letter(table,counts,k) '
                     'specifies each letter for this actual padded table.',
        production_offset_definition='val(1 e(u without its last b) 10), e(b)=10^beta1,e(c)=1',
        encoded_production_length=counts['e_u_length'], D=D)
    return old, padded, table, counts, summary, recipe


def build(form='normalized', *, merge_bound=True):
    assert form in ('raw', 'units', 'normalized')
    old, padded, table, counts, summary, recipe = components()
    packet = schedule.rewrite_raw(compiler.raw_build(D, counts['beta'], counts['e_u_length']),
                                  merge_bound=merge_bound, chain=CHAIN)
    if form != 'raw':
        packet = compiler.parent.units.rewrite(packet)
        packet.update(form='units', unit_product=True)
        if form == 'normalized':
            packet = compiler.parent.normalized.rewrite(packet)
            packet['form'] = form
    compiler.check_source(packet)
    return packet


def ledger(packet):
    source, out = compiler.parent.polynomial_source(packet)
    counts = Counter('M' if op == '*' else 'A' for _, op, _, _ in source)
    base, witnesses, equations = {'raw': (475, 88, 56),
                                 'units': (400, 69, 28),
                                 'normalized': (397, 69, 25)}[packet['form']]
    assert packet['width'] == D and len(CHAIN) == 122
    assert len(source) == base+len(CHAIN)
    assert (packet['witnesses'], packet['equations']) == (witnesses, equations)
    assert packet['parameters'] == [n for n in compiler.PARAMETERS
                                   if not (packet['bound_is_program_E'] and n == 'program_bound')]
    return dict(form=packet['form'], width=D, power_chain_operations=len(CHAIN),
        certificate={k: packet[k] for k in ('operations', 'multiplications',
                     'additions_subtractions', 'equations', 'witnesses')},
        polynomial=dict(operations=len(source), multiplications=counts['M'],
                        additions_subtractions=counts['A'], output=out),
        parameters=packet['parameters'], bound_is_program_E=packet['bound_is_program_E'],
        **compiler.degree_upper_bound(packet))


def verify():
    old, padded, table, counts, summary, recipe = components()
    assert len(CHAIN) == 122
    assert D == (1 << 8)*21653*1729*1922292548371540351195
    power_source = schedule.chain_source(CHAIN, D)
    letter = previous.u15.production_letter
    assert ''.join(letter(table, counts, j) for j in range(3)) == 'bcb'
    assert letter(table, counts, counts['u_length']-1) == 'b'
    assert (counts['u_length']-1) % (counts['beta']-1) == 0
    rng = random.Random(519313206)
    traces = trace_steps = terminal_cases = 0
    lift = lambda q: padded['halt'] if q == old['halt'] else q
    for case in range(384):
        q = 1 if case < 128 else rng.randrange(1, old['halt']+1)
        newq = lift(q)
        word = ''.join(rng.choice('01') for _ in range(rng.randrange(1, 41)))
        newword = word
        for _ in range(128):
            assert (q == old['halt']) == (newq == padded['halt'])
            assert newq == lift(q) and word == newword
            if q == old['halt']:
                break
            written, q = old['transitions'][q, word[0]]
            newwritten, newq = padded['transitions'][newq, newword[0]]
            word = word[1:]+written
            newword = newword[1:]+newwritten
            trace_steps += 1
        traces += 1
    for (q, b), (w, target) in old['transitions'].items():
        if target == old['halt']:
            for tail in ('', '0', '1', '01', '101'):
                assert padded['transitions'][q, b] == (w, padded['halt'])
                assert tail+w == tail+padded['transitions'][q, b][0]
                terminal_cases += 1
    assert terminal_cases > 0
    powers = 0
    for modulus in (2, 8, 27, 97, 257, 1009, 65537, 1000000007):
        for q in (-100, -19, -2, -1, 0, 1, 2, 3, 16, 97, modulus, modulus+1):
            env = schedule.execute_mod(power_source, {'q': q}, {}, modulus)
            for exponent, _, _ in CHAIN:
                name = 'Q' if exponent == D else f'addition_power{exponent}'
                assert env[name] == pow(q, exponent, modulus)
            powers += 1
    records = []
    identities = signed = 0
    for form in ('raw', 'units', 'normalized'):
        before = compiler.build(D, counts['beta'], counts['e_u_length'], form)
        osource, oout = compiler.parent.polynomial_source(before)
        for merge_bound in (False, True):
            packet = build(form, merge_bound=merge_bound)
            newsource, newout = compiler.parent.polynomial_source(packet)
            assert packet['auxiliaries'] == before['auxiliaries']
            assert packet['comparisons'] == before['comparisons']
            common = {n for n, _, _, _ in osource} & {n for n, _, _, _ in newsource}
            for case in range(128):
                modulus = (257, 65537, 1000000007, 1048576)[case % 4]
                values = {n: rng.randrange(1, 20) if case < 64 else rng.randrange(-20, 21)
                          for n in packet['parameters']+packet['auxiliaries']}
                constants = {n: rng.randrange(-1000, 1001) for n in compiler.NUMERALS}
                restored = dict(values)
                if merge_bound:
                    restored['program_bound'] = values['program_E']
                env = schedule.execute_mod(osource, restored, constants, modulus)
                newenv = schedule.execute_mod(newsource, values, constants, modulus)
                assert all(env[n] == newenv[n] for n in common)
                assert env[oout] == newenv[newout]
                identities += 1
                signed += case >= 64
            records.append(ledger(packet))
    counter_cases = 0
    for overhead in (1, 63, 64, 65, 128, 1000, 100001):
        for extra in (0, 1, 7):
            E = overhead+extra
            n = 1 << E.bit_length()
            assert n > E >= overhead and n > (overhead+63)//64
            cells = 64*n+overhead
            assert 64*n < cells < 128*n
            assert 1 << (cells-1).bit_length() == 128*n
            counter_cases += 1
    packet = build()
    final_source, out = compiler.parent.polynomial_source(packet)
    encoded = compiler.encode_source(final_source)
    result = ledger(packet)
    assert result['polynomial']['operations'] == 519
    assert (result['polynomial']['multiplications'], result['polynomial']['additions_subtractions']) == (313, 206)
    rules = {f'{q}:{b}': f'{w}:{t}' for (q, b), (w, t) in sorted(padded['transitions'].items())}
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_U9_QUOTIENT_CHAIN',
        fixed_recipe=recipe, actual_padded_rules=rules, unreachable_padded_states=padded['unreachable'],
        original_quotient_row_checks=len(old['transitions']), padding_rows=2*PAD,
        padding_circular_trace_cases=traces, padding_circular_trace_steps=trace_steps,
        immediate_halt_cases=terminal_cases, cts=summary, tag_counts=counts,
        addition_chain=CHAIN, independent_modular_power_cases=powers,
        independent_modular_node_checks=powers*len(CHAIN),
        full_modular_source_identities=identities, signed_cases=signed,
        exact_counter_bound_cases=counter_cases, ledgers=records,
        source_sha256=hashlib.sha256(json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
        example=dict(source=encoded, output=out, comparisons=packet['comparisons'],
                     parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                     fixed_numeral_definitions=compiler.NUMERALS),
        scope='One fixed universal U9-derived polynomial: 519 operations, 69 positive '
              'witnesses, four positive program parameters. Exact control bisimulation '
              'and unreachable padding precede rebuilding the complete CTS/tag constants. '
              'Degree upper bound only; no shortest-chain/minimum-machine claim or '
              'expanded universal production, huge numeral or complete native Pell zero.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write:
        path.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(path.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print(result['ledgers'][-1])
