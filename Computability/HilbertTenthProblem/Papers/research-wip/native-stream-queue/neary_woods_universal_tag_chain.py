"""A fixed positive addition chain and four program ports for the U15 tag polynomial.

Only the fixed q**D multiplication schedule and the program-bound alias change.
No fixed numeral with D bits or complete native Pell zero is materialized.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_tag557 as parent

compiler = parent.compiler
D = 911894954830740789802965708213760
# Found by a bounded factor/window search, not asserted shortest.
# D = 2**9 * 100404692303 * 17738661339441947785.
# The factor schedules cost 44 and 78 multiplications; nine doublings finish.
CHAIN = (
    (2, 1, 1),
    (3, 1, 2),
    (6, 3, 3),
    (9, 3, 6),
    (15, 6, 9),
    (21, 6, 15),
    (23, 2, 21),
    (46, 23, 23),
    (92, 46, 46),
    (184, 92, 92),
    (187, 184, 3),
    (374, 187, 187),
    (748, 374, 374),
    (1496, 748, 748),
    (2992, 1496, 1496),
    (5984, 2992, 2992),
    (11968, 5984, 5984),
    (23936, 11968, 11968),
    (47872, 23936, 23936),
    (95744, 47872, 47872),
    (95753, 95744, 9),
    (191506, 95753, 95753),
    (383012, 191506, 191506),
    (766024, 383012, 383012),
    (766027, 766024, 3),
    (1532054, 766027, 766027),
    (3064108, 1532054, 1532054),
    (6128216, 3064108, 3064108),
    (12256432, 6128216, 6128216),
    (24512864, 12256432, 12256432),
    (49025728, 24512864, 24512864),
    (98051456, 49025728, 49025728),
    (196102912, 98051456, 98051456),
    (392205824, 196102912, 196102912),
    (784411648, 392205824, 392205824),
    (1568823296, 784411648, 784411648),
    (1568823317, 1568823296, 21),
    (3137646634, 1568823317, 1568823317),
    (6275293268, 3137646634, 3137646634),
    (12550586536, 6275293268, 6275293268),
    (25101173072, 12550586536, 12550586536),
    (50202346144, 25101173072, 25101173072),
    (100404692288, 50202346144, 50202346144),
    (100404692303, 100404692288, 15),
    (200809384606, 100404692303, 100404692303),
    (301214076909, 100404692303, 200809384606),
    (401618769212, 100404692303, 301214076909),
    (502023461515, 200809384606, 301214076909),
    (903642230727, 502023461515, 401618769212),
    (1104451615333, 200809384606, 903642230727),
    (1506070384545, 401618769212, 1104451615333),
    (3012140769090, 1506070384545, 1506070384545),
    (6024281538180, 3012140769090, 3012140769090),
    (12048563076360, 6024281538180, 6024281538180),
    (12349777153269, 12048563076360, 301214076909),
    (24699554306538, 12349777153269, 12349777153269),
    (49399108613076, 24699554306538, 24699554306538),
    (98798217226152, 49399108613076, 49399108613076),
    (197596434452304, 98798217226152, 98798217226152),
    (395192868904608, 197596434452304, 197596434452304),
    (790385737809216, 395192868904608, 395192868904608),
    (1580771475618432, 790385737809216, 790385737809216),
    (1581875927233765, 1580771475618432, 1104451615333),
    (3163751854467530, 1581875927233765, 1581875927233765),
    (6327503708935060, 3163751854467530, 3163751854467530),
    (12655007417870120, 6327503708935060, 6327503708935060),
    (25310014835740240, 12655007417870120, 12655007417870120),
    (50620029671480480, 25310014835740240, 25310014835740240),
    (50620330885557389, 50620029671480480, 301214076909),
    (101240661771114778, 50620330885557389, 50620330885557389),
    (202481323542229556, 101240661771114778, 101240661771114778),
    (404962647084459112, 202481323542229556, 202481323542229556),
    (809925294168918224, 404962647084459112, 404962647084459112),
    (1619850588337836448, 809925294168918224, 809925294168918224),
    (3239701176675672896, 1619850588337836448, 1619850588337836448),
    (3239701678699134411, 3239701176675672896, 502023461515),
    (6479403357398268822, 3239701678699134411, 3239701678699134411),
    (12958806714796537644, 6479403357398268822, 6479403357398268822),
    (25917613429593075288, 12958806714796537644, 12958806714796537644),
    (51835226859186150576, 25917613429593075288, 25917613429593075288),
    (103670453718372301152, 51835226859186150576, 51835226859186150576),
    (207340907436744602304, 103670453718372301152, 103670453718372301152),
    (414681814873489204608, 207340907436744602304, 207340907436744602304),
    (829363629746978409216, 414681814873489204608, 414681814873489204608),
    (1658727259493956818432, 829363629746978409216, 829363629746978409216),
    (3317454518987913636864, 1658727259493956818432, 1658727259493956818432),
    (3317454519891555867591, 3317454518987913636864, 903642230727),
    (6634909039783111735182, 3317454519891555867591, 3317454519891555867591),
    (13269818079566223470364, 6634909039783111735182, 6634909039783111735182),
    (13269818079867437547273, 13269818079566223470364, 301214076909),
    (26539636159734875094546, 13269818079867437547273, 13269818079867437547273),
    (53079272319469750189092, 26539636159734875094546, 26539636159734875094546),
    (106158544638939500378184, 53079272319469750189092, 53079272319469750189092),
    (212317089277879000756368, 106158544638939500378184, 106158544638939500378184),
    (424634178555758001512736, 212317089277879000756368, 212317089277879000756368),
    (849268357111516003025472, 424634178555758001512736, 424634178555758001512736),
    (849268357111817217102381, 849268357111516003025472, 301214076909),
    (1698536714223634434204762, 849268357111817217102381, 849268357111817217102381),
    (3397073428447268868409524, 1698536714223634434204762, 1698536714223634434204762),
    (6794146856894537736819048, 3397073428447268868409524, 3397073428447268868409524),
    (6794146856894638141511351, 6794146856894537736819048, 100404692303),
    (13588293713789276283022702, 6794146856894638141511351, 6794146856894638141511351),
    (27176587427578552566045404, 13588293713789276283022702, 13588293713789276283022702),
    (54353174855157105132090808, 27176587427578552566045404, 27176587427578552566045404),
    (108706349710314210264181616, 54353174855157105132090808, 54353174855157105132090808),
    (217412699420628420528363232, 108706349710314210264181616, 108706349710314210264181616),
    (217412699420628721742440141, 217412699420628420528363232, 301214076909),
    (434825398841257443484880282, 217412699420628721742440141, 217412699420628721742440141),
    (869650797682514886969760564, 434825398841257443484880282, 434825398841257443484880282),
    (1739301595365029773939521128, 869650797682514886969760564, 869650797682514886969760564),
    (3478603190730059547879042256, 1739301595365029773939521128, 1739301595365029773939521128),
    (6957206381460119095758084512, 3478603190730059547879042256, 3478603190730059547879042256),
    (13914412762920238191516169024, 6957206381460119095758084512, 6957206381460119095758084512),
    (13914412762920239095158399751, 13914412762920238191516169024, 903642230727),
    (27828825525840478190316799502, 13914412762920239095158399751, 13914412762920239095158399751),
    (55657651051680956380633599004, 27828825525840478190316799502, 27828825525840478190316799502),
    (111315302103361912761267198008, 55657651051680956380633599004, 55657651051680956380633599004),
    (222630604206723825522534396016, 111315302103361912761267198008, 111315302103361912761267198008),
    (445261208413447651045068792032, 222630604206723825522534396016, 222630604206723825522534396016),
    (890522416826895302090137584064, 445261208413447651045068792032, 445261208413447651045068792032),
    (1781044833653790604180275168128, 890522416826895302090137584064, 890522416826895302090137584064),
    (1781044833653790605083917398855, 1781044833653790604180275168128, 903642230727),
    (3562089667307581210167834797710, 1781044833653790605083917398855, 1781044833653790605083917398855),
    (7124179334615162420335669595420, 3562089667307581210167834797710, 3562089667307581210167834797710),
    (14248358669230324840671339190840, 7124179334615162420335669595420, 7124179334615162420335669595420),
    (28496717338460649681342678381680, 14248358669230324840671339190840, 14248358669230324840671339190840),
    (56993434676921299362685356763360, 28496717338460649681342678381680, 28496717338460649681342678381680),
    (113986869353842598725370713526720, 56993434676921299362685356763360, 56993434676921299362685356763360),
    (227973738707685197450741427053440, 113986869353842598725370713526720, 113986869353842598725370713526720),
    (455947477415370394901482854106880, 227973738707685197450741427053440, 227973738707685197450741427053440),
    (911894954830740789802965708213760, 455947477415370394901482854106880, 455947477415370394901482854106880),
)


def chain_source(chain=CHAIN, target=D):
    """Validate every exponent addition and emit its paid multiplication."""
    known = {1: 'q'}
    source = []
    dependencies = {}
    for exponent, left, right in chain:
        assert all(isinstance(v, int) and v > 0 for v in (exponent, left, right))
        assert left in known and right in known
        assert exponent == left+right and exponent not in known
        assert exponent > max(known), 'Exponents are emitted in increasing order.'
        name = 'Q' if exponent == target else f'addition_power{exponent}'
        source.append((name, '*', known[left], known[right]))
        known[exponent] = name
        dependencies[exponent] = (left, right)
    assert chain[-1][0] == target and known[target] == 'Q'
    needed = {target}
    todo = [target]
    while todo:
        exponent = todo.pop()
        if exponent == 1:
            continue
        for v in dependencies[exponent]:
            if v not in needed:
                needed.add(v)
                todo.append(v)
    assert needed == set(known), 'The published chain has no unused paid steps.'
    return source


def rewrite_raw(old, *, merge_bound=True, chain=CHAIN):
    assert old['form'] == 'raw'
    width = old['width']
    old_chain = compiler.parent.recoder.power_chain(width)
    expected_bound = ('program_duration_bound', '+', 'program_bound', 'program_duration_gap')
    assert old['source'][0] == expected_bound
    assert old['source'][1:1+len(old_chain)] == old_chain
    rest = old['source'][1+len(old_chain):]
    private = {n for n, _, _, _ in old_chain}-{ 'Q' }
    assert all(v not in private for _, _, a, b in rest for v in (a, b))
    assert all(v not in private for pair in old['comparisons'] for v in pair)
    replacement = chain_source(chain, width)
    alias = lambda v: 'program_E' if merge_bound and v == 'program_bound' else v
    source = [expected_bound]+replacement+rest
    source = [(n, op, alias(a), alias(b)) for n, op, a, b in source]
    pairs = [(alias(a), alias(b)) for a, b in old['comparisons']]
    parameters = [n for n in old['parameters'] if not (merge_bound and n == 'program_bound')]
    packet = dict(old, source=source, comparisons=pairs, parameters=parameters,
                  addition_chain=tuple(chain), power_chain_operations=len(replacement),
                  binary_power_chain_operations=len(old_chain), bound_is_program_E=merge_bound)
    compiler.recount(packet)
    compiler.check_source(packet)
    return packet


def build(form='normalized', *, merge_bound=True):
    assert form in ('raw', 'units', 'normalized')
    table, counts, machine, summary, recipe = parent.components()
    assert recipe['D'] == D
    packet = rewrite_raw(compiler.raw_build(D, counts['beta'], counts['e_u_length']),
                         merge_bound=merge_bound)
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
    assert len(source) == base+len(CHAIN)
    assert (packet['witnesses'], packet['equations']) == (witnesses, equations)
    assert packet['parameters'] == [n for n in compiler.PARAMETERS
                                   if not (packet['bound_is_program_E'] and n == 'program_bound')]
    return dict(form=packet['form'], width=D, power_chain_operations=len(CHAIN),
                saved_multiplications=160-len(CHAIN),
                certificate={k: packet[k] for k in ('operations', 'multiplications',
                            'additions_subtractions', 'equations', 'witnesses')},
                polynomial=dict(operations=len(source), multiplications=counts['M'],
                                additions_subtractions=counts['A'], output=out),
                parameters=packet['parameters'], bound_is_program_E=packet['bound_is_program_E'],
                **compiler.degree_upper_bound(packet))


def execute_mod(source, values, constants, modulus):
    env = {n: v % modulus for n, v in values.items()}
    def get(v):
        if isinstance(v, str):
            return env[v]
        if isinstance(v, compiler.Numeral):
            return constants[v.name] % modulus
        return v % modulus
    for n, op, a, b in source:
        aa, bb = get(a), get(b)
        env[n] = (aa*bb if op == '*' else aa+bb if op == '+' else aa-bb) % modulus
    return env


def verify():
    assert len(CHAIN) == 131
    assert CHAIN[43][0] == 100404692303
    assert CHAIN[121][0] == 100404692303*17738661339441947785
    assert D == (1 << 9)*100404692303*17738661339441947785
    source = chain_source()
    rng = random.Random(528322206)
    powers = 0
    for modulus in (2, 4, 8, 15, 97, 257, 1009, 65537, 1000000007):
        for q in (-100, -17, -2, -1, 0, 1, 2, 3, 16, 97, modulus, modulus+1):
            env = execute_mod(source, {'q': q}, {}, modulus)
            assert env['Q'] == pow(q, D, modulus)
            # Every node is checked by modular powering independently of its parents.
            for exponent, _, _ in CHAIN:
                name = 'Q' if exponent == D else f'addition_power{exponent}'
                assert env[name] == pow(q, exponent, modulus)
            powers += 1
    table, counts, machine, summary, recipe = parent.components()
    ledgers = []
    identities = signed = 0
    for form in ('raw', 'units', 'normalized'):
        old = compiler.build(D, counts['beta'], counts['e_u_length'], form)
        osource, oout = compiler.parent.polynomial_source(old)
        for merge_bound in (False, True):
            packet = build(form, merge_bound=merge_bound)
            newsource, newout = compiler.parent.polynomial_source(packet)
            assert packet['auxiliaries'] == old['auxiliaries']
            assert packet['comparisons'] == old['comparisons']
            old_names = {n for n, _, _, _ in osource}
            common = old_names & {n for n, _, _, _ in newsource}
            for case in range(192):
                modulus = (257, 65537, 1000000007, 1048576)[case % 4]
                values = {n: rng.randrange(1, 20) if case < 96 else rng.randrange(-20, 21)
                          for n in packet['parameters']+packet['auxiliaries']}
                constants = {n: rng.randrange(-1000, 1001) for n in compiler.NUMERALS}
                restored = dict(values)
                if merge_bound:
                    restored['program_bound'] = values['program_E']
                before = execute_mod(osource, restored, constants, modulus)
                after = execute_mod(newsource, values, constants, modulus)
                assert all(before[n] == after[n] for n in common)
                assert before[oout] == after[newout]
                identities += 1
                signed += case >= 96
            ledgers.append(ledger(packet))
    # E is the sentinel of PREFIX MIDDLE TAIL. Test the exact counter
    # consequence without allocating the n-long input word or 2**n.
    counter_cases = 0
    for _ in range(96):
        prefix = ''.join(rng.choice('01') for _ in range(rng.randrange(1, 25)))
        middle = ''.join(rng.choice('01') for _ in range(rng.randrange(1, 25)))
        tail = ''.join(rng.choice('01') for _ in range(rng.randrange(1, 25)))
        E = int('1'+prefix+middle+tail, 2)
        overhead = rng.randrange(1, len(prefix)+len(middle)+1)
        assert E >= overhead >= 1
        n = 1 << E.bit_length()
        assert n > E and n > (overhead+127)//128
        tape_length = 128*n+overhead
        assert 128*n < tape_length < 256*n
        assert 1 << (tape_length-1).bit_length() == 256*n
        counter_cases += 1
    packet = build()
    final_source, final_out = compiler.parent.polynomial_source(packet)
    encoded = compiler.encode_source(final_source)
    record = ledger(packet)
    assert record['polynomial']['operations'] == 528
    assert (record['polynomial']['multiplications'], record['polynomial']['additions_subtractions']) == (322, 206)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_TAG_CHAIN',
                addition_chain=CHAIN, exponent=D, chain_multiplications=len(CHAIN),
                independent_modular_power_cases=powers,
                independent_modular_node_checks=powers*len(CHAIN),
                full_modular_source_identities=identities, signed_cases=signed,
                exact_counter_bound_cases=counter_cases, ledgers=ledgers,
                fixed_recipe=recipe, source_sha256=hashlib.sha256(
                    json.dumps(encoded, sort_keys=True).encode()).hexdigest(),
                example=dict(source=encoded, output=final_out, comparisons=packet['comparisons'],
                             parameters=packet['parameters'], auxiliaries=packet['auxiliaries'],
                             fixed_numeral_definitions=compiler.NUMERALS),
                scope='One fixed universal polynomial with four positive program parameters, '
                      'ordinary positive input, 69 positive witnesses and 528 paid operations. '
                      'The exact exponent chain is verified, not claimed optimal. '
                      'Degree upper bound only. Modular identities do not materialize a full '
                      'native Pell zero or any giant fixed coefficient.')


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
