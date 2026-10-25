"""Independent five-way multinomial/SOS verification of actual artifacts. CODE ONLY/HOLD."""
import argparse
import copy
import hashlib
import importlib.util
import json
from math import comb
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CORE = {'README.md', 'PROOF.md', 'TOOLCHAIN.md', 'guard.py', 'build.py',
        'check.py', 'SOURCE_PINS.json'}
hold = json.loads((HERE / 'HOLD_INVENTORY.json').read_text())
if hold.get('schema') != 'held_pell_output_gate_shear_finite_v1' or set(hold['files']) != CORE:
    raise ValueError('bootstrap HOLD schema/closure')
for name, expected in hold['files'].items():
    path = HERE / name
    raw = path.read_bytes()
    if path.is_symlink() or {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()} != expected:
        raise ValueError('bootstrap held bytes: ' + name)
spec = importlib.util.spec_from_file_location('pell_output_shear_check_guard', HERE / 'guard.py')
G = importlib.util.module_from_spec(spec)
spec.loader.exec_module(G)


def coefficients(raw, dimension):
    G.need(type(raw) is list, 'term list type')
    result = {}
    for pair in raw:
        G.need(type(pair) is list and len(pair) == 2, 'term pair shape')
        c, monomial = pair
        G.need(type(c) is int, 'integer coefficient')
        G.need(type(monomial) is list, 'monomial list type')
        G.need(all(type(i) is int and 0 <= i < dimension for i in monomial),
               'integer index')
        key = tuple(sorted(monomial))
        result[key] = result.get(key, 0) + c
    return {m: c for m, c in result.items() if c != 0}


def serialized(polynomial):
    return [[polynomial[m], list(m)] for m in sorted(polynomial)]


def substitute(polynomial, direction):
    """Five-way multinomial; direction -1 is T, +1 its exact inverse."""
    G.need(type(direction) is int and direction in (-1, 1), 'substitution direction')
    result = {}
    for monomial, value in polynomial.items():
        power = monomial.count(35)
        rest = tuple(i for i in monomial if i != 35)
        for ia in range(power + 1):
            for ic in range(power - ia + 1):
                for ip in range(power - ia - ic + 1):
                    for ir in range(power - ia - ic - ip + 1):
                        iv = power - ia - ic - ip - ir
                        ways = (comb(power, ia)*comb(power-ia, ic)*
                                comb(power-ia-ic, ip)*comb(power-ia-ic-ip, ir))
                        key = tuple(sorted(rest+(10,)*ia+(12,)*ic+(25,)*ip+
                                           (27,)*ir+(35,)*iv))
                        c = value*ways*(4*direction)**ia*(5*direction)**ic
                        c *= (2*direction)**ip*direction**ir
                        result[key] = result.get(key, 0) + c
    return {m: c for m, c in result.items() if c}


def plus(*polynomials):
    result = {}
    for polynomial in polynomials:
        for m, c in polynomial.items():
            result[m] = result.get(m, 0) + c
    return {m: c for m, c in result.items() if c}


def scale(polynomial, c):
    return {m: c*v for m, v in polynomial.items() if c*v}


def const(c):
    return {(): c} if c else {}


def var(i):
    return {(i,): 1}


def linear(*pairs):
    return plus(*(scale(var(i), c) for c, i in pairs))


def square_pairs(polynomial):
    result = {}
    entries = sorted(polynomial.items())
    for i, (m, c) in enumerate(entries):
        for j in range(i, len(entries)):
            n, d = entries[j]
            key = tuple(sorted((*m, *n)))
            result[key] = result.get(key, 0) + c*d*(1 if i == j else 2)
    return {m: c for m, c in result.items() if c}


def sos(rows):
    result = {}
    for row in rows:
        for m, c in square_pairs(row).items():
            result[m] = result.get(m, 0) + c
    return {m: c for m, c in result.items() if c}


def ordinary_formulas(profile):
    L = linear((-2, 10), (-4, 11), (2, 12), (2, 21), (2, 25))
    H = linear((4, 10), (5, 12), (2, 25), (1, 27))
    argument = linear((8, 10), (10, 12), (4, 25), (2, 27), (2, 35))
    A = plus(var(35), scale(square_pairs(L), -1), scale(L, 8), const(-12))
    B = plus(var(36), scale(square_pairs(argument), -1),
             linear((-24, 10), (-26, 12), (-8, 25), (-6, 27), (-4, 35)), const(-3))
    newB = plus(var(36), {(35, 35): -4},
                linear((-8, 10), (-6, 12), (-2, 27), (-4, 35)), const(-3))
    consumer = plus(linear((1, 14), (-1, 15), (6, 70), (-1, 75)), {(36, 70): -2})
    label = linear((-1, 10), (-1, 11), (-4, 21), (-2, 24), (-4, 26),
                   (-2, 29), (-2, 31), (-4, 32), (-2, 34), (-2, 36),
                   (-4, 39), (-2, 40), (-2, 43), (-2, 47), (-4, 68),
                   (-2, 69), (1, 105 if profile == 'plain' else 106))
    return {19: A, 20: B, 59: consumer, 90 if profile == 'plain' else 91: label}, {
        19: plus(A, scale(H, -1)), 20: newB}


def local_tables(profile):
    # Every entry is literal (monomial word, old coefficient, new coefficient).
    # Words use distinct coordinate aliases; repeated letters are powers.
    aliases = {'a': 10, 'b': 11, 'c': 12, 'u': 21, 'p': 25, 'r': 27, 'v': 35, 'k': 36}
    cells = [
        ('aaaa',16812,12716), ('aaac',57172,36692), ('aaap',8208,16),
        ('aaar',15232,11136), ('aacc',93109,54709), ('aacp',31104,384),
        ('aacr',47616,32256), ('aapp',6384,240), ('aapr',6336,192),
        ('aarr',7488,5952), ('accc',71162,39162), ('accp',39744,1344),
        ('accr',52224,33024), ('acpp',15552,192), ('acpr',15360,0),
        ('acrr',16128,12288), ('appp',2112,64), ('appr',3264,192),
        ('aprr',1728,192), ('arrr',2560,2304), ('cccc',26365,16365),
        ('cccp',22416,6416), ('cccr',22480,14480), ('ccpp',12576,2976),
        ('ccpr',10368,768), ('ccrr',12192,9792), ('cppp',3456,896),
        ('cppr',4224,384), ('cprr',2304,384), ('crrr',4480,4160),
        ('pppp',896,640), ('pppr',640,128), ('pprr',576,192),
        ('prrr',256,128), ('rrrr',864,848),
        ('aaav',4096,0), ('aacv',15360,0), ('aapv',6144,0),
        ('aarv',3072,0), ('aavv',1536,0), ('accv',19200,0),
        ('acpv',15360,0), ('acrv',7680,0), ('acvv',3840,0),
        ('appv',3072,0), ('aprv',3072,0), ('apvv',1536,0),
        ('arrv',768,0), ('arvv',768,0), ('avvv',256,0),
        ('cccv',8000,0), ('ccpv',9600,0), ('ccrv',4800,0),
        ('ccvv',2400,0), ('cppv',3840,0), ('cprv',3840,0),
        ('cpvv',1920,0), ('crrv',960,0), ('crvv',960,0),
        ('cvvv',320,0), ('pppv',512,0), ('pprv',768,0),
        ('ppvv',384,0), ('prrv',384,0), ('prvv',384,0),
        ('pvvv',128,0), ('rrrv',64,0), ('rrvv',96,0), ('rvvv',64,0), ('vvvv',16,16),
        ('aaa',3044,4), ('aac',16016,4984), ('aap',3120,-1024),
        ('aar',2686,390), ('acc',23310,10142), ('acp',11584,1808),
        ('acr',8700,3180), ('app',1584,-208), ('apr',896,-1168), ('arr',80,-496),
        ('ccc',13752,8592), ('ccp',8782,3118), ('ccr',4558,1286),
        ('cpp',2352,312), ('cpr',1664,-752), ('crr',256,-432),
        ('ppp',-240,-480), ('ppr',-320,-760), ('prr',-512,-768), ('rrr',-416,-464),
        ('aab',1764,1892), ('abb',2520,2648), ('abc',4772,4804),
        ('abu',1916,1788), ('abp',-2176,-2240), ('abr',-816,-784),
        ('bbc',6830,6990), ('bbp',-946,-882), ('bbr',-920,-888),
        ('bcc',14088,13928), ('bcu',1376,1216), ('bcp',7292,7068),
        ('bcr',-320,-352), ('bup',1536,1472), ('bur',-384,-416),
        ('bpp',256,192), ('bpr',-1152,-1184), ('aau',718,654),
        ('acu',1072,1056), ('auu',544,576), ('aup',768,800), ('aur',-96,-112),
        ('ccu',-432,-352), ('cuu',-344,-304), ('cup',-768,-656), ('cur',-512,-496),
        ('uup',-384,-368), ('uur',-96,-88), ('upp',-384,-352), ('upr',0,16),
        ('bbb',2156,2156), ('bbu',1534,1534), ('buu',896,896),
        ('brr',-1096,-1096), ('uuu',576,576), ('urr',-304,-304),
        ('aav',2040,-8), ('acv',4880,16), ('apv',1808,16), ('arv',1024,0),
        ('avv',448,64), ('ccv',2872,-8), ('cpv',2096,-16), ('crv',1216,0),
        ('cvv',528,48), ('ppv',376,-8), ('prv',448,0), ('pvv',192,0),
        ('rrv',128,0), ('rvv',112,16), ('vvv',32,32),
        ('abv',-32,-32), ('auv',16,16), ('bbv',-32,-32),
        ('bcv',32,32), ('buv',32,32), ('bpv',32,32),
        ('cuv',-16,-16), ('uuv',-8,-8), ('upv',-16,-16),
        ('aak',-128,0), ('ack',-320,0), ('apk',-128,0),
        ('ark',-64,0), ('avk',-64,0), ('cck',-200,0),
        ('cpk',-160,0), ('crk',-80,0), ('cvk',-80,0),
        ('ppk',-32,0), ('prk',-32,0), ('pvk',-32,0),
        ('rrk',-8,0), ('rvk',-16,0), ('vvk',-8,-8),
        ('aa',3445,2693), ('ac',4364,2324), ('ap',2216,1400), ('ar',2708,2300),
        ('cc',7422,6047), ('cp',4072,2972), ('cr',1732,1182), ('pp',2069,1849),
        ('pr',2128,1908), ('rr',1145,1090), ('ab',5342,5598), ('bc',5078,5398),
        ('bp',2592,2720), ('br',1776,1840), ('au',-480,-608), ('cu',712,552),
        ('up',704,640), ('ur',0,-32), ('av',352,24), ('cv',480,70),
        ('pv',192,28), ('rv',96,14), ('ak',-44,-12), ('ck',-52,-12),
        ('pk',-16,0), ('rk',-12,-4)]
    before, after, keys = {}, {}, set()
    for word, old, new in cells:
        m = tuple(sorted(aliases[x] for x in word))
        G.need(m not in keys, 'ordinary table duplicate')
        keys.add(m)
        if profile == 'weighted' and word == 'abb':
            old, new = old+2, new+2
        if old:
            before[m] = old
        if new:
            after[m] = new
    G.need(len(cells) == len(keys) == 191 and len(before) == 189 and len(after) == 136,
           'ordinary complete table schema')
    return before, after, keys


def expected_policy():
    return {'name': 'fixed_pell_output_gate_shear_4_5_2_1', 'targets': [35],
            'target_literal_names': ['mul.137'], 'fixed_inputs': [10, 12, 25, 27],
            'fixed_input_literal_names': ['crt.encoded.a', 'crt.encoded.c', 'mul.64', 'mul.75'],
            'forward_terms': [[[-4, [10]], [-5, [12]], [-2, [25]], [-1, [27]], [1, [35]]]],
            'inverse_terms': [[[4, [10]], [5, [12]], [2, [25]], [1, [27]], [1, [35]]]],
            'all_other_coordinates': 'identity', 'search': False,
            'combined_crt_family_change': False}


def independently_count(equation, rows, polynomial):
    dimension = len(equation['variables'])
    used = sorted(set(i for m in polynomial for i in m))
    degrees = {}
    for degree in sorted(set(map(len, polynomial))):
        values = [c for m, c in polynomial.items() if len(m) == degree]
        degrees[str(degree)] = {'terms': len(values), 'height': max(abs(c) for c in values)}
    return {'variables': dimension, 'rows': len(rows), 'degree': max(map(len, polynomial), default=0),
            'monomials': len(polynomial), 'height': max((abs(c) for c in polynomial.values()), default=0),
            'row_height': max((abs(c) for row in rows for c in row.values()), default=0),
            'row_degree': max((len(m) for row in rows for m in row), default=0),
            'used_coordinates': used, 'unconstrained_coordinates': [i for i in range(dimension) if i not in used],
            'degree_census': degrees}


def support_theorem(polynomial, rows, context):
    old = context['collected']
    before, after, keys = local_tables(context['profile'])
    G.need({m: c for m, c in old.items() if m in keys} == before,
           'whole old ordinary191 table')
    G.need({m: c for m, c in polynomial.items() if m in keys} == after,
           'whole actual ordinary191 table')
    G.need({m: c for m, c in old.items() if m not in keys} ==
           {m: c for m, c in polynomial.items() if m not in keys},
           'all outside-table coefficient identity')
    deleted, introduced = set(old)-set(polynomial), set(polynomial)-set(old)
    G.need(len(deleted) == 55 and introduced == {(21, 25, 27), (21, 27)} and
           {d: sum(len(m) == d for m in deleted) for d in (2, 3, 4)} ==
           {2: 1, 3: 19, 4: 35} and len(old)-len(polynomial) == 53,
           'whole support55/2/net53 theorem')
    high = {m: c for m, c in old.items() if len(m) == 4 and abs(c) > 54709}
    G.need(high == {(10, 10, 10, 12): 57172, (10, 10, 12, 12): 93109,
                    (10, 12, 12, 12): 71162} and
           polynomial.get((10, 10, 12, 12)) == 54709, 'old height boundary/witness')
    G.need(all(abs(c) <= {0: 2674, 1: 2116, 2: 10576, 3: 48942, 4: 54709}[len(m)]
               for m, c in polynomial.items()) and
           {m: c for m, c in old.items() if len(m) <= 1} ==
           {m: c for m, c in polynomial.items() if len(m) <= 1},
           'whole degree height bounds/low-term identity')
    G.need([(i, m, c) for i, row in enumerate(context['rows'])
            for m, c in row.items() if abs(c) > 128] == [(20, (10, 12), -160)] and
           rows[12].get((10, 12)) == -128 and
           max(abs(c) for c in rows[19].values()) == 32 and
           max(abs(c) for c in rows[20].values()) == 8,
           'row height boundary/witness')
    G.need([len(context['rows'][i]) for i in (19, 20)] == [22, 22] and
           [len(rows[i]) for i in (19, 20)] == [23, 7] and
           sum(len(r) for r in context['rows'])-sum(len(r) for r in rows) == 14,
           'row support14 theorem')
    G.need([polynomial.get((i,)*4) for i in (10, 12, 25, 27)] ==
           [12716, 16365, 640, 848], 'exceptional liveness witnesses')
    return {'ordinary_table_cells': 191, 'old_table_terms': 189, 'new_table_terms': 136,
            'removed_old_monomials': 55, 'introduced_monomials': 2, 'net_terms_removed': 53,
            'removed_by_degree': {'2': 1, '3': 19, '4': 35},
            'introduced_full_monomials': [[21, 27], [21, 25, 27]],
            'coefficient_absolute_values_nonincreasing_claimed': False,
            'all_outside_table_coefficients_unchanged': True,
            'all_linear_and_constant_coefficients_unchanged': True,
            'whole_lower_degree_bounds': {'0': 2674, '1': 2116, '2': 10576, '3': 48942},
            'residual_monomial_occurrences_removed': 14}


def prepare(profile):
    old = G.source(profile, 'equation.json')
    n = len(old['variables'])
    G.need(n == (316 if profile == 'plain' else 315) and
           len(old['residuals']) == (218 if profile == 'plain' else 217), 'parent dimension/rows')
    names = [v['name'] for v in old['variables']]
    G.need(len(names) == len(set(names)) and
           [names[i] for i in (10, 11, 12, 21, 25, 27, 35, 36)] ==
           ['crt.encoded.a', 'crt.encoded.b', 'crt.encoded.c', 'mul.40',
            'mul.64', 'mul.75', 'mul.137', 'add.142'], 'parent literal names')
    rows = [coefficients(r['terms'], n) for r in old['residuals']]
    oldpoly = G.source(profile, 'expanded_polynomial.json')
    collected = coefficients(oldpoly['terms'], n)
    G.need(sos(rows) == collected, 'parent whole SOS')
    G.need(G.equal(independently_count(old, rows, collected), G.source(profile, 'METRICS.json')),
           'parent complete census')
    occurrences = {str(j): [i for i, row in enumerate(rows) if any(j in m for m in row)]
                   for j in (35, 36)}
    G.need(occurrences == {'35': [19, 20],
                           '36': [20, 59, 90 if profile == 'plain' else 91]},
           'whole occurrence closure')
    old_formulas, formulas = ordinary_formulas(profile)
    for i, expected in old_formulas.items():
        G.need(rows[i] == expected, 'ordinary full old residual/consumer formula')
    transformed = [substitute(row, -1) for row in rows]
    changed = [i for i, (a, b) in enumerate(zip(rows, transformed)) if a != b]
    G.need(changed == sorted(formulas) == [19, 20], 'complete2 changed-row coverage')
    for i, row in enumerate(transformed):
        G.need(row == (formulas[i] if i in formulas else rows[i]), 'ordinary/unchanged full row')
    whole = sos(transformed)
    G.need(whole == substitute(collected, -1), 'forward whole quartic identity')
    G.need(substitute(whole, 1) == collected, 'inverse whole quartic identity')
    parent = G.source(profile, 'COMPOSED_MAPS.json')
    centered = parent['parent_balanced_maps']['parent_centered_maps']
    G.need(len(centered['translation']['shifts']) == 58 and
           len(centered['parent_maps']['actual_free_factored_coordinates']) == 83 and
           len(centered['parent_maps']['reverse_monic_restorations']) == (204 if profile == 'plain' else 203),
           'parent whole witness-map counts')
    context = {'profile': profile, 'old': old, 'rows': rows, 'n': n, 'oldpoly': oldpoly,
               'collected': collected, 'transformed': transformed, 'whole': whole,
               'formulas': formulas, 'changed': changed, 'occurrences': occurrences, 'parent': parent}
    support_theorem(whole, transformed, context)
    return context


def check_index(bundle):
    index = bundle['INDEX.json']
    G.need(index.get('schema') == 'pell_output_gate_shear_data_inventory_v1', 'data index schema')
    G.need(G.equal(index.get('policy'), expected_policy()), 'data index policy')
    expected = {'schema': 'pell_output_gate_shear_data_inventory_v1', 'policy': expected_policy(),
                'files': G.bundle_records({k: v for k, v in bundle.items() if k != 'INDEX.json'}),
                'source_pins': G.record(HERE / 'SOURCE_PINS.json'),
                'producer': G.record(HERE / 'build.py'), 'checker': G.record(HERE / 'check.py'),
                'guard': G.record(HERE / 'guard.py')}
    G.need(G.equal(index, expected), 'whole data index binding')


def verify_profile(bundle, profile, context):
    pre = profile + '/'
    old, n = context['old'], context['n']
    equation = bundle[pre + 'equation.json']
    cert = bundle[pre + 'shear_certificate.json']
    G.need(cert.get('schema') == 'pell_output_gate_shear_v1', 'shear schema')
    G.need(cert.get('convention') == 'neighbor_x = pell_output_shear(new_z)', 'shear convention')
    inverse = 'new_z35 = neighbor_x35+4neighbor_x10+5neighbor_x12+2neighbor_x25+neighbor_x27'
    G.need(cert.get('inverse_convention') == inverse, 'shear inverse convention')
    policy = cert.get('policy', {})
    G.need(G.equal(policy.get('forward_terms'), expected_policy()['forward_terms']), 'shear direction')
    G.need(G.equal(policy.get('inverse_terms'), expected_policy()['inverse_terms']), 'shear inverse')
    G.need(G.equal(policy, expected_policy()), 'shear policy')
    G.need(G.equal(cert.get('input'), G.source_record(profile, 'equation.json')), 'shear input binding')
    G.need(G.equal(cert.get('changed_rows'), context['changed']), 'shear changed coverage')
    G.need(G.equal(cert.get('complete_occurrences'), context['occurrences']), 'shear occurrence coverage')
    pins = G.obj(HERE / 'SOURCE_PINS.json')
    G.need(G.equal(cert.get('ordinary_proposal'), pins['ordinary_shear_manifest']), 'shear ordinary binding')
    chart = G.record_bytes(G.encode(equation))
    expected_cert = {'schema': 'pell_output_gate_shear_v1', 'profile': profile,
                     'input': G.source_record(profile, 'equation.json'), 'output': chart,
                     'convention': 'neighbor_x = pell_output_shear(new_z)', 'inverse_convention': inverse,
                     'policy': expected_policy(), 'changed_rows': context['changed'],
                     'complete_occurrences': context['occurrences'],
                     'ordinary_proposal': pins['ordinary_shear_manifest']}
    G.need(G.equal(cert, expected_cert), 'whole shear certificate')
    oldmeta = {k: v for k, v in old.items() if k != 'residuals'}
    oldmeta['variant'] += ':pell_output_gate_shear_4_5_2_1'
    G.need(G.equal({k: v for k, v in equation.items() if k != 'residuals'}, oldmeta), 'equation metadata')
    rawrows = equation.get('residuals')
    G.need(type(rawrows) is list and len(rawrows) == len(context['rows']), 'complete row count')
    rows = []
    for i, (actual, source) in enumerate(zip(rawrows, old['residuals'])):
        G.need(G.equal({k: v for k, v in actual.items() if k != 'terms'},
                       {k: v for k, v in source.items() if k != 'terms'}), 'row metadata')
        row = coefficients(actual['terms'], n)
        G.need(row == context['transformed'][i], 'forward row identity')
        G.need(row == (context['formulas'][i] if i in context['formulas'] else context['rows'][i]),
               'actual ordinary/unchanged residual formula')
        rows.append(row)
    expanded = bundle[pre + 'expanded_polynomial.json']
    G.need(G.equal({k: v for k, v in expanded.items() if k != 'terms'},
                   {k: v for k, v in context['oldpoly'].items() if k != 'terms'}), 'expanded metadata')
    polynomial = coefficients(expanded['terms'], n)
    G.need(polynomial == sos(rows) == context['whole'], 'full SOS coefficient identity')
    G.need(substitute(polynomial, 1) == context['collected'], 'inverse whole quartic identity')
    theorem = support_theorem(polynomial, rows, context)
    metrics = independently_count(equation, rows, polynomial)
    G.need(metrics['degree'] == 4 and metrics['row_degree'] <= 2 and
           metrics['used_coordinates'] == list(range(n)), 'quartic degree/liveness')
    G.need(G.equal(bundle[pre + 'METRICS.json'], metrics), 'complete census')
    G.need(metrics['monomials'] == (5728 if profile == 'plain' else 5734) and
           metrics['height'] == 54709 and metrics['row_height'] == 128,
           'ordinary full support/height deduction')
    G.need({d: cell['terms'] for d, cell in metrics['degree_census'].items()} ==
           {'0': 1, '1': 112, '2': 809 if profile == 'plain' else 808,
            '3': 1388 if profile == 'plain' else 1390, '4': 3418 if profile == 'plain' else 3423},
           'ordinary complete degree census')
    parent = context['parent']
    endpoint = G.source(profile, 'ENDPOINT_BINDING.json')
    expected_maps = {
        'schema': 'pell_output_gate_shear_composed_maps_v1', 'profile': profile,
        'chart': chart, 'shear': expected_policy(), 'parent_neighbor_maps': parent,
        'parent_neighbor_endpoint': endpoint,
        'parent_neighbor_shear_certificate': G.source(profile, 'shear_certificate.json'),
        'forward_order': parent['forward_order'] + ['apply_inverse_pell_output_shear_to_neighbor_tuple'],
        'inverse_order': ['apply_pell_output_shear_to_recover_neighbor_tuple'] + parent['inverse_order'],
        'new_chart_is_whole_integer_bijection': True,
        'old_private_witness_identity_claimed': False, 'source_or_native_program_rerun': False}
    G.need(G.equal(bundle[pre + 'COMPOSED_MAPS.json'], expected_maps), 'complete composed maps')
    expected_endpoint = {
        'schema': 'pell_output_gate_shear_endpoint_v1', 'profile': profile,
        'all_prior_profile_files': {f: G.record_bytes(G.encode(bundle[pre + f]))
                                    for f in G.PROFILE_FILES if f != 'ENDPOINT_BINDING.json'},
        'ordinary_shear_manifest': pins['ordinary_shear_manifest'],
        'accepted_neighbor_verification_manifest': pins['accepted_neighbor_verification_manifest'],
        'parent_neighbor_data_index': G.record(G.SOURCE / 'INDEX.json'),
        'source_calibration': endpoint['source_calibration'],
        'equivalence_chain': ['fixed_pell_output_unimodular_shear'] + endpoint['equivalence_chain'],
        'source_restored_before_calibration': True, 'search_or_optimality_claimed': False}
    G.need(G.equal(bundle[pre + 'ENDPOINT_BINDING.json'], expected_endpoint), 'complete endpoint binding')
    return {'metrics': metrics, 'changed_rows': context['changed'],
            'unchanged_rows': len(rows)-2, 'complete_occurrences': context['occurrences'],
            'whole_forward_and_inverse_coefficients': True, 'ordinary_replacement_formulas': 2, 'whole_old_consumer_formulas': 4,
            'support_and_height_theorem': theorem}


def verify_bundle(bundle, contexts, profiles=('plain', 'weighted')):
    G.need(set(bundle) == G.ARTIFACTS, 'data object inventory')
    check_index(bundle)
    return {p: verify_profile(bundle, p, contexts[p]) for p in profiles}


def rebind(bundle):
    """Rebind actual artifact bytes only; never repair mathematical/source fields."""
    for profile in ('plain', 'weighted'):
        pre = profile + '/'
        chart = G.record_bytes(G.encode(bundle[pre + 'equation.json']))
        bundle[pre + 'shear_certificate.json']['output'] = chart
        bundle[pre + 'COMPOSED_MAPS.json']['chart'] = chart
        bundle[pre + 'ENDPOINT_BINDING.json']['all_prior_profile_files'] = {
            f: G.record_bytes(G.encode(bundle[pre + f]))
            for f in G.PROFILE_FILES if f != 'ENDPOINT_BINDING.json'}
    bundle['INDEX.json']['files'] = G.bundle_records({k: v for k, v in bundle.items() if k != 'INDEX.json'})


def put(root, path, value):
    for part in path[:-1]:
        root = root[part]
    root[path[-1]] = value


def controls(bundle, contexts):
    negatives, valids = [], []
    for profile in ('plain', 'weighted'):
        pre = profile + '/'
        eq, poly, cert, maps, census, endpoint = (pre + f for f in
            ('equation.json', 'expanded_polynomial.json', 'shear_certificate.json',
             'COMPOSED_MAPS.json', 'METRICS.json', 'ENDPOINT_BINDING.json'))
        tests = []

        def add(name, path, value, reason):
            tests.append((name, lambda b, p=path, v=value: put(b, p, copy.deepcopy(v)), reason))

        add('wrong_direction_first_row', [eq, 'residuals', 19, 'terms'], contexts[profile]['old']['residuals'][19]['terms'], 'forward row identity')
        add('wrong_direction_second_row', [eq, 'residuals', 20, 'terms'], contexts[profile]['old']['residuals'][20]['terms'], 'forward row identity')
        changed = copy.deepcopy(bundle[eq]['residuals'][19]['terms'])
        for term in changed:
            if term[1] == [10, 12]:
                term[0] *= -1
        add('mixed_sign_actual_row', [eq, 'residuals', 19, 'terms'], changed, 'forward row identity')
        changed = copy.deepcopy(bundle[eq]['residuals'][20]['terms'])
        for term in changed:
            term[1] = [34 if i == 35 else i for i in term[1]]
        add('wrong_gate_actual_row', [eq, 'residuals', 20, 'terms'], changed, 'forward row identity')
        add('missing_whole_row', [eq, 'residuals'], bundle[eq]['residuals'][:19]+bundle[eq]['residuals'][20:], 'complete row count')
        add('missing_actual_term', [eq, 'residuals', 20, 'terms'], bundle[eq]['residuals'][20]['terms'][1:], 'forward row identity')
        add('unchanged_row_corruption', [eq, 'residuals', 0, 'terms', 0, 0], 7, 'forward row identity')
        add('preceding_row_corruption', [eq, 'residuals', 18, 'terms', 0, 0], bundle[eq]['residuals'][18]['terms'][0][0]+1, 'forward row identity')
        add('row_label', [eq, 'residuals', 19, 'label'], 'wrong', 'row metadata')
        add('integer_domain', [eq, 'domain'], 'positive integers', 'equation metadata')
        add('literal_name', [eq, 'variables', 35, 'name'], 'mul.138', 'equation metadata')
        add('boolean_coefficient', [eq, 'residuals', 19, 'terms', 0, 0], True, 'integer coefficient')
        add('float_coefficient', [eq, 'residuals', 19, 'terms', 0, 0], -12.0, 'integer coefficient')
        add('boolean_index', [eq, 'residuals', 19, 'terms'], bundle[eq]['residuals'][19]['terms']+[[1, [True]]], 'integer index')
        add('out_of_range_index', [eq, 'residuals', 19, 'terms'], bundle[eq]['residuals'][19]['terms']+[[1, [contexts[profile]['n']]]], 'integer index')
        add('quartic_coefficient', [poly, 'terms', 0, 0], bundle[poly]['terms'][0][0]+1, 'full SOS coefficient identity')
        add('dropped_quartic_term', [poly, 'terms'], bundle[poly]['terms'][1:], 'full SOS coefficient identity')
        add('boolean_quartic_coefficient', [poly, 'terms', 0, 0], True, 'integer coefficient')
        add('quartic_header', [poly, 'domain'], 'positive integers', 'expanded metadata')
        add('certificate_schema', [cert, 'schema'], 'wrong', 'shear schema')
        add('direction_convention', [cert, 'convention'], 'new_z = pell_output_shear(neighbor_x)', 'shear convention')
        add('inverse_convention', [cert, 'inverse_convention'], 'new_z = pell_output_shear(neighbor_x)', 'shear inverse convention')
        add('first_forward_sign', [cert, 'policy', 'forward_terms', 0, 0, 0], 4, 'shear direction')
        add('second_forward_sign', [cert, 'policy', 'forward_terms', 0, 1, 0], 5, 'shear direction')
        add('inverse_map_sign', [cert, 'policy', 'inverse_terms', 0, 3, 0], -1, 'shear inverse')
        add('wrong_gate_schema', [cert, 'policy', 'targets', 0], 34, 'shear policy')
        add('boolean_gate_schema', [cert, 'policy', 'targets', 0], True, 'shear policy')
        add('stale_input_binding', [cert, 'input', 'sha256'], '0'*64, 'shear input binding')
        add('changed_row_coverage', [cert, 'changed_rows'], contexts[profile]['changed'][1:], 'shear changed coverage')
        add('occurrence_coverage', [cert, 'complete_occurrences', '35'], [20], 'shear occurrence coverage')
        add('ordinary_proof_binding', [cert, 'ordinary_proposal', 'sha256'], '0'*64, 'shear ordinary binding')
        add('inverse_map_order', [maps, 'inverse_order'], list(reversed(bundle[maps]['inverse_order'])), 'complete composed maps')
        nested = ['parent_neighbor_maps', 'parent_balanced_maps', 'parent_centered_maps', 'parent_maps']
        old_private = bundle[maps]['parent_neighbor_maps']['parent_balanced_maps']['parent_centered_maps']['parent_maps']
        free = old_private['actual_free_factored_coordinates']
        add('free_coordinate_omission', [maps]+nested+['actual_free_factored_coordinates'], free[1:], 'complete composed maps')
        monic = copy.deepcopy(old_private['reverse_monic_restorations'])
        monic[0]['restoration'][0][0] += 1
        add('monic_restoration', [maps]+nested+['reverse_monic_restorations'], monic, 'complete composed maps')
        add('parent_balanced_map_sign', [maps, 'parent_neighbor_maps', 'parent_balanced_maps', 'shear', 'forward_terms', 0, 0], 2, 'complete composed maps')
        add('source_calibration', [maps, 'parent_neighbor_maps', 'parent_balanced_maps', 'parent_centered_maps', 'source_binding', 'interval_triples_fresh_across_reparameterization'], False, 'complete composed maps')
        add('native_rerun_claim', [maps, 'source_or_native_program_rerun'], True, 'complete composed maps')
        add('whole_height_census', [census, 'height'], bundle[census]['height']+1, 'complete census')
        add('support_census', [census, 'monomials'], bundle[census]['monomials']+1, 'complete census')
        add('row_height_census', [census, 'row_height'], 160, 'complete census')
        add('float_degree_census', [census, 'degree'], 4.0, 'complete census')
        add('endpoint_calibration', [endpoint, 'source_restored_before_calibration'], False, 'complete endpoint binding')
        add('endpoint_parent_binding', [endpoint, 'accepted_neighbor_verification_manifest', 'sha256'], '0'*64, 'complete endpoint binding')
        add('index_schema', ['INDEX.json', 'schema'], 'wrong', 'data index schema')
        add('index_search', ['INDEX.json', 'policy', 'search'], True, 'data index policy')
        add('index_combined_family', ['INDEX.json', 'policy', 'combined_crt_family_change'], True, 'data index policy')
        # Eighteen fixed-T additions, retaining all46 previous control contracts above.
        add('third_forward_sign', [cert, 'policy', 'forward_terms', 0, 2, 0], 2, 'shear direction')
        add('fourth_forward_sign', [cert, 'policy', 'forward_terms', 0, 3, 0], 1, 'shear direction')
        add('missing_forward_term', [cert, 'policy', 'forward_terms', 0], bundle[cert]['policy']['forward_terms'][0][1:], 'shear direction')
        add('wrong_forward_base_index', [cert, 'policy', 'forward_terms', 0, 2, 1, 0], 26, 'shear direction')
        add('wrong_inverse_target_index', [cert, 'policy', 'inverse_terms', 0, 4, 1, 0], 34, 'shear inverse')
        add('alternative_shear_family', [cert, 'policy', 'name'], 'alternative_unreviewed_shear', 'shear policy')
        add('restore_deleted_quartic', [poly, 'terms'], bundle[poly]['terms']+[[1, [10, 12, 25, 27]]], 'full SOS coefficient identity')
        add('omit_introduced_cubic', [poly, 'terms'], [t for t in bundle[poly]['terms'] if t[1] != [21, 25, 27]], 'full SOS coefficient identity')
        add('omit_introduced_quadratic', [poly, 'terms'], [t for t in bundle[poly]['terms'] if t[1] != [21, 27]], 'full SOS coefficient identity')
        add('outside_support_corruption', [poly, 'terms'], bundle[poly]['terms']+[[1, [0, 1]]], 'full SOS coefficient identity')
        add('output_occurrence_coverage', [cert, 'complete_occurrences', '36'], [20], 'shear occurrence coverage')
        add('parent_neighbor_map_sign', [maps, 'parent_neighbor_maps', 'shear', 'forward_terms', 1, 0, 0], 8, 'complete composed maps')
        add('parent_neighbor_certificate', [maps, 'parent_neighbor_shear_certificate', 'policy', 'forward_terms', 0, 0, 0], 8, 'complete composed maps')
        add('endpoint_optimality_claim', [endpoint, 'search_or_optimality_claimed'], True, 'complete endpoint binding')
        add('private_tuple_identity_claim', [maps, 'old_private_witness_identity_claimed'], True, 'complete composed maps')
        add('ordinary_proof_length_binding', [cert, 'ordinary_proposal', 'bytes'], bundle[cert]['ordinary_proposal']['bytes']+1, 'shear ordinary binding')
        add('pure_target_quartic_corruption', [poly, 'terms'], bundle[poly]['terms']+[[1, [35, 35, 35, 35]]], 'full SOS coefficient identity')
        add('omit_new_inverse_step', [maps, 'inverse_order'], bundle[maps]['inverse_order'][1:], 'complete composed maps')
        G.need(len(tests) == 64, 'complete negative control coverage')
        for name, mutate, reason in tests:
            actual = copy.deepcopy(bundle)
            mutate(actual)
            G.need(not G.equal(actual, bundle), 'negative mutation unchanged: '+name)
            rebind(actual)
            try:
                verify_bundle(actual, contexts, (profile,))
            except ValueError as error:
                G.need(str(error) == reason, 'control wrong rejection: '+name+': '+str(error))
            else:
                raise ValueError('control unexpectedly accepted: '+name)
            negatives.append({'profile': profile, 'name': name, 'expected_reason': reason})
        for kind in ('row_reorder', 'row_split_coefficient', 'row_cancel_pair',
                     'quartic_reorder', 'quartic_split_coefficient', 'quartic_cancel_pair'):
            actual = copy.deepcopy(bundle)
            if kind == 'row_reorder':
                actual[eq]['residuals'][19]['terms'].reverse()
            elif kind == 'row_split_coefficient':
                target = actual[eq]['residuals'][20]['terms']
                c, m = target[0]
                target[0] = [c+7, list(m)]
                target.append([-7, list(m)])
            elif kind == 'row_cancel_pair':
                actual[eq]['residuals'][19]['terms'].extend([[9, [10, 35]], [-9, [10, 35]]])
            elif kind == 'quartic_reorder':
                actual[poly]['terms'].reverse()
            elif kind == 'quartic_split_coefficient':
                c, m = actual[poly]['terms'][0]
                actual[poly]['terms'][0] = [c+7, list(m)]
                actual[poly]['terms'].append([-7, list(m)])
            else:
                actual[poly]['terms'].extend([[9, [0, 35, 35]], [-9, [0, 35, 35]]])
            rebind(actual)
            verify_bundle(actual, contexts, (profile,))
            valids.append({'profile': profile, 'name': kind})
    G.need(len(negatives) == 128 and len(valids) == 12, 'complete control counts')
    return {'negative_count': len(negatives), 'valid_count': len(valids),
            'negative_controls': negatives, 'valid_algebraic_controls': valids}


def canonical_terms(bundle, contexts):
    for profile in ('plain', 'weighted'):
        n = contexts[profile]['n']
        for row in bundle[profile+'/equation.json']['residuals']:
            G.need(G.equal(row['terms'], serialized(coefficients(row['terms'], n))), 'canonical saved row terms')
        poly = bundle[profile+'/expanded_polynomial.json']
        G.need(G.equal(poly['terms'], serialized(coefficients(poly['terms'], n))), 'canonical saved polynomial terms')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--data', required=True)
    parser.add_argument('--receipt', required=True)
    args = parser.parse_args()
    G.authenticate()
    G.need(sys.flags.optimize in (0, 1), 'optimize mode')
    data = G.external_data(args.data, absent=False)
    receipt = G.external_receipt(args.receipt, 'check-optimized' if sys.flags.optimize else 'check')
    bundle = G.read_bundle(data)
    contexts = {p: prepare(p) for p in ('plain', 'weighted')}
    results = verify_bundle(bundle, contexts)
    canonical_terms(bundle, contexts)
    evidence = controls(bundle, contexts)
    G.authenticate()
    G.report(receipt, {'schema': 'pell_output_gate_shear_check_result_v1', 'status': 'PASS',
                      'optimize': sys.flags.optimize, 'hold': G.record(HERE/'HOLD_INVENTORY.json'),
                      'artifacts': G.bundle_records(bundle), 'profiles': results, 'controls': evidence,
                      'producer_or_adopted_module_imported': False,
                      'source_or_native_program_rerun': False, 'search': False,
                      'combined_crt_family_change': False})


if __name__ == '__main__':
    main()
