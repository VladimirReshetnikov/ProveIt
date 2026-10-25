"""Independent three-way multinomial/symmetric SOS check. CODE ONLY/HOLD."""
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
def bootstrap_unique(pairs):
    result = {}
    for key,value in pairs:
        if key in result:
            raise ValueError('bootstrap duplicate JSON key')
        result[key] = value
    return result


hold = json.loads((HERE / 'HOLD_INVENTORY.json').read_text(),
                  object_pairs_hook=bootstrap_unique,
                  parse_constant=lambda _: (_ for _ in ()).throw(
                      ValueError('bootstrap nonfinite JSON number')))
if hold.get('schema') != 'held_second_pair_sum_gate_shear_r1_finite_v1' or set(hold['files']) != CORE:
    raise ValueError('bootstrap HOLD schema/closure')
for name, expected in hold['files'].items():
    path = HERE / name
    raw = path.read_bytes()
    if (type(expected) is not dict or set(expected) != {'bytes','sha256'} or
            type(expected['bytes']) is not int or type(expected['sha256']) is not str or
            path.is_symlink() or {'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()} != expected):
        raise ValueError('bootstrap held bytes: ' + name)
spec = importlib.util.spec_from_file_location('second_pair_sum_shear_r1_check_guard', HERE / 'guard.py')
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
    """Three-way multinomial; direction -1 is V, +1 its exact inverse."""
    G.need(type(direction) is int and direction in (-1, 1), 'substitution direction')
    result = {}
    for monomial, value in polynomial.items():
        power = monomial.count(25)
        rest = tuple(i for i in monomial if i != 25)
        for ib in range(power + 1):
            for ic in range(power - ib + 1):
                ip = power - ib - ic
                ways = comb(power, ib)*comb(power-ib, ic)
                key = tuple(sorted(rest+(11,)*ib+(12,)*ic+(25,)*ip))
                c = value*ways*direction**(ib+ic)
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


def ordinary_formulas():
    """All eleven full old/new residuals, including every lower term/output."""
    def row(output, argument, lpairs=(), constant=0):
        return plus(var(output), scale(square_pairs(linear(*argument)), -1),
                    linear(*lpairs), const(constant))
    D = ((1, 11), (1, 12))
    L = ((-2, 10), (-4, 11), (2, 12), (2, 21), (2, 25))
    Lnew = ((-2, 10), (-6, 11), (2, 21), (2, 25))
    old = {
        9: row(25, D, (), -2),
        10: row(26, ((1, 10), (2, 11), (2, 25)), ((7, 10), (12, 11), (12, 25)), -9),
        14: row(30, ((-2, 10), (2, 12), (2, 25), (2, 27)),
                ((-8, 10), (8, 12), (8, 25), (8, 27)), -6),
        16: row(32, ((1, 10), (6, 11), (8, 12), (2, 25)),
                ((-5, 10), (-36, 11), (-48, 12), (-12, 25)), -10),
        19: row(35, L, ((-19, 10), (-32, 11), (12, 12), (16, 21), (14, 25), (-1, 27)), -12),
        26: row(42, ((8, 11), (6, 12), (2, 25), (2, 41)),
                ((8, 11), (6, 12), (2, 25), (4, 41)), -4),
        30: row(46, ((2, 11), (-2, 12), (2, 25), (2, 27)),
                ((24, 11), (-24, 12), (24, 25), (24, 27)), -35),
        33: row(49, ((2, 11), (2, 25)), ((8, 11), (8, 25)), -1),
        34: row(50, ((4, 11), (1, 12), (4, 25), (2, 49)), (), -1),
        45: row(61, ((2, 11), (2, 25), (4, 59), (2, 60)),
                ((4, 11), (4, 25), (8, 59), (4, 60)), 1),
        46: row(62, ((5, 11), (4, 25), (2, 61)), ((1, 11),))}
    new = {
        9: row(25, D, ((-1, 11), (-1, 12)), -2),
        10: row(26, ((1, 10), (-2, 12), (2, 25)), ((7, 10), (-12, 12), (12, 25)), -9),
        14: row(30, ((-2, 10), (-2, 11), (2, 25), (2, 27)),
                ((-8, 10), (-8, 11), (8, 25), (8, 27)), -6),
        16: row(32, ((1, 10), (4, 11), (6, 12), (2, 25)),
                ((-5, 10), (-24, 11), (-36, 12), (-12, 25)), -10),
        19: row(35, Lnew, ((-19, 10), (-46, 11), (-2, 12), (16, 21), (14, 25), (-1, 27)), -12),
        26: row(42, ((6, 11), (4, 12), (2, 25), (2, 41)),
                ((6, 11), (4, 12), (2, 25), (4, 41)), -4),
        30: row(46, ((-4, 12), (2, 25), (2, 27)),
                ((-48, 12), (24, 25), (24, 27)), -35),
        33: row(49, ((-2, 12), (2, 25)), ((-8, 12), (8, 25)), -1),
        34: row(50, ((-3, 12), (4, 25), (2, 49)), (), -1),
        45: row(61, ((-2, 12), (2, 25), (4, 59), (2, 60)),
                ((-4, 12), (4, 25), (8, 59), (4, 60)), 1),
        46: row(62, ((1, 11), (-4, 12), (4, 25), (2, 61)), ((1, 11),))}
    return old, new


def expected_policy():
    return {'name': 'fixed_second_pair_sum_gate_shear_r1_1_1', 'targets': [25],
            'target_literal_names': ['mul.64'], 'fixed_inputs': [11, 12],
            'fixed_input_literal_names': ['crt.encoded.b', 'crt.encoded.c'],
            'forward_terms': [[[-1, [11]], [-1, [12]], [1, [25]]]],
            'inverse_terms': [[[1, [11]], [1, [12]], [1, [25]]]],
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


def ordinary_source_guards(rows, polynomial, profile):
    """Complete accepted-source premises used by the ordinary V proof."""
    G.need(sorted((i,m,c) for i,row in enumerate(rows)
                  for m,c in row.items() if abs(c) > 72) ==
           [(16,(11,12),-96),(26,(11,12),-96)], 'source residual72 cutoff')
    G.need({m:c for m,c in polynomial.items() if len(m) == 4 and abs(c) > 17472} ==
           {(11,11,12,12):32053,(11,12,12,12):23394,(11,11,11,12):20204},
           'source complete quartic cutoff')
    expected_cubic_p = coefficients([
        [-624,[10,10,25]],
        [-1056,[10,11,25]],
        [2192,[10,12,25]],
        [784,[10,21,25]],
        [552,[10,25,25]],
        [-8,[10,25,26]],
        [368,[10,25,27]],
        [16,[10,25,30]],
        [-8,[10,25,32]],
        [16,[10,25,35]],
        [-882,[11,11,25]],
        [8252,[11,12,25]],
        [1472,[11,21,25]],
        [192,[11,25,25]],
        [-16,[11,25,26]],
        [-1184,[11,25,27]],
        [-48,[11,25,32]],
        [32,[11,25,35]],
        [-512,[11,25,41]],
        [-64,[11,25,42]],
        [-16,[11,25,46]],
        [-16,[11,25,49]],
        [-64,[11,25,50]],
        [-384,[11,25,59]],
        [-192,[11,25,60]],
        [-48,[11,25,61]],
        [-80,[11,25,62]],
        [3102,[12,12,25]],
        [-672,[12,21,25]],
        [1072,[12,25,25]],
        [784,[12,25,27]],
        [-16,[12,25,30]],
        [-64,[12,25,32]],
        [-16,[12,25,35]],
        [-384,[12,25,41]],
        [-48,[12,25,42]],
        [16,[12,25,46]],
        [-16,[12,25,50]],
        [-368,[21,21,25]],
        [-352,[21,25,25]],
        [16,[21,25,27]],
        [-16,[21,25,35]],
        [-480,[25,25,25]],
        [-8,[25,25,26]],
        [-760,[25,25,27]],
        [-8,[25,25,30]],
        [-8,[25,25,32]],
        [-8,[25,25,35]],
        [-64,[25,25,41]],
        [-8,[25,25,42]],
        [-8,[25,25,46]],
        [-8,[25,25,49]],
        [-32,[25,25,50]],
        [-192,[25,25,59]],
        [-96,[25,25,60]],
        [-8,[25,25,61]],
        [-32,[25,25,62]],
        [-768,[25,27,27]],
        [-16,[25,27,30]],
        [-16,[25,27,46]],
        [-80,[25,41,41]],
        [-16,[25,41,42]],
        [-32,[25,49,50]],
        [-384,[25,59,59]],
        [-384,[25,59,60]],
        [-32,[25,59,61]],
        [-96,[25,60,60]],
        [-16,[25,60,61]],
        [-32,[25,61,62]],
    ], 316)
    expected_quadratic_p = coefficients([
        [-508,[10,25]],
        [2720,[11,25]],
        [1064,[12,25]],
        [640,[21,25]],
        [1849,[25,25]],
        [24,[25,26]],
        [1908,[25,27]],
        [16,[25,30]],
        [-24,[25,32]],
        [28,[25,35]],
        [80,[25,41]],
        [4,[25,42]],
        [48,[25,46]],
        [48,[25,49]],
        [32,[25,59]],
        [16,[25,60]],
        [8,[25,61]],
    ], 316)
    G.need(len(expected_cubic_p) == 69 and
           {m:c for m,c in polynomial.items() if len(m) == 3 and 25 in m} == expected_cubic_p,
           'source complete cubic69 slice')
    G.need(len(expected_quadratic_p) == 17 and
           {m:c for m,c in polynomial.items() if len(m) == 2 and 25 in m} == expected_quadratic_p,
           'source complete quadratic17 slice')
    G.need(all(abs(c) <= {0:2674,1:2270,2:6419,3:13184}[len(m)]
               for m,c in polynomial.items() if len(m) < 4) and
           polynomial.get(()) == 2674 and polynomial.get((25,)) == -2116,
           'source complete lower-degree bounds')
    first = {0:{(3,3):-1},1:{(0,2):-1},2:{(2,7):-1},
             3:{(8,9):-1},4:{(5,20):-1}}
    arguments = (
        ((1,10),(1,11)),
        ((2,10),(4,11),(2,21)),
        ((1,10),(2,22)),
        ((6,10),(2,23)),
        ((1,11),(1,12)),
        ((1,10),(2,11),(2,25)),
        ((1,10),(1,12)),
        ((6,10),(4,11),(6,12),(2,21),(2,27)),
        ((2,26),(2,28)),
        ((-2,10),(2,12),(2,25),(2,27)),
        ((-2,10),(4,11),(2,21),(4,27),(2,30)),
        ((1,10),(6,11),(8,12),(2,25)),
        ((4,10),(1,11),(6,12),(2,27)),
        ((2,32),(2,33)),
        ((-2,10),(-4,11),(2,12),(2,21),(2,25)),
        ((2,35),),
        ((2,10),(4,11),(2,21)),
        ((1,10),(2,37)),
        ((6,10),(2,38)),
        ((1,11),(2,39)),
        ((4,21),),
        ((8,11),(6,12),(2,25),(2,41)),
        ((6,10),(4,12),(2,27),(2,42)),
        ((1,12),(1,13)),
        ((1,10),(2,12),(2,44)),
        ((2,11),(-2,12),(2,25),(2,27)),
        ((4,27),(4,44),(2,45),(2,46)),
        ((-4,10),(1,12),(4,27),(2,30)),
        ((2,11),(2,25)),
        ((4,11),(1,12),(4,25),(2,49)),
        ((1,11),(2,12),(2,50)),
        ((2,51),),
        ((1,12),(4,51),(2,52)),
        ((1,11),(2,12),(2,53)),
        ((2,48),(2,54)),
        ((1,10),(4,48),(2,55)),
        ((2,56),),
        ((1,12),(4,56),(2,57)),
        ((1,10),(2,12),(2,58)),
        ((2,59),),
        ((2,11),(2,25),(4,59),(2,60)),
        ((5,11),(4,25),(2,61)),
        ((2,54),),
        ((4,54),(2,62),(2,63)),
        ((1,12),(4,62),(2,64)),
        ((2,10),(4,11),(-1,12),(-2,21)),
        ((2,10),(4,11),(-2,21),(-2,66)),
        ((4,10),(8,11),(-4,21),(-2,65),(-2,67)),
        ((2,68),))
    G.need(len(arguments) == 49, 'source early argument coverage')
    first.update({i+5:scale(square_pairs(linear(*arg)),-1)
                  for i,arg in enumerate(arguments)})
    G.need(all({m:c for m,c in rows[i].items() if len(m) == 2} == first[i]
               for i in range(54)), 'source all54 early quadratic parts')
    incidence = [i for i,row in enumerate(rows) if i >= 54 and
                 any(11 in m or 12 in m for m in row)]
    expected_incidence = ([63,68,71,73,90,91,176,192,210,211] if profile == 'plain'
                          else [63,68,71,74,91,92,177,193,212])
    G.need(incidence == expected_incidence, 'source complete tail b/c incidence')
    allowed = {10,11,12,21,25,27,41,49,59,60,61}
    diagonal = {(10,10):-1,(11,11):-1,(12,12):-1}
    restricted = {63:{(10,11):-1,(10,12):1,(11,12):1,(12,12):-1},
                  (91 if profile == 'plain' else 92):diagonal,
                  (176 if profile == 'plain' else 177):diagonal,
                  (192 if profile == 'plain' else 193):scale(diagonal,-1)}
    if profile == 'plain':
        restricted[210] = {(10,11):-1}
    G.need(all({m:c for m,c in rows[i].items() if len(m) == 2 and set(m) <= allowed} ==
               restricted.get(i,{}) for i in incidence), 'source whole restricted tail quadratic parts')
    return {'cubic_p_terms':69,'quadratic_p_terms':17,'early_quadratic_rows':54,
            'complete_tail_b_c_incidence':incidence,'restricted_coordinate_set':sorted(allowed),
            'all_quartic_cutoff_exceptions':3,'complete_lower_degree_and_row_cutoffs':True}


def ordinary_theorem(polynomial, rows, context):
    """Accepted ordinary V bounds; exact new height/support remain observations."""
    old = context['collected']
    words = ((11,11,11,11),(12,12,12,12),(11,11,12,12),
             (11,11,11,12),(11,12,12,12),(10,10,12,12))
    G.need([old.get(m,0) for m in words] == [12234,8365,32053,20204,23394,15445],
           'six whole old quartic witnesses')
    G.need([polynomial.get(m,0) for m in words] == [8506,5117,10837,6300,9106,15109],
           'six whole new quartic witnesses')
    contributions = {
        10:([16,0,0,0,0,0],[0,16,0,0,0,24]),
        14:([0,16,0,0,0,96],[16,0,0,0,0,0]),
        16:([1296,4096,13824,6912,12288,384],[256,1296,3456,1536,3456,216]),
        19:([256,16,384,-512,-128,96],[1296,0,0,0,0,0]),
        26:([4096,1296,13824,12288,6912,0],[1296,256,3456,3456,1536,0]),
        30:([16,16,96,-64,-64,0],[0,256,0,0,0,0]),
        33:([16,0,0,0,0,0],[0,16,0,0,0,0]),
        34:([256,1,96,256,16,0],[0,81,0,0,0,0]),
        45:([16,0,0,0,0,0],[0,16,0,0,0,0]),
        46:([625,0,0,0,0,0],[1,256,96,-16,-256,0])}
    for i,(before,after) in contributions.items():
        oldsquare,newsquare = square_pairs(context['rows'][i]),square_pairs(rows[i])
        G.need([oldsquare.get(m,0) for m in words] == before and
               [newsquare.get(m,0) for m in words] == after, 'all60 old/new row witness cells')
    order = [9,10,14,16,19,26,30,33,34,45,46]
    G.need([len(context['rows'][i]) for i in order] == [5,11,16,16,23,16,16,7,12,16,8] and
           [len(rows[i]) for i in order] == [7,11,16,16,18,16,11,7,8,16,12] and
           sum(map(len,context['rows']))-sum(map(len,rows)) == 8,
           'whole residual support8 theorem')
    G.need(max(abs(c) for row in rows for c in row.values()) == 72 and
           rows[12].get((10,12)) == -72, 'exact residual height72 theorem')
    G.need(all((-23426 <= c <= 24000) if len(m) == 4 else
               abs(c) <= {0:2674,1:4386,2:15557,3:20762}[len(m)]
               for m,c in polynomial.items()), 'whole ordinary degree bounds')
    G.need(polynomial.get(()) == old.get(()) == 2674 and old.get((25,)) == -2116 and
           all(polynomial.get((i,),0) == old.get((i,),0)+2116 for i in (11,12)) and
           {m:c for m,c in old.items() if len(m) == 1 and m not in ((11,),(12,))} ==
           {m:c for m,c in polynomial.items() if len(m) == 1 and m not in ((11,),(12,))},
           'whole constant/linear theorem')
    allowed = {10,11,12,21,25,27,41,49,59,60,61}
    changed = sorted(m for m in set(old)|set(polynomial) if old.get(m,0) != polynomial.get(m,0))
    G.need(all((11 in m or 12 in m) and set(m) <= allowed
               for m in changed if len(m) == 4), 'whole quartic change support guard')
    deleted,introduced = set(old)-set(polynomial),set(polynomial)-set(old)
    G.need(len(deleted)+len(introduced) <= 2196 and
           abs(len(old)-len(polynomial)) <= 2196, 'ordinary whole support bound')
    return {'ordinary_full_old_new_residuals':11,'quartic_whole_witnesses':6,
            'quartic_row_witness_cells_each_side':60,'exact_residual_height':72,
            'residual_monomial_occurrences_removed':8,
            'ordinary_whole_height_lower_bound':15109,'ordinary_whole_height_upper_bound':24000,
            'ordinary_degree_bounds':{'4_lower':-23426,'4_upper':24000,'3_abs':20762,
                                      '2_abs':15557,'1_abs':4386,'0_exact':2674},
            'ordinary_source_guards':context['source_guards'],
            'support_symmetric_difference_upper_bound':2196,
            'observed_removed_monomials':[list(m) for m in sorted(deleted)],
            'observed_introduced_monomials':[list(m) for m in sorted(introduced)],
            'observed_removed_by_degree':{str(d):sum(len(m)==d for m in deleted) for d in range(5)},
            'observed_introduced_by_degree':{str(d):sum(len(m)==d for m in introduced) for d in range(5)},
            'observed_net_terms_removed':len(old)-len(polynomial),
            'observed_complete_coefficient_changes':[[old.get(m,0),polynomial.get(m,0),list(m)] for m in changed],
            'exact_expanded_height_or_support_preasserted':False,'search_or_optimality_claimed':False}


def prepare(profile):
    old = G.source(profile,'equation.json')
    n = len(old['variables'])
    G.need(n == (316 if profile == 'plain' else 315) and
           len(old['residuals']) == (218 if profile == 'plain' else 217), 'parent dimension/rows')
    names = [v['name'] for v in old['variables']]
    G.need(len(names) == len(set(names)) and
           [names[i] for i in (10,11,12,21,25,27,30,35,41,49,59,60,61)] ==
           ['crt.encoded.a','crt.encoded.b','crt.encoded.c','mul.40','mul.64','mul.75',
            'mul.96','mul.137','add.172','mul.210','add.262','mul.266','mul.270'], 'parent literal names')
    rows = [coefficients(r['terms'],n) for r in old['residuals']]
    oldpoly = G.source(profile,'expanded_polynomial.json')
    collected = coefficients(oldpoly['terms'],n)
    source_guards = ordinary_source_guards(rows,collected,profile)
    G.need(sos(rows) == collected, 'parent whole SOS')
    metrics = independently_count(old,rows,collected)
    G.need(G.equal(metrics,G.source(profile,'METRICS.json')), 'parent complete census')
    G.need(metrics['height'] == 32053 and metrics['row_height'] == 96 and
           metrics['monomials'] == (5626 if profile == 'plain' else 5632), 'accepted parent endpoint')
    occurrences = {str(j):[i for i,row in enumerate(rows) if any(j in m for m in row)] for j in (25,27,35)}
    G.need(occurrences == {'25':[9,10,14,16,19,26,30,33,34,45,46],
                          '27':[11,12,14,15,17,19,20,27,30,31,32],'35':[19,20]},
           'whole occurrence closure')
    old_formulas,formulas = ordinary_formulas()
    for i,expected in old_formulas.items():
        G.need(rows[i] == expected, 'ordinary full old residual formula')
    transformed = [substitute(row,-1) for row in rows]
    changed = [i for i,(a,b) in enumerate(zip(rows,transformed)) if a != b]
    G.need(changed == sorted(formulas) == [9,10,14,16,19,26,30,33,34,45,46],
           'complete11 changed-row coverage')
    for i,row in enumerate(transformed):
        G.need(row == (formulas[i] if i in formulas else rows[i]), 'ordinary/unchanged full row')
        G.need(substitute(row,1) == rows[i], 'inverse whole residual identity')
    whole = sos(transformed)
    G.need(whole == substitute(collected,-1), 'forward whole quartic identity')
    G.need(substitute(whole,1) == collected, 'inverse whole quartic identity')
    parent = G.source(profile,'COMPOSED_MAPS.json')
    centered = parent['parent_pell_maps']['parent_neighbor_maps']['parent_balanced_maps']['parent_centered_maps']
    G.need(len(centered['translation']['shifts']) == 58 and
           len(centered['parent_maps']['actual_free_factored_coordinates']) == 83 and
           len(centered['parent_maps']['reverse_monic_restorations']) == (204 if profile == 'plain' else 203),
           'parent whole witness-map counts')
    context = {'profile':profile,'old':old,'rows':rows,'n':n,'oldpoly':oldpoly,
               'collected':collected,'transformed':transformed,'whole':whole,
               'formulas':formulas,'changed':changed,'occurrences':occurrences,'parent':parent,
               'source_guards':source_guards}
    ordinary_theorem(whole,transformed,context)
    return context


def check_index(bundle):
    index = bundle['INDEX.json']
    G.need(index.get('schema') == 'second_pair_sum_gate_shear_r1_data_inventory_v1', 'data index schema')
    G.need(G.equal(index.get('policy'),expected_policy()), 'data index policy')
    expected = {'schema':'second_pair_sum_gate_shear_r1_data_inventory_v1','policy':expected_policy(),
                'files':G.bundle_records({k:v for k,v in bundle.items() if k != 'INDEX.json'}),
                'source_pins':G.record(HERE/'SOURCE_PINS.json'),
                'producer':G.record(HERE/'build.py'),'checker':G.record(HERE/'check.py'),
                'guard':G.record(HERE/'guard.py')}
    G.need(G.equal(index,expected), 'whole data index binding')


def verify_profile(bundle,profile,context):
    pre = profile+'/'
    old,n = context['old'],context['n']
    equation,cert = bundle[pre+'equation.json'],bundle[pre+'shear_certificate.json']
    G.need(cert.get('schema') == 'second_pair_sum_gate_shear_r1_v1', 'shear schema')
    G.need(cert.get('convention') == 'U_w = second_pair_sum_shear_r1(new_z)', 'shear convention')
    inverse = 'new_z25 = U_w25+U_w11+U_w12'
    G.need(cert.get('inverse_convention') == inverse, 'shear inverse convention')
    policy = cert.get('policy',{})
    G.need(G.equal(policy.get('forward_terms'),expected_policy()['forward_terms']), 'shear direction')
    G.need(G.equal(policy.get('inverse_terms'),expected_policy()['inverse_terms']), 'shear inverse')
    G.need(G.equal(policy,expected_policy()), 'shear policy')
    G.need(G.equal(cert.get('input'),G.source_record(profile,'equation.json')), 'shear input binding')
    G.need(G.equal(cert.get('changed_rows'),context['changed']), 'shear changed coverage')
    G.need(G.equal(cert.get('complete_occurrences'),context['occurrences']), 'shear occurrence coverage')
    pins = G.obj(HERE/'SOURCE_PINS.json')
    G.need(G.equal(cert.get('ordinary_proposal'),pins['ordinary_shear_manifest']), 'shear ordinary binding')
    chart = G.record_bytes(G.encode(equation))
    expected_cert = {'schema':'second_pair_sum_gate_shear_r1_v1','profile':profile,
                     'input':G.source_record(profile,'equation.json'),'output':chart,
                     'convention':'U_w = second_pair_sum_shear_r1(new_z)','inverse_convention':inverse,
                     'policy':expected_policy(),'changed_rows':context['changed'],
                     'complete_occurrences':context['occurrences'],
                     'ordinary_proposal':pins['ordinary_shear_manifest']}
    G.need(G.equal(cert,expected_cert), 'whole shear certificate')
    oldmeta = {k:v for k,v in old.items() if k != 'residuals'}
    oldmeta['variant'] += ':second_pair_sum_gate_shear_r1_1_1'
    G.need(G.equal({k:v for k,v in equation.items() if k != 'residuals'},oldmeta), 'equation metadata')
    rawrows = equation.get('residuals')
    G.need(type(rawrows) is list and len(rawrows) == len(context['rows']), 'complete row count')
    rows = []
    for i,(actual,source) in enumerate(zip(rawrows,old['residuals'])):
        G.need(G.equal({k:v for k,v in actual.items() if k != 'terms'},
                       {k:v for k,v in source.items() if k != 'terms'}), 'row metadata')
        row = coefficients(actual['terms'],n)
        G.need(row == context['transformed'][i], 'forward row identity')
        G.need(row == (context['formulas'][i] if i in context['formulas'] else context['rows'][i]),
               'actual ordinary/unchanged residual formula')
        G.need(substitute(row,1) == context['rows'][i], 'inverse actual residual identity')
        rows.append(row)
    expanded = bundle[pre+'expanded_polynomial.json']
    G.need(G.equal({k:v for k,v in expanded.items() if k != 'terms'},
                   {k:v for k,v in context['oldpoly'].items() if k != 'terms'}), 'expanded metadata')
    polynomial = coefficients(expanded['terms'],n)
    G.need(polynomial == sos(rows) == context['whole'], 'full SOS coefficient identity')
    G.need(substitute(polynomial,1) == context['collected'], 'inverse whole quartic identity')
    theorem = ordinary_theorem(polynomial,rows,context)
    metrics = independently_count(equation,rows,polynomial)
    G.need(metrics['degree'] == 4 and metrics['row_degree'] == 2 and
           metrics['used_coordinates'] == list(range(n)), 'quartic degree/liveness')
    G.need(G.equal(bundle[pre+'METRICS.json'],metrics), 'complete census')
    G.need(15109 <= metrics['height'] <= 24000 and metrics['row_height'] == 72,
           'ordinary bounded height deduction')
    parent = context['parent']
    endpoint = G.source(profile,'ENDPOINT_BINDING.json')
    expected_maps = {
        'schema':'second_pair_sum_gate_shear_r1_composed_maps_v1','profile':profile,
        'chart':chart,'shear':expected_policy(),'parent_pair_sum_maps':parent,
        'parent_pair_sum_endpoint':endpoint,
        'parent_pair_sum_shear_certificate':G.source(profile,'shear_certificate.json'),
        'forward_order':parent['forward_order']+['apply_inverse_second_pair_sum_shear_r1_to_U_tuple'],
        'inverse_order':['apply_second_pair_sum_shear_r1_to_recover_U_tuple']+parent['inverse_order'],
        'new_chart_is_whole_integer_bijection':True,
        'old_private_witness_identity_claimed':False,'source_or_native_program_rerun':False}
    G.need(G.equal(bundle[pre+'COMPOSED_MAPS.json'],expected_maps), 'complete composed maps')
    expected_endpoint = {
        'schema':'second_pair_sum_gate_shear_r1_endpoint_v1','profile':profile,
        'all_prior_profile_files':{f:G.record_bytes(G.encode(bundle[pre+f]))
                                  for f in G.PROFILE_FILES if f != 'ENDPOINT_BINDING.json'},
        'ordinary_shear_manifest':pins['ordinary_shear_manifest'],
        'accepted_pair_sum_verification_manifest':pins['accepted_pair_sum_verification_manifest'],
        'parent_pair_sum_data_index':G.record(G.SOURCE/'INDEX.json'),
        'source_calibration':endpoint['source_calibration'],
        'equivalence_chain':['fixed_pair_sum_unimodular_shear']+endpoint['equivalence_chain'],
        'source_restored_before_calibration':True,'search_or_optimality_claimed':False}
    G.need(G.equal(bundle[pre+'ENDPOINT_BINDING.json'],expected_endpoint), 'complete endpoint binding')
    return {'metrics':metrics,'changed_rows':context['changed'],'unchanged_rows':len(rows)-11,
            'complete_occurrences':context['occurrences'],'whole_forward_and_actual_saved_inverse':True,
            'whole_old_and_new_SOS':True,'ordinary_bounds_and_observed_census':theorem}


def verify_bundle(bundle,contexts,profiles=('plain','weighted')):
    G.need(set(bundle) == G.ARTIFACTS, 'data object inventory')
    check_index(bundle)
    return {p:verify_profile(bundle,p,contexts[p]) for p in profiles}


def rebind(bundle):
    """Rebind outer byte records only; never repair algebra/source/policy fields."""
    for profile in ('plain','weighted'):
        pre = profile+'/'
        chart = G.record_bytes(G.encode(bundle[pre+'equation.json']))
        bundle[pre+'shear_certificate.json']['output'] = chart
        bundle[pre+'COMPOSED_MAPS.json']['chart'] = chart
        bundle[pre+'ENDPOINT_BINDING.json']['all_prior_profile_files'] = {
            f:G.record_bytes(G.encode(bundle[pre+f])) for f in G.PROFILE_FILES if f != 'ENDPOINT_BINDING.json'}
    bundle['INDEX.json']['files'] = G.bundle_records({k:v for k,v in bundle.items() if k != 'INDEX.json'})


def put(root,path,value):
    for part in path[:-1]:
        root = root[part]
    root[path[-1]] = value


def controls(bundle,contexts):
    negatives,valids = [],[]
    for profile in ('plain','weighted'):
        pre = profile+'/'
        eq,poly,cert,maps,census,endpoint = (pre+f for f in
            ('equation.json','expanded_polynomial.json','shear_certificate.json',
             'COMPOSED_MAPS.json','METRICS.json','ENDPOINT_BINDING.json'))
        tests = []

        def add(name,path,value,reason):
            tests.append((name,lambda b,p=path,v=value:put(b,p,copy.deepcopy(v)),reason))

        add('wrong_direction_first_row',[eq,'residuals',9,'terms'],contexts[profile]['old']['residuals'][9]['terms'],'forward row identity')
        add('wrong_direction_second_row',[eq,'residuals',10,'terms'],contexts[profile]['old']['residuals'][10]['terms'],'forward row identity')
        changed = copy.deepcopy(bundle[eq]['residuals'][16]['terms'])
        for term in changed:
            if term[1] == [11,12]:
                term[0] *= -1
        add('mixed_sign_actual_row',[eq,'residuals',16,'terms'],changed,'forward row identity')
        changed = copy.deepcopy(bundle[eq]['residuals'][9]['terms'])
        for term in changed:
            term[1] = [24 if i == 25 else i for i in term[1]]
        add('wrong_gate_actual_row',[eq,'residuals',9,'terms'],changed,'forward row identity')
        add('missing_whole_row',[eq,'residuals'],bundle[eq]['residuals'][:9]+bundle[eq]['residuals'][10:],'complete row count')
        add('missing_actual_term',[eq,'residuals',10,'terms'],bundle[eq]['residuals'][10]['terms'][1:],'forward row identity')
        add('unchanged_row_corruption',[eq,'residuals',0,'terms',0,0],bundle[eq]['residuals'][0]['terms'][0][0]+1,'forward row identity')
        add('preceding_row_corruption',[eq,'residuals',8,'terms',0,0],bundle[eq]['residuals'][8]['terms'][0][0]+1,'forward row identity')
        add('row_label',[eq,'residuals',9,'label'],'wrong','row metadata')
        add('integer_domain',[eq,'domain'],'positive integers','equation metadata')
        add('literal_name',[eq,'variables',25,'name'],'mul.65','equation metadata')
        add('boolean_coefficient',[eq,'residuals',9,'terms',0,0],True,'integer coefficient')
        add('float_coefficient',[eq,'residuals',9,'terms',0,0],-2.0,'integer coefficient')
        add('boolean_index',[eq,'residuals',9,'terms'],bundle[eq]['residuals'][9]['terms']+[[1,[True]]],'integer index')
        add('out_of_range_index',[eq,'residuals',9,'terms'],bundle[eq]['residuals'][9]['terms']+[[1,[contexts[profile]['n']]]],'integer index')
        add('quartic_coefficient',[poly,'terms',0,0],bundle[poly]['terms'][0][0]+1,'full SOS coefficient identity')
        add('dropped_quartic_term',[poly,'terms'],bundle[poly]['terms'][1:],'full SOS coefficient identity')
        add('boolean_quartic_coefficient',[poly,'terms',0,0],True,'integer coefficient')
        add('quartic_header',[poly,'domain'],'positive integers','expanded metadata')
        add('certificate_schema',[cert,'schema'],'wrong','shear schema')
        add('direction_convention',[cert,'convention'],'new_z = second_pair_sum_shear_r1(U_w)','shear convention')
        add('inverse_convention',[cert,'inverse_convention'],'new_z = second_pair_sum_shear_r1(U_w)','shear inverse convention')
        add('first_forward_sign',[cert,'policy','forward_terms',0,0,0],1,'shear direction')
        add('second_forward_sign',[cert,'policy','forward_terms',0,1,0],1,'shear direction')
        add('inverse_map_sign',[cert,'policy','inverse_terms',0,0,0],-1,'shear inverse')
        add('wrong_gate_schema',[cert,'policy','targets',0],24,'shear policy')
        add('boolean_gate_schema',[cert,'policy','targets',0],True,'shear policy')
        add('stale_input_binding',[cert,'input','sha256'],'0'*64,'shear input binding')
        add('changed_row_coverage',[cert,'changed_rows'],contexts[profile]['changed'][1:],'shear changed coverage')
        add('occurrence_coverage',[cert,'complete_occurrences','25'],[9,10],'shear occurrence coverage')
        add('ordinary_proof_binding',[cert,'ordinary_proposal','sha256'],'0'*64,'shear ordinary binding')
        add('inverse_map_order',[maps,'inverse_order'],list(reversed(bundle[maps]['inverse_order'])),'complete composed maps')
        nested = ['parent_pair_sum_maps','parent_pell_maps','parent_neighbor_maps','parent_balanced_maps','parent_centered_maps','parent_maps']
        old_private = bundle[maps]['parent_pair_sum_maps']['parent_pell_maps']['parent_neighbor_maps']['parent_balanced_maps']['parent_centered_maps']['parent_maps']
        add('free_coordinate_omission',[maps]+nested+['actual_free_factored_coordinates'],old_private['actual_free_factored_coordinates'][1:],'complete composed maps')
        monic = copy.deepcopy(old_private['reverse_monic_restorations'])
        monic[0]['restoration'][0][0] += 1
        add('monic_restoration',[maps]+nested+['reverse_monic_restorations'],monic,'complete composed maps')
        add('parent_balanced_map_sign',[maps,'parent_pair_sum_maps','parent_pell_maps','parent_neighbor_maps','parent_balanced_maps','shear','forward_terms',0,0],2,'complete composed maps')
        add('source_calibration',[maps,'parent_pair_sum_maps','parent_pell_maps','parent_neighbor_maps','parent_balanced_maps','parent_centered_maps','source_binding','interval_triples_fresh_across_reparameterization'],False,'complete composed maps')
        add('native_rerun_claim',[maps,'source_or_native_program_rerun'],True,'complete composed maps')
        add('whole_height_census',[census,'height'],bundle[census]['height']+1,'complete census')
        add('support_census',[census,'monomials'],bundle[census]['monomials']+1,'complete census')
        add('row_height_census',[census,'row_height'],96,'complete census')
        add('float_degree_census',[census,'degree'],4.0,'complete census')
        add('endpoint_calibration',[endpoint,'source_restored_before_calibration'],False,'complete endpoint binding')
        add('endpoint_parent_binding',[endpoint,'accepted_pair_sum_verification_manifest','sha256'],'0'*64,'complete endpoint binding')
        add('index_schema',['INDEX.json','schema'],'wrong','data index schema')
        add('index_search',['INDEX.json','policy','search'],True,'data index policy')
        add('index_combined_family',['INDEX.json','policy','combined_crt_family_change'],True,'data index policy')
        add('missing_forward_term',[cert,'policy','forward_terms',0],bundle[cert]['policy']['forward_terms'][0][1:],'shear direction')
        add('wrong_forward_target_index',[cert,'policy','forward_terms',0,2,1,0],24,'shear direction')
        add('wrong_forward_base_index',[cert,'policy','forward_terms',0,0,1,0],10,'shear direction')
        add('wrong_inverse_target_index',[cert,'policy','inverse_terms',0,2,1,0],24,'shear inverse')
        add('alternative_shear_family',[cert,'policy','name'],'unreviewed_alternative','shear policy')
        add('pure_b_quartic_witness',[poly,'terms'],bundle[poly]['terms']+[[1,[11,11,11,11]]],'full SOS coefficient identity')
        add('pure_c_quartic_witness',[poly,'terms'],bundle[poly]['terms']+[[1,[12,12,12,12]]],'full SOS coefficient identity')
        add('old_height_monomial_witness',[poly,'terms'],bundle[poly]['terms']+[[1,[11,11,12,12]]],'full SOS coefficient identity')
        add('outside_support_corruption',[poly,'terms'],bundle[poly]['terms']+[[1,[0,1]]],'full SOS coefficient identity')
        add('fixed_output_occurrence_coverage',[cert,'complete_occurrences','35'],[20],'shear occurrence coverage')
        add('parent_U_map_sign',[maps,'parent_pair_sum_maps','shear','forward_terms',0,0,0],1,'complete composed maps')
        add('parent_U_certificate',[maps,'parent_pair_sum_shear_certificate','policy','forward_terms',0,0,0],1,'complete composed maps')
        add('endpoint_optimality_claim',[endpoint,'search_or_optimality_claimed'],True,'complete endpoint binding')
        add('private_tuple_identity_claim',[maps,'old_private_witness_identity_claimed'],True,'complete composed maps')
        add('ordinary_proof_length_binding',[cert,'ordinary_proposal','bytes'],bundle[cert]['ordinary_proposal']['bytes']+1,'shear ordinary binding')
        add('pure_target_quartic_corruption',[poly,'terms'],bundle[poly]['terms']+[[1,[25,25,25,25]]],'full SOS coefficient identity')
        add('omit_new_inverse_step',[maps,'inverse_order'],bundle[maps]['inverse_order'][1:],'complete composed maps')
        swapped = list(bundle[maps]['forward_order'])
        swapped[-3],swapped[-1] = swapped[-1],swapped[-3]
        add('noncommuting_T_V_order',[maps,'forward_order'],swapped,'complete composed maps')
        wrong_linear = copy.deepcopy(bundle[eq]['residuals'][30]['terms'])
        linear_c = [term for term in wrong_linear if term[1] == [12]]
        G.need(len(linear_c) == 1 and linear_c[0][0] == -48, 'R1 regression target coverage')
        linear_c[0][0] = -24
        add('restore_erroneous_row30_linear_minus24',[eq,'residuals',30,'terms'],wrong_linear,'forward row identity')
        for i in (14,19,26,30,33,34,45,46):
            add('restore_old_complete_row_'+str(i),[eq,'residuals',i,'terms'],
                contexts[profile]['old']['residuals'][i]['terms'],'forward row identity')
        G.need(len(tests) == len({name for name,_,_ in tests}) == 73,
               'complete artifact negative control coverage')
        for name,mutate,reason in tests:
            actual = copy.deepcopy(bundle)
            mutate(actual)
            G.need(not G.equal(actual,bundle), 'negative mutation unchanged: '+name)
            rebind(actual)
            try:
                verify_bundle(actual,contexts,(profile,))
            except ValueError as error:
                G.need(str(error) == reason, 'control wrong rejection: '+name+': '+str(error))
            else:
                raise ValueError('control unexpectedly accepted: '+name)
            negatives.append({'profile':profile,'name':name,'expected_reason':reason,
                              'model':'actual_saved_successor_artifacts_outer_records_only_rebound'})
        for kind in ('row_reorder','row_split_coefficient','row_cancel_pair',
                     'quartic_reorder','quartic_split_coefficient','quartic_cancel_pair'):
            actual = copy.deepcopy(bundle)
            if kind == 'row_reorder':
                actual[eq]['residuals'][9]['terms'].reverse()
            elif kind == 'row_split_coefficient':
                target = actual[eq]['residuals'][10]['terms']
                c,m = target[0]
                target[0] = [c+7,list(m)]
                target.append([-7,list(m)])
            elif kind == 'row_cancel_pair':
                actual[eq]['residuals'][9]['terms'].extend([[9,[11,25]],[-9,[11,25]]])
            elif kind == 'quartic_reorder':
                actual[poly]['terms'].reverse()
            elif kind == 'quartic_split_coefficient':
                c,m = actual[poly]['terms'][0]
                actual[poly]['terms'][0] = [c+7,list(m)]
                actual[poly]['terms'].append([-7,list(m)])
            else:
                actual[poly]['terms'].extend([[9,[0,25,25]],[-9,[0,25,25]]])
            G.need(not G.equal(actual,bundle), 'valid mutation unchanged: '+kind)
            rebind(actual)
            verify_bundle(actual,contexts,(profile,))
            valids.append({'profile':profile,'name':kind})
    source_negatives = source_guard_controls(contexts)
    negatives.extend(source_negatives)
    G.need(len(negatives) == 172 and len(valids) == 12, 'complete control counts')
    return {'negative_count':len(negatives),'valid_count':len(valids),
            'saved_artifact_negative_count':146,'source_premise_negative_count':26,
            'negative_controls':negatives,'valid_algebraic_controls':valids}


def source_guard_controls(contexts):
    """Supplemental raw accepted-source premise tests, not successor verification."""
    results = []
    for profile,context in contexts.items():
        original = {'equation':context['old'],'quartic':context['oldpoly']}
        tests = []

        def term_change(model,field,monomial,delta,row=None):
            raw = (model['equation']['residuals'][row]['terms'] if row is not None
                   else model[field]['terms'])
            found = [term for term in raw if term[1] == list(monomial)]
            G.need(len(found) == 1, 'source control target coverage')
            found[0][0] += delta

        def omit(model,field,monomial,row=None):
            raw = (model['equation']['residuals'][row]['terms'] if row is not None
                   else model[field]['terms'])
            found = [term for term in raw if term[1] == list(monomial)]
            G.need(len(found) == 1, 'source control target coverage')
            raw.remove(found[0])

        tests.append(('source_row72_cutoff',lambda m:term_change(m,'equation',(11,12),1,16),'source residual72 cutoff'))
        tests.append(('source_quartic_cutoff',lambda m:term_change(m,'quartic',(11,11,12,12),1),'source complete quartic cutoff'))
        tests.append(('source_cubic69_coefficient',lambda m:term_change(m,'quartic',(10,10,25),1),'source complete cubic69 slice'))
        tests.append(('source_cubic69_omission',lambda m:omit(m,'quartic',(10,10,25)),'source complete cubic69 slice'))
        tests.append(('source_cubic69_extra',lambda m:m['quartic']['terms'].append([1,[0,25,25]]),'source complete cubic69 slice'))
        tests.append(('source_quadratic17_coefficient',lambda m:term_change(m,'quartic',(10,25),1),'source complete quadratic17 slice'))
        tests.append(('source_quadratic17_omission',lambda m:omit(m,'quartic',(10,25)),'source complete quadratic17 slice'))
        tests.append(('source_lower_degree_bound',lambda m:term_change(m,'quartic',(),1),'source complete lower-degree bounds'))
        tests.append(('source_early_quadratic_part',lambda m:m['equation']['residuals'][5]['terms'].append([1,[0,0]]),'source all54 early quadratic parts'))
        tests.append(('source_tail_incidence_extra',lambda m:m['equation']['residuals'][54]['terms'].append([1,[11]]),'source complete tail b/c incidence'))
        tests.append(('source_tail_incidence_missing',lambda m:omit(m,'equation',(3,11),68),'source complete tail b/c incidence'))
        tests.append(('source_tail_restriction',lambda m:term_change(m,'equation',(10,11),1,63),'source whole restricted tail quadratic parts'))

        def private_to_inside(model):
            raw = model['equation']['residuals'][68]['terms']
            found = [term for term in raw if term[1] == [3,11]]
            G.need(len(found) == 1, 'source control target coverage')
            found[0][1] = [11,21]

        tests.append(('source_tail_outside_to_inside',private_to_inside,'source whole restricted tail quadratic parts'))
        G.need(len(tests) == len({name for name,_,_ in tests}) == 13,
               'complete source-premise negative control coverage')
        for name,mutate,reason in tests:
            actual = copy.deepcopy(original)
            mutate(actual)
            G.need(not G.equal(actual,original), 'source negative mutation unchanged: '+name)
            rows = [coefficients(row['terms'],context['n']) for row in actual['equation']['residuals']]
            polynomial = coefficients(actual['quartic']['terms'],context['n'])
            try:
                ordinary_source_guards(rows,polynomial,profile)
            except ValueError as error:
                G.need(str(error) == reason, 'source control wrong rejection: '+name+': '+str(error))
            else:
                raise ValueError('source control unexpectedly accepted: '+name)
            results.append({'profile':profile,'name':name,'expected_reason':reason,
                            'model':'private_actual_raw_source_equation_and_quartic_premise_only'})
    return results


def canonical_terms(bundle,contexts):
    for profile in ('plain','weighted'):
        n = contexts[profile]['n']
        for row in bundle[profile+'/equation.json']['residuals']:
            G.need(G.equal(row['terms'],serialized(coefficients(row['terms'],n))), 'canonical saved row terms')
        poly = bundle[profile+'/expanded_polynomial.json']
        G.need(G.equal(poly['terms'],serialized(coefficients(poly['terms'],n))), 'canonical saved polynomial terms')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--data',required=True)
    parser.add_argument('--receipt',required=True)
    args = parser.parse_args()
    G.authenticate()
    G.need(sys.flags.optimize in (0,1), 'optimize mode')
    data = G.external_data(args.data,absent=False)
    receipt = G.external_receipt(args.receipt,'check-optimized' if sys.flags.optimize else 'check')
    bundle = G.read_bundle(data)
    contexts = {p:prepare(p) for p in ('plain','weighted')}
    results = verify_bundle(bundle,contexts)
    canonical_terms(bundle,contexts)
    evidence = controls(bundle,contexts)
    G.need(G.equal(G.read_bundle(data),bundle), 'saved data changed during verification')
    G.authenticate()
    G.report(receipt,{'schema':'second_pair_sum_gate_shear_r1_check_result_v1','status':'PASS',
                      'optimize':sys.flags.optimize,'hold':G.record(HERE/'HOLD_INVENTORY.json'),
                      'artifacts':G.bundle_records(bundle),'profiles':results,'controls':evidence,
                      'producer_or_adopted_module_imported':False,
                      'source_or_native_program_rerun':False,'search':False,
                      'combined_crt_family_change':False})


if __name__ == '__main__':
    main()
