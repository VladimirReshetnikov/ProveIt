#!/usr/bin/env python3
"""Read-only exact certificates for Report294 (Python 3.10+, standard library)."""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
from types import MappingProxyType

MAX_BITS = 512
MAX_TERMS = 12000
MAX_PAIRS = 2000000


def require(condition, message):
    if type(condition) is not bool or type(message) is not str:
        raise ValueError('require needs bool and str')
    if not condition:
        raise RuntimeError(message)


def integer(value, name='integer'):
    if type(value) is not int or value.bit_length() > MAX_BITS:
        raise ValueError(name + ' must be a bounded integer, not bool')
    return value


def rational(value):
    if type(value) not in (int, Fraction):
        raise ValueError('an exact integer or Fraction is required')
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_BITS:
        raise ValueError('rational exceeds 512-bit numerator/denominator bound')
    return Fraction(value)


class Polynomial:
    """Bounded sparse Q-polynomials. Adapted from the Report293 exact companion.

    Every monomial coefficient is compared; no interpolation or sampling.
    The public coefficient mapping is immutable. All interfaces reject floats.
    """
    __slots__ = ('_terms',)

    def __init__(self, terms=None):
        if terms is None:
            terms = {}
        if type(terms) is not dict or len(terms) > MAX_TERMS:
            raise ValueError('polynomial needs a dictionary of at most 12000 terms')
        clean = {}
        for monomial, coefficient in terms.items():
            if (type(monomial) is not tuple or len(monomial) > 16
                    or any(type(v) is not str or not v.isidentifier() or len(v) > 20 for v in monomial)
                    or tuple(sorted(monomial)) != monomial):
                raise ValueError('sorted variable-name tuples of degree at most 16 required')
            c = rational(coefficient)
            if c:
                clean[monomial] = c
        if len({v for mon in clean for v in mon}) > 32:
            raise ValueError('at most 32 variables are supported')
        self._terms = MappingProxyType(clean)

    @property
    def terms(self):
        return self._terms

    @classmethod
    def variable(cls, name):
        return cls({(name,): 1})

    @classmethod
    def constant(cls, value):
        return cls({(): value})

    @staticmethod
    def coerce(value):
        if type(value) is Polynomial:
            return value
        return Polynomial.constant(rational(value))

    def __add__(self, other):
        other = self.coerce(other)
        terms = dict(self.terms)
        for mon, value in other.terms.items():
            terms[mon] = terms.get(mon, 0) + value
        return Polynomial(terms)
    __radd__ = __add__

    def __neg__(self):
        return Polynomial({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + (-self.coerce(other))

    def __rsub__(self, other):
        return self.coerce(other) + (-self)

    def __mul__(self, other):
        other = self.coerce(other)
        if len(self.terms)*len(other.terms) > MAX_PAIRS:
            raise ValueError('polynomial multiplication exceeds pair budget')
        if self.terms and other.terms and max(map(len, self.terms))+max(map(len, other.terms)) > 16:
            raise ValueError('polynomial product degree exceeds 16')
        terms = defaultdict(Fraction)
        for m, a in self.terms.items():
            for n, b in other.terms.items():
                terms[tuple(sorted(m+n))] += a*b
        return Polynomial(dict(terms))
    __rmul__ = __mul__

    def __truediv__(self, other):
        other = rational(other)
        if not other:
            raise ValueError('division requires a nonzero rational scalar')
        return self*(1/other)

    def __pow__(self, exponent):
        integer(exponent)
        if not 0 <= exponent <= 16:
            raise ValueError('exponent must be 0..16')
        out = Polynomial.constant(1)
        for _ in range(exponent):
            out *= self
        return out

    def __eq__(self, other):
        if type(other) in (int, Fraction):
            other = self.constant(other)
        return type(other) is Polynomial and self.terms == other.terms

    def derivative(self, variable):
        Polynomial.variable(variable)
        terms = {}
        for mon, c in self.terms.items():
            n = mon.count(variable)
            if n:
                shorter = list(mon)
                shorter.remove(variable)
                terms[tuple(shorter)] = n*c
        return Polynomial(terms)

    def evaluate(self, values):
        variables = {v for mon in self.terms for v in mon}
        if type(values) is not dict or set(values) != variables:
            raise ValueError('evaluation needs exactly the polynomial variables')
        values = {k: rational(v) for k, v in values.items()}
        total = Fraction(0)
        for mon, c in self.terms.items():
            for v in mon:
                c *= values[v]
            total += c
        return rational(total)


P = Polynomial.variable


def jsonable(value):
    if type(value) is Fraction:
        return str(value)
    if type(value) is dict:
        if any(type(k) is not str for k in value):
            raise ValueError('JSON keys must be strings')
        return {k: jsonable(v) for k, v in value.items()}
    if type(value) in (tuple, list):
        return [jsonable(v) for v in value]
    if value is None or type(value) in (str, int, bool):
        return value
    raise ValueError('unsupported exact JSON value')


def canonical_bytes(value):
    return (json.dumps(jsonable(value), sort_keys=True, separators=(',', ':'))+'\n').encode('ascii')


def _unique_keys(pairs):
    result = {}
    for k, v in pairs:
        if k in result:
            raise ValueError('duplicate JSON key')
        result[k] = v
    return result


def _bad_constant(value):
    raise ValueError('nonfinite JSON constant')


def _json_integer(value):
    if len(value.lstrip('-')) > 160:
        raise ValueError('JSON integer exceeds digit budget')
    return integer(int(value))


def load_certificate(path):
    if type(path) is not str and not isinstance(path, Path):
        raise ValueError('certificate path must be str or Path')
    with Path(path).open('rb') as stream:
        data = stream.read(300001)
    if len(data) > 300000:
        raise ValueError('certificate exceeds 300000 bytes')
    try:
        decoded = data.decode('utf-8')
        depth = 0
        inside_string = escaped = False
        for char in decoded:
            if inside_string:
                if escaped:
                    escaped = False
                elif char == '\\':
                    escaped = True
                elif char == '"':
                    inside_string = False
            elif char == '"':
                inside_string = True
            elif char in '[{':
                depth += 1
                if depth > 16:
                    raise ValueError('JSON nesting exceeds depth 16')
            elif char in ']}':
                depth -= 1
        return json.loads(decoded, object_pairs_hook=_unique_keys,
                          parse_constant=_bad_constant, parse_float=_bad_constant, parse_int=_json_integer)
    except (UnicodeError, RecursionError) as error:
        raise ValueError('invalid bounded JSON certificate') from error


def vector(value, length, bound):
    integer(length, 'vector length')
    integer(bound, 'vector bound')
    if not 1 <= length <= 32 or bound < 0:
        raise ValueError('vector length must be 1..32 and bound nonnegative')
    if type(value) not in (tuple, list) or len(value) != length:
        raise ValueError('vector has incorrect length')
    for x in value:
        integer(x)
        if abs(x) > bound:
            raise ValueError('vector coordinate exceeds bound')
    return tuple(value)


def midpoint_relations():
    """Reconstruct all nine transversal lines from the formal source grid."""
    grid = {(x, y): ((x+(y == 2)) % 3, int(y == 1), int(y == 2))
            for x, y in product(range(3), repeat=2)}
    def normalize(v):
        sign = next((1 if x > 0 else -1 for x in v if x), 1)
        return tuple(sign*x for x in v)
    def alternatives(t):
        return tuple(sorted(normalize(tuple(3*t[k][i]-sum(q[i] for q in t) for i in range(3)))
                            for k in range(3)))
    lines = [tuple(grid[((start+slope*y) % 3, y)] for y in range(3))
             for slope, start in product(range(3), repeat=2)]
    relations = tuple(sorted({alternatives(t) for t in lines}))
    zero = (0, 0, 0)
    triples = ((zero,(0,1,0),(1,0,1)), (zero,(0,1,0),(-2,0,1)),
               (zero,(1,1,0),(0,0,1)), (zero,(-2,1,0),(0,0,1)),
               (zero,(2,1,0),(2,0,1)), (zero,(-1,1,0),(-1,0,1)))
    require(len(relations) == 6 and set(relations) == {alternatives(t) for t in triples},
            'the displayed six triples do not cover the nine transversal lines')
    return relations, [relations.index(alternatives(t)) for t in lines]


def verify_midpoint_certificate(certificate):
    if type(certificate) is not dict or set(certificate) != {'schema_version','relations','certificates'}:
        raise ValueError('incorrect certificate fields')
    if type(certificate['schema_version']) is not int or certificate['schema_version'] != 1:
        raise ValueError('incorrect schema version')
    relations, coverage = midpoint_relations()
    given = certificate['relations']
    if type(given) is not list or len(given) != 6:
        raise ValueError('six relation groups required')
    normalized = []
    for group in given:
        if type(group) is not list or len(group) != 3:
            raise ValueError('three midpoint alternatives required')
        normalized.append(tuple(vector(v, 3, 6) for v in group))
    require(tuple(normalized) == relations, 'relation data differs from regenerated geometry')
    records = certificate['certificates']
    if type(records) is not list or len(records) != 729:
        raise ValueError('exactly 729 records required')
    seen = set()
    maximum = 0
    for record in records:
        if type(record) is not dict or set(record) != {'choice','relation_columns','integer_combination'}:
            raise ValueError('incorrect record fields')
        choice = vector(record['choice'], 6, 2)
        if any(x < 0 for x in choice) or choice in seen:
            raise ValueError('invalid or duplicate midpoint choice')
        seen.add(choice)
        columns = record['relation_columns']
        if type(columns) is not list or len(columns) != 6:
            raise ValueError('six relation columns required')
        columns = tuple(vector(v, 3, 6) for v in columns)
        require(columns == tuple(relations[j][choice[j]] for j in range(6)), 'wrong relation columns')
        coefficients = vector(record['integer_combination'], 6, 6)
        require(tuple(sum(coefficients[j]*columns[j][i] for j in range(6)) for i in range(3)) == (6,0,0),
                'integer linear combination does not certify 6v=0')
        maximum = max(maximum, max(map(abs, coefficients)))
    require(seen == set(product(range(3), repeat=6)), 'incomplete midpoint coverage')
    return {'choices':729, 'transversal_line_relation_indices':coverage,
            'maximum_absolute_integer_coefficient':maximum,
            'certified_relation':[6,0,0], 'method':'explicit integer linear combinations; no lattice saturation or HNF'}


def partitions(n, maximum=None):
    integer(n)
    if not 0 <= n <= 12:
        raise ValueError('partition size must be 0..12')
    if maximum is not None:
        integer(maximum)
        if not 1 <= maximum <= 12:
            raise ValueError('maximum part must be 1..12')
    if not n:
        yield ()
        return
    for head in range(min(n, maximum or n), 0, -1):
        for tail in partitions(n-head, head):
            yield (head,)+tail


def _assignments(counts):
    if not any(counts):
        yield ()
        return
    for i, count in enumerate(counts):
        if count:
            rest = list(counts)
            rest[i] -= 1
            for tail in _assignments(tuple(rest)):
                yield (i,)+tail


def _combination(rows, target):
    """Tiny exhaustive integer-combination finder, for three cycle equations."""
    for coeff in product(range(-2,3), repeat=len(rows)):
        if tuple(sum(a*row[j] for a,row in zip(coeff,rows)) for j in range(len(target))) == target:
            return coeff
    return None


def check_cycle_cases():
    ps = list(partitions(9))
    above35 = [(9,),(8,1),(7,2),(7,1,1),(6,3),(6,2,1),(6,1,1,1),(5,4)]
    require([p for p in ps if sum(x*x for x in p)>35] == above35, 'large derivative partitions')
    results = []
    for kind in ((8,1),(7,2),(7,1,1),(6,3),(5,4),(6,2,1),(6,1,1,1)):
        counts = Counter()
        profiles = set()
        for assignment in _assignments(kind):
            counts['assignments'] += 1
            cycles = [assignment[3*j:3*j+3] for j in range(3)]
            if any(len(set(c)) == 3 for c in cycles):
                counts['non_AP_cycle'] += 1
                continue
            rows = tuple(tuple(c.count(i) for i in range(len(kind))) for c in cycles)
            collapse = False
            for i,j in combinations(range(len(kind)),2):
                for factor in (1,2):
                    target = tuple(factor*((k==i)-(k==j)) for k in range(len(kind)))
                    coeff = _combination(rows,target)
                    if coeff is not None:
                        counts['equal_values' if factor==1 else 'doubling_injective_collapse'] += 1
                        collapse = True
                        break
                if collapse:
                    break
            if collapse:
                continue
            profile = tuple(sorted(rows))
            if kind == (6,3):
                require(profile in (((0,3),(3,0),(3,0)),((2,1),(2,1),(2,1))), 'uncovered Q45 branch')
            elif kind == (6,2,1):
                require(profile == ((0,2,1),(3,0,0),(3,0,0)), 'uncovered Q41 branch')
            else:
                raise RuntimeError('unexcluded impossible derivative partition')
            profiles.add(profile)
            counts['structural_branch'] += 1
        results.append({'partition':kind, **dict(sorted(counts.items())), 'surviving_cycle_profiles':sorted(profiles)})
    # Direct two-value cycle-count coverage, independent of assignment labels.
    q45 = sorted({tuple(sorted(k)) for k in product(range(4),repeat=3) if sum(k)==3})
    q54 = sorted({tuple(sorted(k)) for k in product(range(4),repeat=3) if sum(k)==4})
    require(q45 == [(0,0,3),(0,1,2),(1,1,1)], 'Q45 u counts')
    require(q54 == [(0,1,3),(0,2,2),(1,1,2)], 'Q41 (5,4) u counts')
    # Exhaust every exceptional-edge placement and validate the actual values
    # under x -> orientation*x + shear*y + translation.
    edges_out = []
    for edges in product(range(3), repeat=3):
        aligned = any(all(edges[j] == (b*j+c)%3 for j in range(3)) for b,c in product(range(3),repeat=2))
        wanted = (2,2,2) if aligned else (2,2,1)
        found = None
        for orientation,b,c in product((1,-1),range(3),range(3)):
            new = tuple((edges[j]-b*j-c)%3 if orientation==1 else (b*j+c-edges[j]-1)%3 for j in range(3))
            if new != wanted:
                continue
            values = [[(orientation*i+b*j+c-edges[j]-1)%3 for i in range(3)] for j in range(3)]
            for j in range(3):
                base = values[j][0 if j<2 or aligned else 2]
                target = (0,1,2) if j<2 or aligned else (1,2,0)
                require([x-base for x in values[j]] == [orientation*x for x in target], 'edge normalization')
            found = [orientation,b,c]
            break
        require(found is not None, 'missing affine exceptional-edge normalization')
        edges_out.append({'edges':edges,'aligned':aligned,'source_change':found})
    require(sum(r['aligned'] for r in edges_out)==9, 'aligned edge placements')
    # Aligned two transversal lines, coefficient order (v,u).
    triples = (((0,1),(1,2),(2,0)),((0,0),(1,2),(2,1)))
    rel = [[tuple(3*t[k][i]-sum(x[i] for x in t) for i in range(2)) for k in range(3)] for t in triples]
    aligned_choices = []
    for choice in product(range(3),repeat=2):
        rows = tuple(rel[j][choice[j]] for j in range(2))
        witness = next(((t,_combination(rows,t)) for t in ((3,0),(6,0),(0,3)) if _combination(rows,t) is not None),None)
        require(witness is not None, 'uncovered aligned midpoint choice')
        aligned_choices.append({'choice':choice,'relation':witness[0],'coefficients':witness[1]})
    return {'partitions_of_nine':len(ps),'partitions_above_35':above35,'cycle_cases':results,
            'Q45_counts':q45,'Q41_5_4_counts':q54,'edge_configurations':edges_out,
            'aligned_midpoint_choices':aligned_choices}


def points(rank):
    integer(rank)
    if not 1 <= rank <= 3:
        raise ValueError('supported rank is 1..3')
    return tuple(product(range(3),repeat=rank))


def _quadruples(rank):
    pts = points(rank)
    index = {p:i for i,p in enumerate(pts)}
    for x,y,z in product(range(len(pts)),repeat=3):
        w = index[tuple((a+b-c)%3 for a,b,c in zip(pts[x],pts[y],pts[z]))]
        yield x,y,z,w


def energies(values, weights, rank=2, modulus=None, method='quadruples'):
    """Exact (retained, ordinary) energies; rank 1..3, target Z or C_m."""
    pts = points(rank)
    n = len(pts)
    if type(values) not in (list,tuple) or len(values)!=n:
        raise ValueError('target length must equal 3**rank')
    for v in values:
        integer(v)
    if modulus is not None:
        integer(modulus)
        if modulus < 1:
            raise ValueError('modulus must be positive')
    if type(weights) not in (list,tuple) or len(weights)!=n:
        raise ValueError('weight length must equal 3**rank')
    weights = tuple(rational(w) for w in weights)
    if any(w<0 for w in weights) or not any(weights):
        raise ValueError('weights must be nonnegative and not all zero')
    if type(method) is not str or method not in ('quadruples','pairs'):
        raise ValueError('unknown exact energy method')
    if method == 'pairs':
        ordinary,respected = defaultdict(Fraction),defaultdict(Fraction)
        for x,y in product(range(n),repeat=2):
            s = tuple((a+b)%3 for a,b in zip(pts[x],pts[y]))
            target = values[x]+values[y]
            if modulus is not None:
                target %= modulus
            ordinary[s] += weights[x]*weights[y]
            respected[s,target] += weights[x]*weights[y]
        return sum(v*v for v in respected.values()),sum(v*v for v in ordinary.values())
    retained = total = Fraction(0)
    for x,y,z,w in _quadruples(rank):
        term = weights[x]*weights[y]*weights[z]*weights[w]
        total += term
        d = values[x]+values[y]-values[z]-values[w]
        if d==0 if modulus is None else d%modulus==0:
            retained += term
    return retained,total


def histograms(values, modulus=None):
    # Input validation is shared with the public exact energy interface.
    energies(values,[1]*9,2,modulus,'pairs')
    pts = points(2)
    index = {p:i for i,p in enumerate(pts)}
    result = []
    for direction in ((0,1),(1,0),(1,1),(1,2)):
        counts = Counter()
        for i,p in enumerate(pts):
            d = values[index[tuple((x+y)%3 for x,y in zip(p,direction))]]-values[i]
            counts[d if modulus is None else d%modulus] += 1
        result.append({'multiplicities':sorted(counts.values(),reverse=True),'Q':sum(c*c for c in counts.values())})
    return result


def check_histograms_and_lines():
    pattern = [0,0,0,2,2,2,-2,1,4]
    records = []
    pts = points(2)
    index = {p:i for i,p in enumerate(pts)}
    collision_differences = set()
    for direction in ((0,1),(1,0),(1,1),(1,2)):
        coefficients = {pattern[index[tuple((x+y)%3 for x,y in zip(p,direction))]]-pattern[i]
                        for i,p in enumerate(pts)}
        collision_differences.update(abs(a-b) for a,b in combinations(coefficients,2))
    require(collision_differences=={3,6,9}, 'universal normal-form histogram collision factors')
    for modulus, expected, qs in ((None,361,[41,33,33,33]),(9,369,[45,33,33,33])):
        energy = energies(pattern,[1]*9,2,modulus)
        require(energy == energies(pattern,[1]*9,2,modulus,'pairs') == (expected,729),'normal form exact energy')
        actual = histograms(pattern,modulus)
        require([r['Q'] for r in actual] == qs, 'normal form derivative histograms')
        require(expected == 81+2*sum(qs), 'derivative energy identity')
        records.append({'target_modulus':modulus,'values':pattern,'histograms':actual,'retained':expected,'ordinary':729})
    # Free integer target values on a three-point line; defect classes are
    # zero or one of the three midpoint relations, up to sign.
    defects = Counter()
    for quad in _quadruples(1):
        x,y,z,w = quad
        v = tuple((x==i)+(y==i)-(z==i)-(w==i) for i in range(3))
        defects[min(v,tuple(-k for k in v))] += 1
    require(defects[(0,0,0)]==15 and sorted(c for v,c in defects.items() if any(v))==[4,4,4], 'line midpoint energy formula')
    require(Fraction(361,729)<Fraction(41,81)<Fraction(5,9), 'indicator witness ordering')
    return {'universal_normal_form_counts':records,'generic_histogram_collision_factors':sorted(collision_differences),
            'generic_conditions':'doubling injective and 9q nonzero exclude every collision factor',
            'order_nine_conditions':'q has exact order nine, so the cyclic model is faithful',
            'line_always_retained':15,'line_each_midpoint_adds':4}


def check_three_fiber_algebra():
    x,y,z = map(P,('x','y','z'))
    N = x**4+y**4+z**4+4*(x*x*y*y+x*x*z*z+y*y*z*z)
    sos = ((x*x-y*y)**2+(y*y-z*z)**2+(z*z-x*x)**2)/2+5*((x*y-y*z)**2+(y*z-z*x)**2+(z*x-x*y)**2)/2
    require(N-5*x*y*z*(x+y+z)==sos, 'quartic 5/9 sum of squares')
    weights = [x,y,z]
    retained,total = Polynomial(),Polynomial()
    for i,j,k,l in _quadruples(1):
        term = weights[i]*weights[j]*weights[k]*weights[l]
        total += term
        if (i==2)+(j==2)==(k==2)+(l==2):
            retained += term
    require(retained==N and total==N+4*x*y*z*(x+y+z),'0,0,t energy polynomial')
    A,B,C,Ac,Bc,Cc = map(P,('A','B','C','Ac','Bc','Cc'))
    aa,bb,cc = A*Ac,B*Bc,C*Cc
    Nc = aa*aa+bb*bb+cc*cc+4*(aa*bb+bb*cc+cc*aa)
    Ec = (A*A+2*B*C)*(Ac*Ac+2*Bc*Cc)+(B*B+2*A*C)*(Bc*Bc+2*Ac*Cc)+(C*C+2*A*B)*(Cc*Cc+2*Ac*Bc)
    cross = A*A*Bc*Cc+B*B*Ac*Cc+C*C*Ac*Bc+Ac*Ac*B*C+Bc*Bc*A*C+Cc*Cc*A*B
    require(Ec==Nc+2*cross, 'arbitrary complex three-fiber identity')
    h = P('h')
    require(3*h**4+12*h**4==15*h**4 and 3*(3*h*h)**2==27*h**4,'three identical fibers attainment')
    return {'coefficient_identities':5,'SOS':'N-5xyz(x+y+z) = sum(square differences)/2 + 5 sum(product differences squared)/2',
            'three_point_energy':'E_a=N; E=N+4xyz(x+y+z)',
            'complex_identity':'E_chi=N_chi+2*(cross+conjugate cross)',
            'identical_fibers_coefficients':[15,27]}


def _qadd(a,b):
    return (a[0]+b[0],a[1]+b[1])


def _qmul(a,b):
    return (a[0]*b[0]+6*a[1]*b[1],a[0]*b[1]+a[1]*b[0])


def _qscale(c,a):
    return (c*a[0],c*a[1])


def check_reflection_algebra():
    identities = []
    def identity(left,right,name):
        require(left==right,name)
        identities.append(name)
    # Formal normalized expectation, with M1=0, M2=1, M3=s.
    t,s,M4 = map(P,('t','s','M4'))
    square = (t*t-s*t-1)**2
    moments = {0:Polynomial.constant(1),1:Polynomial(),2:Polynomial.constant(1),3:s,4:M4}
    expected_square = Polynomial()
    for mon,c in square.terms.items():
        degree = mon.count('t')
        coefficient = Polynomial({tuple(v for v in mon if v!='t'):c})
        expected_square += coefficient*moments[degree]
    identity(expected_square,M4-s*s-1,'Pearson normalized square expansion')
    skewness = []
    for k in range(1,9):
        values = [9-k]*k+[-k]*(9-k)
        M = [sum(Fraction(v**j,9) for v in values) for j in range(5)]
        require(M[1]==0 and M[2]==k*(9-k),'two-value centered variance')
        require(M[3]==k*(9-k)*(9-2*k),'two-value third moment')
        skew2 = M[3]**2/M[2]**3
        require(skew2==Fraction((9-2*k)**2,k*(9-k))==Fraction(81,k*(9-k))-4,'nine-atom skewness formula')
        require(M[4]*M[2]==M[3]**2+M[2]**3,'two-value Pearson equality')
        require(skew2<=Fraction(49,8) and (skew2==Fraction(49,8))==(k in (1,8)), 'sharp skewness endpoint')
        skewness.append({'positive_multiplicity':k,'skewness_squared':skew2})
    r,y = map(P,('r','y'))
    D = r**4+6*r*r+1+s*s
    identity((4*r*s).derivative('r')*D-4*r*s*D.derivative('r'),4*s*(1+s*s-6*r*r-3*r**4),'scalar critical derivative numerator')
    ss = 3*y*y+6*y-1
    Dstar = y*y+6*y+1+ss
    identity(Dstar,4*y*(y+3),'critical denominator simplification')
    identity(16*y*ss*y*(y+3)**2,ss*Dstar**2,'critical maximum square G')
    n,d = 3*y*y+6*y-1,y*(y+3)**2
    identity(n.derivative('y')*d-n*d.derivative('y'),-3*(y-1)*(y+1)**2*(y+3),'G derivative cross-multiplied identity')
    # Exact radicals in Q[sqrt(6)]. Only signs of rational bounds are used.
    u2,v = (Fraction(-8),Fraction(6)),(Fraction(11),Fraction(6))
    ystar = _qscale(Fraction(1,8),u2)
    u4 = _qmul(u2,u2)
    require(_qadd(_qadd(_qscale(3,u4),_qscale(48,u2)),(-456,0))==(0,0),'u stationary relation')
    Nat = _qadd(_qadd(u4,_qscale(48,u2)),(456,0))
    require(Nat==_qscale(32,v),'exact reflection constant simplification')
    ss_at = _qadd(_qadd(_qscale(3,_qmul(ystar,ystar)),_qscale(6,ystar)),(-1,0))
    require(ss_at==(Fraction(49,8),0),'skewness endpoint critical point')
    n_at = ss_at
    d_at = _qmul(ystar,_qmul(_qadd(ystar,(3,0)),_qadd(ystar,(3,0))))
    require(_qmul(n_at,_qmul(v,v))==_qscale(49,_qmul(u2,d_at)),'G endpoint equals exact k squared')
    require(Fraction(2)**2<6<Fraction(5,2)**2,'positive radical brackets')
    require(Fraction(27,8)<4 and Fraction(4,3)>1,'critical y interval inside (0,1)')
    # 0<k<1 and lambda>5/9; strict exact comparison k^2<1/2.
    positive = _qadd(_qmul(v,v),_qscale(-98,u2))
    require(positive==(1121,-456),'half bound radical residual')
    require(Fraction(49,20)**2>6 and 1121-456*Fraction(49,20)>0,'k squared below one half')
    require(Fraction(1,2)<Fraction(16,25),'lambda strictly above 5/9')
    # Arbitrary centered real vector in nine coordinates, not sampled values.
    m = P('m')
    w = [P('w'+str(i)) for i in range(8)]
    w.append(-sum(w))
    variance = sum(x*x for x in w)/9
    third = sum(x**3 for x in w)/9
    fourth = sum(x**4 for x in w)/9
    A,B = m**4+6*m*m*variance+fourth,4*m*third
    identity(sum((m+x)**4 for x in w)/9,A+B,'nine-coordinate centered fourth moment')
    identity(sum((x-m)**4 for x in w)/9,A-B,'reflected centered fourth moment')
    kappa = P('k')
    identity((1+kappa)*(A-B)-(1-kappa)*(A+B),2*(kappa*A-B),'reflection lower-bound rearrangement')
    # Formal H9 involution, for arbitrary coordinates.
    z = [P('z'+str(i)) for i in range(9)]
    mean = sum(z)/9
    hz = [x-2*mean for x in z]
    identity(sum(hz)/9,-mean,'reflection mean reversal')
    require(all(x-2*sum(hz)/9==original for x,original in zip(hz,z)),'reflection involution')
    identities.append('reflection involution in all nine coordinates')
    N = t**4+48*t*t+456
    identity(((t+8)**4+8*(t-1)**4)/9,N+224*t,'reflection extremizer fourth power')
    identity(((8-t)**4+8*(-t-1)**4)/9,N-224*t,'reflected extremizer fourth power')
    # Exact circle average: constant Laurent coefficient of
    # ((x+iy)e^(i theta)+(x-iy)e^(-i theta))^4 /16.
    x,zimag = P('x'),P('z')
    def cmul(a,b):
        return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    plus,minus = (x,zimag),(x,-zimag)
    product2 = cmul(plus,minus)
    constant = cmul(product2,product2)
    identity(constant[0]*Fraction(6,16),Fraction(3,8)*(x*x+zimag*zimag)**2,'circle-average fourth-power identity')
    identity(constant[1],0,'circle-average imaginary part zero')
    return {'identities':identities,'coefficient_identities':len(identities),
            'nine_atom_skewness':skewness,'u_squared_sqrt6_coordinates':u2,
            'N_u_sqrt6_coordinates':Nat,'k_squared_below_half_residual':positive,
            'constant':'k=7u/(11+6sqrt(6)); lambda=1/(1+k); rho=(1-k)/(1+k)',
            'rho_scope':'sharp fourth-power lower ratio; not a norm ratio',
            'mean_and_variance_degeneracies':'handled analytically in Report294; no normalization divides by zero'}


def _zeta(exponent):
    return ((Fraction(1),Fraction(0)),(Fraction(0),Fraction(1)),(Fraction(-1),Fraction(-1)))[exponent%3]


def _cadd(a,b):
    return (a[0]+b[0],a[1]+b[1])


def _cscale(c,a):
    return (c*a[0],c*a[1])


def check_spike_polynomials():
    N,E,S = [0]*5,[0]*5,[0]*5
    for quad in _quadruples(2):
        degree = quad.count(0)
        E[degree] += 1
        S[degree] += (-1)**degree
        if degree%2==0:
            N[degree] += 1
    require(N==[456,0,48,0,1] and E==[456,224,48,0,1] and S==[456,-224,48,0,1],'rank-two spike polynomial')
    require(all(2*a==b+c for a,b,c in zip(N,E,S)),'spike parity polynomial')
    # Independent ordered-pair polynomials.
    t = P('t')
    f = [t]+[Polynomial.constant(1)]*8
    ordinary,respected,signed = defaultdict(Polynomial),defaultdict(Polynomial),defaultdict(Polynomial)
    pts = points(2)
    for i,j in product(range(9),repeat=2):
        source = tuple((a+b)%3 for a,b in zip(pts[i],pts[j]))
        parity = ((i==0)+(j==0))%2
        ordinary[source] += f[i]*f[j]
        respected[source,parity] += f[i]*f[j]
        signed[source] += (-1)**parity*f[i]*f[j]
    for classes,coeffs in ((ordinary,E),(respected,N),(signed,S)):
        require(sum(v*v for v in classes.values())==sum(c*t**i for i,c in enumerate(coeffs)), 'independent polynomial pair count')
    require([int(i%2==0) for i in range(5)]==[(1+(-1)**i)//2 for i in range(5)],'order-two retention parity')
    return {'retained_coefficients':N,'ordinary_coefficients':E,'signed_coefficients':S,
            'variable':'weight t at origin, weight 1 at all eight other points',
            'coefficient_order':'constant through fourth degree','independent_pair_checks':3}


def check_fourier_and_products():
    # This coefficientwise rank-three illustration is supplemental to the
    # arbitrary-kernel Fourier argument in the report. No input f is sampled.
    pts = points(3)
    W = tuple((a,b,0) for a,b in product(range(3),repeat=2))
    checked = 0
    block_counts = Counter()
    for xi in pts:
        block_counts[xi[2]] += 1
        for x in pts:
            phase = _zeta(-sum(a*b for a,b in zip(xi,x)))
            lhs = _cscale(-1 if x[:2]==(0,0) else 1,phase)
            summation = (Fraction(0),Fraction(0))
            for eta in W:
                shifted = tuple((a+b)%3 for a,b in zip(xi,eta))
                summation = _cadd(summation,_zeta(-sum(a*b for a,b in zip(shifted,x))))
            rhs = _cadd(phase,_cscale(Fraction(-2,9),summation))
            require(lhs==rhs,'rank-three coefficientwise Fourier nine-block identity')
            checked += 1
    require(sorted(block_counts.values())==[9,9,9],'nine-element frequency blocks')
    # Character orthogonality on the quotient certifies the general block
    # multiplier: sum_{eta in F3^2} zeta^(-eta.q)=9*1_{q=0}.
    orthogonal = []
    for q in points(2):
        total = (Fraction(0),Fraction(0))
        for eta in points(2):
            total = _cadd(total,_zeta(-sum(a*b for a,b in zip(eta,q))))
        require(total==((9,0) if q==(0,0) else (0,0)),'quotient character orthogonality')
        orthogonal.append(list(total))
    # Nonconstant, non-full-support kernel product, in rank three.
    h = (1,2,0)
    Eh = sum(h[i]*h[j]*h[k]*h[l] for i,j,k,l in _quadruples(1))
    require(Eh==33,'nonuniform kernel energy')
    retained,total,signed = [0]*5,[0]*5,[0]*5
    for quad in _quadruples(3):
        degree = sum(pts[i][:2]==(0,0) for i in quad)
        coefficient = 1
        for i in quad:
            coefficient *= h[pts[i][2]]
        total[degree] += coefficient
        signed[degree] += (-1)**degree*coefficient
        if degree%2==0:
            retained[degree] += coefficient
    require(total==[33*c for c in (456,224,48,0,1)],'rank-three product ordinary energy polynomial')
    require(retained==[33*c for c in (456,0,48,0,1)],'rank-three product retained energy polynomial')
    require(signed==[33*c for c in (456,-224,48,0,1)],'rank-three product signed energy polynomial')
    # Three quotient fibers repeated across a nonconstant C3 kernel also attain
    # the no-two-torsion 5/9 bound, including a zero kernel coordinate.
    target = [int(p[0]==2) for p in points(2)]
    weights = [h[p[1]] for p in points(2)]
    ea,ev = energies(target,weights)
    require((ea,ev)==(15*Eh,27*Eh)==energies(target,weights,method='pairs'),'three-fiber nonuniform product equality')
    return {'proof_algebra':{'quotient_character_orthogonality_values':orthogonal,
              'order_two_parity':'retention=(1+product of four signs)/2'},
            'supplemental_rank_three':{'coefficientwise_fourier_identities':checked,'block_sizes':[9,9,9],
              'kernel_weight':h,'kernel_energy':Eh,'product_retained_coefficients':retained,
              'product_ordinary_coefficients':total,'product_signed_coefficients':signed},
            'supplemental_three_fiber_product':{'kernel_weight':h,'retained':ea,'ordinary':ev,'ratio':'5/9'}}


def run_checks():
    path = Path(__file__).with_name('midpoint_certificate.json')
    supplied = load_certificate(path)
    replay = verify_midpoint_certificate(supplied)
    canonical = canonical_bytes(supplied)
    require(path.read_bytes()==canonical,'certificate must have canonical JSON encoding')
    return {'report':294,'schema_version':1,'status':'passed',
            'arithmetic':'standard library; exact integers and Fractions; no CAS or numerical decisions',
            'scope':'Universal midpoint relation certificates and proof-algebra identities. Structural reductions, analytic inequalities and arbitrary-rank passage are proved in Report294. Finite examples are separately labeled.',
            'midpoint_certificate':{**replay,'sha256':sha256(canonical).hexdigest()},
            'cycle_case_coverage':check_cycle_cases(),
            'normal_forms_and_line_test':check_histograms_and_lines(),
            'three_fiber_proof_algebra':check_three_fiber_algebra(),
            'reflection_proof_algebra':check_reflection_algebra(),
            'spike_energy_polynomials':check_spike_polynomials(),
            'fourier_and_attainment':check_fourier_and_products()}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,allow_abbrev=False)
    parser.parse_args(argv)
    sys.stdout.write(canonical_bytes(run_checks()).decode('ascii'))


if __name__=='__main__':
    main()
