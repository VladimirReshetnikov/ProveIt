"""Fresh static affine and fixed-word certificates, not a CA evaluator.

No source imports, template compiler, global candidate enumerator, step function,
trajectory loop, or simulator is present. Fixed word intersections merely check
the explicitly proved malformed examples in AUDIT.md.
"""
from pathlib import Path
import json

OUT = Path(__file__).resolve().parent
# An affine triple stores coefficients of (D-2), J, and 1. These variables
# are nonnegative for every accepted source, since m>=1 and J>=0.
D = (1, 0, 2)
J = (0, 1, 0)
one = (0, 0, 1)
def plus(*terms):
    return tuple(sum(t[i] for t in terms) for i in range(3))
def times(k, t):
    return tuple(k*a for a in t)
def minus(a, b):
    return plus(a, times(-1, b))
records = []
def eq(label, a, b):
    if a != b:
        raise RuntimeError(label)
    records.append({'claim': label, 'equality_coefficients': a})
def ge(label, a, b, strict=False):
    margin = minus(a, b)
    if min(margin) < 0 or (strict and margin[2] <= 0):
        raise RuntimeError(label)
    records.append({'claim': label, 'positive_margin_coefficients': margin,
                    'strict': strict})
S = plus(times(2, D), times(2, one))
B2 = plus(D, one)
L = plus(times(3, D), times(4, one))
b = plus(times(4, D), times(5, one))
Z = plus(times(10, b), times(10, one), times(2, J))
r = plus(Z, J)
H = plus(b, r)
edge = plus(times(3, b), r)
phase = times(6, b)
eq('b = L+D+1', b, plus(L, D, one))
ge('head/singleton distance S-D exceeds D', minus(S, D), D, True)
ge('all other markers outside old triple window at shifted anchor', minus(Z, one), plus(times(3, b), one), True)
ge('two different markers cannot both match any triple', Z, times(2, plus(L, one)), True)
ge('context reads outside write interval', Z, b, True)
ge('control radius contains prospective data', r, times(3, b))
ge('edge exclusion separates recognition windows', H, times(4, b))
ge('pair exactness contains pair rewrite', L, B2)
ge('new triple exactness dominates pair exactness', b, L)
eq('edge bound', edge, plus(times(13, b), times(10, one), times(3, J)))
eq('main radius', plus(edge, phase), plus(times(76, D), times(105, one), times(3, J)))
eq('same-map support refinement', minus(plus(edge, phase), one), plus(times(76, D), times(104, one), times(3, J)))

# These are independently derived extrema over both signs, all t in the stated
# range, and each independently assigned d+ and d- in [1,D]. Checking extrema
# bounds every literal endpoint, including the boundary equalities.
envelopes = [
    ('edge-free', times(-1, one), plus(D, one), B2),
    ('edge-behind S..L, including reverse L+1', times(-1, plus(L, one)), plus(L, D, one), b),
    ('edge-ahead S+1..L', times(-1, L), plus(L, D), b),
    ('edge-dispatch/commit/direct', times(-1, S), plus(S, D), b),
    ('edge-endpoint both sides and update signs', times(-1, plus(S, one)), plus(S, D, one), b),
    ('phase-free', (0,0,0), D, minus(b, one)),
    ('phase-near both sides, S..L', times(-1, L), plus(L, D), minus(b, one)),
    ('phase-home', (0,0,0), plus(S, D), minus(b, one)),
]
for label, low, high, bound in envelopes:
    ge(label+' upper', bound, high)
    ge(label+' lower', low, times(-1, bound))
eq('positive phase endpoint at t=L,d=D is exactly b-1', plus(L,D), minus(b,one))
eq('positive reverse behind endpoint at t=L,d=D can reach b', plus(L,D,one), b)

def value(t, d, j):
    return t[0]*(d-2)+t[1]*j+t[2]
examples = []
for d, j in ((8,0), (18,1), (509508,0)):
    examples.append({'D': d, 'J': j, **{name:value(t,d,j) for name,t in
                    [('b',b),('edge',edge),('phase',phase),('main',plus(edge,phase)),
                     ('refined',minus(plus(edge,phase),one)),('H_edge',H)]}})
if 2*122622+4*66066 != 509508:
    raise RuntimeError('Ledger arithmetic')

fixed = []
def word(label, support, center, radius, expected):
    actual = sorted(z for z in support if abs(z-center) <= radius)
    if actual != sorted(expected):
        raise RuntimeError(label)
    fixed.append({'claim':label,'support':sorted(support),'center':center,'radius':radius,
                  'intersection':actual})
# Each set here is literal data already independently derived in the proof.
X = {0,18,23,80}
EX = {0,19,25,80}
PX = {0,18,24,80}
FX = {0,19,24,80}
word('X new triple word', X, 0, 37, {0,18,23})
word('X old triple fails exactness', X, 0, 112, X)
word('X free key sees extra marker', X, 18, 28, {0,18,23})
word('EX reverse triple word', EX, 0, 37, {0,19,25})
word('EX inverse free predecessor key sees marker', EX, 18, 28, {0,19,25})
word('PX phase reverse triple word', PX, 0, 37, {0,18,24})
word('FX phase forward triple word', FX, 0, 37, {0,19,24})
for label, support in (('Y',{0,5,200,205}), ('PY',{0,6,200,206})):
    word(label+' free first', support, 0, 28, {z for z in support if z<100})
    word(label+' free second', support, 200, 28, {z for z in support if z>100})
if not 4*37 < 200 <= 2*(37+112) < 37+380 < 2*(37+380):
    raise RuntimeError('Y threshold comparison')

# Read the inherited arithmetic certificate as JSON data, never as executable
# code. This only confirms its stated affine assertions/counts, not the CA proof.
source = Path('/workspace/shared/short-exactness-radius-20261004/proof-packet/static-algebra-certificate.json')
supplied = json.loads(source.read_text())
for rec in supplied['checks']:
    if rec['kind'] == 'nonnegative_D_ge_2_J_ge_0':
        a,c,k = rec['margin']
        if not (a >= 0 and c >= 0 and 2*a+k >= 0):
            raise RuntimeError('Supplied affine assertion: '+rec['label'])
    elif rec['kind'] != 'affine_identity':
        raise RuntimeError('Unexpected source certificate record')
result = {'status':'PASS', 'kind':'static affine and fixed-word data, no CA evaluation',
          'coefficient_basis':['D-2','J','1'], 'affine_assertions':records,
          'support_envelopes':len(envelopes), 'fixed_word_intersections':fixed,
          'numeric_substitutions':examples, 'inherited_affine_records_checked':len(supplied['checks']),
          'universal_source_table_or_universality_reproved':False}
(OUT/'static-certificates.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','fresh_affine_assertions':len(records),
                  'fixed_word_intersections':len(fixed),'numeric_substitutions':examples,
                  'inherited_affine_records_checked':len(supplied['checks'])},sort_keys=True))
