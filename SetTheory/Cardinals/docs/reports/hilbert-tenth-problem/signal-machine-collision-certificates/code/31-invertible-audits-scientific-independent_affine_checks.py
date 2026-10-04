"""Independent exact algebra audit; no source imports or collision execution.

All formulas below are reviewer-authored affine line equations in k=x/y,
s=time/y. They encode static mathematical identities, not an executable
signal machine. No source rules, supplied event table, stored schedule, or
author checker are loaded. Positivity is certified on the entire interval
1/4<k<1 by exact endpoint evaluations of affine functions.
"""
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json


def af(a=0, b=0):
    """a*k+b."""
    return (F(a), F(b))


def plus(p, q):
    return tuple(a+b for a, b in zip(p, q))


def minus(p, q):
    return tuple(a-b for a, b in zip(p, q))


def times(a, p):
    return tuple(F(a)*b for b in p)


def at(p, k):
    return p[0]*k+p[1]


def line(a=0, b=0, c=0):
    """a*k+b*s+c, where s is normalized absolute time."""
    return (F(a), F(b), F(c))


def evaluate(linear, moment):
    a, b, c = linear
    return plus(af(a, c), times(b, moment))


def strict_interval_certificate(p):
    values = (at(p, F(1,4)), at(p, F(1)))
    assert min(values) >= 0 and max(values) > 0, (p, values)
    return values


def det2(M):
    return M[0][0]*M[1][1]-M[0][1]*M[1][0]


def mm(A, B):
    return tuple(tuple(sum(a*b for a,b in zip(row,col))
                       for col in zip(*B)) for row in A)


# Direct global line equations, derived in REVIEW.md before this execution.
# The messenger line is unchanged across the fourth, marker-only contact.
messenger = (
    line(0, 1, 0),
    line(F(5,2), F(-3,2), 0),
    line(F(-5,3), 1, 0),
    line(F(35,36), F(-1,4), 0),
    line(F(35,36), F(-1,4), 0),
    line(F(-35,9), 1, 0),
    line(F(23,9), -1, F(5,3)),
)
marker = (
    line(1, 0, 0),
    line(F(3,2), F(-1,2), 0),
    line(F(3,2), F(-1,2), 0),
    line(F(-34,9), 2, 0),
    line(F(17,18), F(-1,2), F(5,4)),
    line(F(17,18), F(-1,2), F(5,4)),
    line(F(-2,3), 0, F(5,6)),
)
moments = (
    af(), af(1), af(F(5,3)), af(F(19,9)),
    af(F(17,9), F(1,2)), af(F(35,9)),
    af(F(29,9), F(5,6)), af(F(23,9), F(5,3)),
)
zero, one = af(), af(0,1)

# These are simultaneous contact identities, not next-event selection.
assert evaluate(messenger[0], moments[1]) == evaluate(marker[0], moments[1])
assert evaluate(messenger[1], moments[2]) == zero
assert evaluate(messenger[2], moments[3]) == evaluate(marker[2], moments[3])
assert evaluate(marker[3], moments[4]) == one
assert evaluate(messenger[4], moments[5]) == zero
assert evaluate(messenger[5], moments[6]) == evaluate(marker[5], moments[6])
assert evaluate(messenger[6], moments[7]) == zero

# Continuity is checked independently for both lines at every shared time.
for j in range(1,7):
    assert evaluate(messenger[j-1], moments[j]) == evaluate(messenger[j], moments[j])
    assert evaluate(marker[j-1], moments[j]) == evaluate(marker[j], moments[j])

# At each endpoint, (q, X-q, 1-X) are the first three gaps divided by y.
# The fourth gap is independently D/y-1>0 throughout.
contacts = (0,1,0,1,2,0,1,0)
gap_certificates = []
positions = []
for j, moment in enumerate(moments):
    piece = min(j,6)
    q = evaluate(messenger[piece], moment)
    x = evaluate(marker[piece], moment)
    positions.append((q,x))
    gaps = (q, minus(x,q), minus(one,x))
    assert gaps[contacts[j]] == zero
    gap_certificates.append(tuple(None if i == contacts[j]
                                  else strict_interval_certificate(gap)
                                  for i,gap in enumerate(gaps)))

durations = tuple(minus(moments[j+1], moments[j]) for j in range(7))
duration_certificates = tuple(strict_interval_certificate(p) for p in durations)
assert minus(moments[5], moments[4]) == af(2,F(-1,2))
assert messenger[3] == messenger[4]
assert tuple(p[1] for p in messenger) == tuple(map(F,(1,F(-3,2),1,F(-1,4),F(-1,4),1,-1)))
assert tuple(p[1] for p in marker) == tuple(map(F,(0,F(-1,2),F(-1,2),2,F(-1,2),F(-1,2),0)))

# Static pair-speed arithmetic, incoming closing and outgoing separation.
closing = tuple(map(F,(1,F(3,2),F(3,2),2,F(1,4),F(3,2),1)))
opening = tuple(map(F,(1,1,F(9,4),F(1,2),1,1,1)))
ratios = tuple(o/c for o,c in zip(opening,closing))
product = F(1)
for value in ratios:
    product *= value
assert product == F(2,3)

J = ((F(-2,3),F(5,6)),(F(0),F(1)))
Ji = ((F(-3,2),F(5,4)),(F(0),F(1)))
I = ((F(1),F(0)),(F(0),F(1)))
assert mm(J,Ji) == mm(Ji,J) == I
assert det2(J) == -product
M = ((F(1),F(0),F(0)),(F(0),F(-2,3),F(5,6)),(F(0),F(0),F(1)))
C = ((F(1),F(0),F(0)),(F(1,3),F(1),F(0)),(F(2,3),F(0),F(1)))
Ci = ((F(1),F(0),F(0)),(F(-1,3),F(1),F(0)),(F(-2,3),F(0),F(1)))
assert mm(mm(Ci,M),C) == M
assert mm(M,((F(1),),(F(1,3),),(F(2,3),))) == ((F(1),),(F(1,3),),(F(2,3),))


def encode(obj):
    if isinstance(obj,F):
        return str(obj)
    if isinstance(obj,dict):
        return {key:encode(value) for key,value in obj.items()}
    if isinstance(obj,(tuple,list)):
        return [encode(value) for value in obj]
    return obj


out = {
    'passed': True,
    'method': 'Static global affine line identities and whole-open-interval positivity; no simulation or author-source imports',
    'variables': 'k=x/y in (1/4,1), s=time/y, D/y-1>0; each affine row is [coefficient of k, constant]',
    'times_divided_by_y': moments,
    'positions_divided_by_y': positions,
    'flights_divided_by_y': durations,
    'flight_endpoint_certificates_at_k_quarter_and_one': duration_certificates,
    'first_three_gap_endpoint_certificates_at_k_quarter_and_one': gap_certificates,
    'marker_only_event4_messenger_line_unchanged': True,
    't5_minus_t4_divided_by_y': minus(moments[5],moments[4]),
    'speed_ratios': ratios,
    'J': J,
    'J_inverse': Ji,
    'determinant': det2(J),
    'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
destination = Path(__file__).with_name('independent_affine_evidence.json')
destination.write_text(json.dumps(encode(out),indent=2)+'\n')
print(json.dumps({'passed':True,'evidence':str(destination)}))
