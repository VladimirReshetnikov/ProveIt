#!/usr/bin/env python3
"""Fresh, standard-library exact checks of the displayed symbolic identities.

This is not a collision finder or trajectory simulator. All rows in the proof's
seven-event table are supplied explicitly. The program checks linear identities,
strict-cone certificates, local speed ratios, and matrix products. It imports no
other local file and runs no author/upstream program or saved collision schedule.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json


def row(*a):
    return tuple(Q(x) for x in a)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def mul(c, a):
    return tuple(Q(c) * x for x in a)


def matmul(a, b):
    return tuple(tuple(sum(x * y for x, y in zip(r, c)) for c in zip(*b)) for r in a)


def det(a):
    if len(a) == 1:
        return a[0][0]
    return sum((-1)**j * a[0][j] * det(tuple(tuple(r[k] for k in range(len(a)) if k != j) for r in a[1:])) for j in range(len(a)))


def serial(obj):
    if isinstance(obj, Q):
        return str(obj)
    if isinstance(obj, (list, tuple)):
        return [serial(x) for x in obj]
    if isinstance(obj, dict):
        return {k: serial(v) for k, v in obj.items()}
    return obj


# Rows use (D,x,y); these are copied from the displayed proof table, not generated.
z = row(0, 0, 0)
d = row(1, 0, 0)
x = row(0, 1, 0)
y = row(0, 0, 1)
f = row(0, Q(-2, 3), Q(5, 6))
times = (
    z, x, row(0, Q(5, 3), 0), row(0, Q(19, 9), 0),
    row(0, Q(17, 9), Q(1, 2)), row(0, Q(35, 9), 0),
    row(0, Q(29, 9), Q(5, 6)), row(0, Q(23, 9), Q(5, 3)),
)
positions = (
    (z, z, x, y, d),
    (z, x, x, y, d),
    (z, z, row(0, Q(2, 3), 0), y, d),
    (z, row(0, Q(4, 9), 0), row(0, Q(4, 9), 0), y, d),
    (z, row(0, Q(1, 2), Q(-1, 8)), y, y, d),
    (z, z, row(0, -1, Q(5, 4)), y, d),
    (z, f, f, y, d),
    (z, z, f, y, d),
)
# Velocities on the seven intervals, in the named/sorted order L,Q,X,Y,D.
velocities = (
    row(0, 1, 0, 0, 0),
    row(0, Q(-3, 2), Q(-1, 2), 0, 0),
    row(0, 1, Q(-1, 2), 0, 0),
    row(0, Q(-1, 4), 2, 0, 0),
    row(0, Q(-1, 4), Q(-1, 2), 0, 0),
    row(0, 1, Q(-1, 2), 0, 0),
    row(0, -1, 0, 0, 0),
)
contacts = (0, 1, 0, 1, 2, 0, 1, 0)  # zero-based adjacent-gap indices
# (D,x,y) = C(r,s,t), r=x-y/4>0, s=y-x>0, t=D-y>0.
C = (row(Q(4, 3), Q(4, 3), 1), row(Q(4, 3), Q(1, 3), 0), row(Q(4, 3), Q(4, 3), 0))


def cone_certificate(a):
    return matmul((a,), C)[0]


def positive(a):
    c = cone_certificate(a)
    assert all(x >= 0 for x in c) and any(x > 0 for x in c), (a, c)
    return c


flight_certificates = []
for j in range(7):
    dt = sub(times[j+1], times[j])
    certificate = positive(dt)
    for k in range(5):
        assert sub(positions[j+1][k], positions[j][k]) == mul(velocities[j][k], dt)
    flight_certificates.append(certificate)

gap_certificates = []
for j, p in enumerate(positions):
    gaps = [sub(p[k+1], p[k]) for k in range(4)]
    assert gaps[contacts[j]] == z
    gap_certificates.append([None if k == contacts[j] else positive(g) for k, g in enumerate(gaps)])

ratios = []
for j in range(1, 8):
    k = contacts[j]
    incoming = velocities[j-1][k] - velocities[j-1][k+1]
    outgoing_v = velocities[j] if j < 7 else velocities[0]
    outgoing = outgoing_v[k+1] - outgoing_v[k]
    assert incoming > 0 and outgoing > 0
    ratios.append(outgoing / incoming)

product = Q(1)
for r in ratios:
    product *= r
assert ratios == list(row(1, Q(2, 3), Q(3, 2), Q(1, 4), 4, Q(2, 3), 1))
assert -product == Q(-2, 3)

M = (row(1, 0, 0), f, row(0, 0, 1))
S = (row(1, 0, 0), row(Q(1, 3), 1, 0), row(Q(2, 3), 0, 1))
S_inverse = (row(1, 0, 0), row(Q(-1, 3), 1, 0), row(Q(-2, 3), 0, 1))
centered = matmul(matmul(S_inverse, M), S)
J = (row(Q(-2, 3), Q(5, 6)), row(0, 1))
J_inverse = (row(Q(-3, 2), Q(5, 4)), row(0, 1))
assert centered == (row(1, 0, 0), row(0, Q(-2, 3), Q(5, 6)), row(0, 0, 1))
assert det(M) == det(J) == -product
assert matmul(J, J_inverse) == (row(1, 0), row(0, 1))
assert matmul(J_inverse, J) == (row(1, 0), row(0, 1))
center = row(1, Q(1, 3), Q(2, 3))
for a in (x, sub(y,x), sub(d,y), sub(mul(4,x),y)):
    assert sum(u*v for u,v in zip(a,center)) > 0

# Verify the generic omitted-coordinate projection determinant formula in exact
# symbolic coefficient instances; the general proof is given in PROOF.md.
projection_checks = 0
for dimension in range(2, 7):
    w = tuple(Q(i+1) * (-1 if i % 2 else 1) for i in range(dimension))
    for source in range(dimension):
        for target in range(dimension):
            columns = [k for k in range(dimension) if k != source]
            rows = [k for k in range(dimension) if k != target]
            p = tuple(tuple((Q(i == k) - w[i] * Q(target == k) / w[target]) for k in columns) for i in rows)
            assert det(p) == (-1)**(source+target) * w[source]/w[target]
            projection_checks += 1

out = {
    'all_checks_passed': True,
    'method': 'static rational row and matrix identities, no collision selection or numerical trajectory simulation',
    'event_count': 7,
    'live_signals': 5,
    'standalone_meta_signals': 11,
    'exact_chamber_rows_Dxy': [x, sub(y,x), sub(d,y), sub(mul(4,x),y)],
    'homogeneous_return_Dxy': M,
    'centered_return_DXY': centered,
    'planar_matrix': J,
    'planar_inverse': J_inverse,
    'return_determinant': det(J),
    'duration_Dxy': times[-1],
    'speed_ratios': ratios,
    'flight_strict_cone_certificates': flight_certificates,
    'event_gap_strict_cone_certificates': gap_certificates,
    'projection_identity_instances': projection_checks,
    'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
out_path = Path(__file__).parent / 'evidence' / 'static_checks.json'
out_path.write_text(json.dumps(serial(out), indent=2) + '\n')
print(json.dumps(serial({'all_checks_passed':True,'return_determinant':det(J),'projection_identity_instances':projection_checks,'evidence':str(out_path)}), indent=2))
