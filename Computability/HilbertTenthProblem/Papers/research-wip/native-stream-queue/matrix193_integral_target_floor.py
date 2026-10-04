#!/usr/bin/env python3
"""Fresh exact certificates for a scoped integral-basis target lower bound."""
import argparse
import hashlib
import json
from pathlib import Path

PINS = {
    'matrix193_gamma1_recode.py': 'ae24e64539b450fd9c4db0b3e04ce440d00562dcfe532a43002d7c52da34757c',
    'matrix193_gamma1_recode.json': '9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668',
    'matrix193_gamma1_recode.md': '6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742',
}
I = (1, 0, 0, 1)
T = (1, 1, 0, 1)
U = (1, 0, 5, 1)
V = (-9, 5, -20, 11)
W0 = (-29, 3, -10, 1)
W1 = (-14, 3, 65, -14)
D = (0, 3, 65, 0)
J = (0, 1, 1, 0)
E = (1, 0, 0, -1)


def need(ok, label):
    if not ok:
        raise ValueError(label)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def unique_pairs(items):
    out = {}
    for key, value in items:
        need(key not in out, 'duplicate JSON key')
        out[key] = value
    return out


def read(raw):
    def nonfinite(value):
        raise ValueError('nonfinite JSON ' + value)
    return json.loads(raw, object_pairs_hook=unique_pairs, parse_constant=nonfinite)


def exact(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def mul(a, b):
    return (a[0]*b[0]+a[1]*b[2], a[0]*b[1]+a[1]*b[3],
            a[2]*b[0]+a[3]*b[2], a[2]*b[1]+a[3]*b[3])


def det(a):
    return a[0]*a[3]-a[1]*a[2]


def inv(a):
    d = det(a)
    need(d in (-1, 1), 'unimodular inverse')
    return (d*a[3], -d*a[1], -d*a[2], d*a[0])


def power(a, n):
    if n < 0:
        a, n = inv(a), -n
    result = I
    while n:
        if n & 1:
            result = mul(result, a)
        a, n = mul(a, a), n//2
    return result


def conj(a, s):
    return mul(mul(inv(s), a), s)


def plus(a, b):
    return tuple(x+y for x, y in zip(a, b))


def scale(k, a):
    return tuple(k*x for x in a)


def verify(root):
    data = {}
    for name, pin in PINS.items():
        raw = (root/name).read_bytes()
        need(sha(raw) == pin, 'pin ' + name)
        data[name] = raw
    parent = read(data['matrix193_gamma1_recode.json'])
    letters = {k: tuple(v) for k, v in parent['packet']['letters'].items()}
    tape_a, tape_b = letters['0'], letters['1']
    need(conj(mul(tape_a, tape_b), inv(V)) == T, 'H contains T')
    need(conj(inv(tape_b), inv(V)) == U, 'H contains U')
    actual_w = mul(power(mul(tape_a, tape_b), 3), power(tape_b, 2))
    need(conj(actual_w, inv(V)) == W0, 'actual repeated block')
    need(conj(W0, U) == W1 and plus(W1, scale(14, I)) == D, 'fixed normal frame')
    need(mul(D, D) == scale(195, I), 'quadratic algebra')
    need(plus(scale(14, I), D) == scale(-1, inv(W1)), 'fundamental unit in signed H')
    b = mul(actual_w, actual_w)
    d_actual = plus(b, scale(-391, I))
    need(d_actual == (-52500, 29036, -94920, 52500), 'actual bare target')

    # Every forbidden determinant Q(p,r)=+/-c is excluded at all integer
    # points by one complete modular image, not a bounded integer search.
    moduli = {
        (1, -1): 5, (1, 1): 5,
        (3, 1): 9,
        (5, -1): 13, (5, 1): 13,
        (13, -1): 8, (13, 1): 3,
        (15, -1): 13, (15, 1): 13,
        (39, -1): 5, (39, 1): 5,
        (65, -1): 3,
        (195, -1): 25, (195, 1): 25,
    }
    divisors = [c for c in range(1, 196) if 195 % c == 0]
    need(divisors == [1, 3, 5, 13, 15, 39, 65, 195], 'complete divisor list')
    certificates = []
    for (c, sign), modulus in sorted(moduli.items()):
        residues = sorted({(65*p*p-3*r*r) % modulus
                           for p in range(modulus) for r in range(modulus)})
        need((sign*c) % modulus not in residues, 'unrestricted modular exclusion')
        certificates.append(dict(c=c, sign=sign, modulus=modulus,
                                 residues=residues, excluded=(sign*c) % modulus))
    need({(c, s) for c in divisors for s in (-1, 1)}-set(moduli)
         == {(3, -1), (65, 1)}, 'exact two surviving cases')

    # The full classification is the companion Pell descent proof. These
    # exact examples check its two canonical families and lower collisions.
    units = []
    fundamental = plus(scale(14, I), D)
    for n in range(-8, 9):
        cmat = power(fundamental, n)
        r, h = cmat[0], cmat[1]//3
        need(cmat == (r, 3*h, 65*h, r), 'unit coefficient family')
        need(r*r-195*h*h == 1 and mul(cmat, D) == mul(D, cmat), 'norm one centralizer')
        for swap in (False, True):
            for flip in (False, True):
                frame = J if swap else I
                if flip:
                    frame = mul(frame, E)
                s = mul(cmat, frame)
                moved_d = conj(D, s)
                need(moved_d[0] == moved_d[3] == 0, 'equal diagonal frame')
                # C belongs to +/-H; choose a conjugate of T or U in H.
                parabolic = T if swap else U
                hword = mul(mul(cmat, parabolic), inv(cmat))
                collision = conj(hword, s)
                need(collision[:2] == (1, 0) and collision != I,
                     'exact nontrivial lower stabilizer')
        units.append(dict(n=n, root=r, coefficient=h))

    # Explicit failed one-gate frame relative to actual H'.
    actual_to_normal = mul(inv(V), U)
    one_gate_w = conj(actual_w, actual_to_normal)
    one_gate_b = mul(one_gate_w, one_gate_w)
    need(one_gate_b == (391, -84, -1820, 391), 'tempting one-gate square')
    actual_lower = mul(mul(inv(V), U), V)
    failed_lower = conj(actual_lower, actual_to_normal)
    need(failed_lower == U, 'actual group has colliding images in this frame')

    # The two shared-product alternatives become equal-diagonal under a
    # lower shear, which preserves first-row injectivity or its failure.
    shear_cases = []
    for c in divisors:
        for sign in (-1, 1):
            a = sign*c
            k = 195//c-c
            m = (a, c, k, -a)
            shear = (1, 0, -sign, 1)
            need(mul(m, m) == scale(195, I), 'shared-product discriminant')
            need(conj(m, shear) == (0, c, 195//c, 0), 'lower shear to zero diagonal')
            shear_cases.append(dict(diagonal=a, off_diagonal=c, shear=list(shear)))

    # The actual three-gate generic first-row circuit, with both ports
    # independent, and exact indexed Pell corroboration.
    source = [['scaled_psi', '*', 52500, 'psi'],
              ['target11', '+', 'chi', 'scaled_psi'],
              ['target12', '*', -29036, 'psi']]
    chi, psi = 1, 0
    for n in range(21):
        need((chi+52500*psi, -29036*psi) == power(b, -n)[:2], 'actual bare target pair')
        chi, psi = 391*chi+152880*psi, chi+391*psi
    return dict(status='PASS', source_sha256=sha(Path(__file__).read_bytes()),
                pins=PINS, normal_frame=dict(W=list(W1), D=list(D)),
                modular_exclusions=certificates, surviving_determinants=[-3, 65],
                unit_fixtures=units, equal_diagonal_collision_checks=68,
                lower_shears=shear_cases, actual_bare_source=source,
                actual_target_ledger=dict(M=2, A=1, total=3),
                indexed_target_checks=21, failed_one_gate_square=list(one_gate_b),
                failed_one_gate_collision=list(failed_lower),
                scope='Three-gate floor only for all-value first-row target assembly under integral unimodular basis changes that retain first-row injectivity on the inherited twenty-letter group H-prime. Exact index and unbounded semigroup membership remain unpaid.',
                new_universal_Diophantine_bound=False, predecessor_code_executed=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output', type=Path)
    mode.add_argument('--expect', type=Path)
    args = parser.parse_args()
    result = verify(args.root)
    if args.expect:
        need(exact(result, read(args.expect.read_bytes())), 'type-exact receipt')
    else:
        args.output.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n')
    print('PASS: integral-frame classification and scoped three-gate target floor')


if __name__ == '__main__':
    main()
