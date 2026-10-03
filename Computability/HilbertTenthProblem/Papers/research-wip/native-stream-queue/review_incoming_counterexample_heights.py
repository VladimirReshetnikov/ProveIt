#!/usr/bin/env python3
"""Report34 review: pinned text, exact Laurent algebra and literal orientation guards."""
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from zipfile import ZipFile

ARCHIVE_NAME = 'Counterexample_Height_Expansions_and_Rotation_Discrepancy_Package.zip'
ARCHIVE_PIN = '7d108e8a2d8f77160b31e99758697d15d0eaf70d7ca6242d726d0d2fff24adee'
MEMBER_PINS = {'Research_Report34/README.md': 'bf13118783038839b004de040e93d0ca159b5564e155511977112ae30dbe12a4', 'Research_Report34/Research_Report34.tex': 'e4d083703b92bb1de45e68ae0a791084299d5909aea27c91f6c79f0dfe6fcb73', 'Research_Report34/evidence/PROOF-PACKET.md': '0792d80078f1cf43f50e90ed37a6bb1f2191ab9668b97bfde4ea6039038499bc', 'Research_Report34/evidence/ALL-ORDERS-SUPPLEMENT.md': '8b31ef158c9ada5b3a26cffd97c25c038a62ff707ee00a28eb24e40fd99b71b5', 'Research_Report34/evidence/rotation-counting-audit.md': '6bade97d60715d04d68cb34fdd241aa923c03ae0b7cebc788d201cc568f32542', 'Research_Report34/evidence/TRANSFER-PROOF.md': 'bbb32a8d3139370af5743c09a9b867072c849447fc37338d7c5da87044a4dc83', 'Research_Report34/evidence/FULL-SIGNED-COUNTEREXAMPLE.md': 'b109e2fd1142cdad84a5b519acc5dc5055160f1d8e7617d648a561538fd956cd'}
SOURCE_PINS = {'complete74_equation_orientation_census.json': '627568df8674e3fbe32bac6881a9ef89587a902ed25476b2a541f1eff0875559', 'complete74_equation_orientation_census.md': '292f4b2ef80c9eca684e50e561efd21469a9ad9d0c9970aab537f30f93d0776d', 'complete74_asymmetric_scale_transfer.md': '0484dc71131d7d132e12c7961de731ca4c5bb91adc98447f72fed77882461fe3', 'review_incoming_negative_index_fibers.md': '002f4c52a81462e464239cd3dfe848bc5f0d994e55b4b561729798844d61ee12'}

def need(ok, why):
    if not ok:
        raise ValueError(why)

def sha(b):
    return hashlib.sha256(b).hexdigest()

def exact(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b

# Q[d,alpha,p,ell,epsilon] with integer Laurent exponents. No CAS dependency.
ZERO = (0, 0, 0, 0, 0)
def term(coef=1, **powers):
    exponents = tuple(powers.get(n, 0) for n in ('d', 'alpha', 'p', 'ell', 'epsilon'))
    return {exponents: Fraction(coef)} if coef else {}

def add(a, b):
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, 0) + c
    return {e: c for e, c in out.items() if c}

def scale(a, c):
    return {e: v*c for e, v in a.items() if v*c}

def mul(a, b):
    out = {}
    for e, c in a.items():
        for f, d in b.items():
            key = tuple(x+y for x, y in zip(e, f))
            out[key] = out.get(key, 0) + c*d
    return {e: c for e, c in out.items() if c}

def coefficient_checks():
    one = term()
    m = add(term(Fraction(1, 2), p=1, epsilon=-1, d=-1),
            term(Fraction(-1, 2), p=1, epsilon=1, d=-1))
    first = add(add(scale(m, 2), term(p=1)), term(-1))
    second = add(mul(term(alpha=1), m), term(ell=1))
    Ap = add(term(d=1), term(-1, d=1, p=-1))
    Bp = term(2, d=1, ell=1, alpha=-1, p=-1)
    def quadratic(C):
        return add(add(one, mul(C, term(epsilon=1))), term(-1, epsilon=2))
    normal = mul(term(Fraction(1,2), alpha=1, p=2, d=-2, epsilon=-2),
                 mul(quadratic(Ap), quadratic(Bp)))
    need(mul(first, second) == normal, 'complete Laurent normal-form factorization')
    # Independent coefficient derivation: integrate (C-2e)/(1+Ce-e^2).
    # Compare against the report's power sums, for both symbolic A_p and B_p.
    combined = []
    for C in (Ap, Bp):
        inverse = [one]
        power_sums = [term(2), scale(C, -1)]
        coefficients = []
        for n in range(1, 25):
            prev = inverse[n-2] if n >= 2 else {}
            inverse.append(add(scale(mul(C, inverse[n-1]), -1), prev))
            if n >= 2:
                power_sums.append(add(scale(mul(C, power_sums[-1]), -1), power_sums[-2]))
            derivative = add(mul(C, inverse[n-1]), scale(prev, -2))
            coefficient = scale(derivative, Fraction(1, n))
            need(coefficient == scale(power_sums[n], Fraction(-1, n)),
                 'logarithm coefficient '+str(n))
            need(all(-n <= e[2] <= 0 for e in coefficient), 'degree in inverse p')
            coefficients.append(coefficient)
        combined.append(coefficients)
    a1 = add(combined[0][0], combined[1][0])
    a2 = add(combined[0][1], combined[1][1])
    need(a1 == add(Ap, Bp), 'first exponential correction')
    need(a2 == add(term(-2), scale(add(mul(Ap, Ap), mul(Bp, Bp)), Fraction(-1,2))),
         'second exponential correction')
    return dict(complete_Laurent_factorization=True, independently_derived_log_coefficients=48,
                maximum_order=24, first_two_coefficients_verified=True,
                analytic_remainder_or_count_proved_by_code=False)

def source_checks(blobs):
    forms = json.loads(blobs['complete74_equation_orientation_census.json'])['forms']
    chosen = [f['packet'] for f in forms if f['packet']['mode'] == 'signed20']
    need(len(chosen) == 8, 'eight literal signed20 orientations')
    by = {}
    for packet in chosen:
        o = packet['orientation']
        need(all(o[k] is False for k in ('E_from_a', 'kY_from_c', 'kappa_from_gap')),
             'only signed20 switches available')
        key = tuple(o[k] for k in ('asymmetric','aux_coefficient_rhs','aux_root_rhs'))
        need(key not in by, 'unique orientation')
        by[key] = packet
        d = {row[0]: row[1:] for row in packet['source']}
        need(d['L17'] == ['*', 'R16' if key[1] else 'ic22', 'aux_square_gap'], 'actual auxiliary coefficient')
        u = 'aux_u_rhs' if key[2] else 'H17'
        need(d['H2'] == ['*',u,u], 'actual auxiliary root')
        need(['ic22','R16'] in packet['comparisons'] and ['H17','aux_u_rhs'] in packet['comparisons'],
             'both protecting comparisons retained')
        need([r[0] for r in packet['source'] if 'w' in r[2:]] == ['wn2'], 'sole w consumer')
        need([r[0] for r in packet['source'] if 'r' in r[2:]] == ['r1','H17'], 'all computed r consumers')
        need([c for c in packet['comparisons'] if 'r' in c] == [['r','r_lhs']], 'packing r consumer')
        need(d['R10b'] == ['+','eta','zeta'] and d['hpm1'] == ['*','h','UM']
             and d['r1'] == ['+','r',1] and d['R11'] == ['+','r1','hpm1']
             and ['R10b','R11'] in packet['comparisons'], 'actual eliminable index equation')
        need(d['q'] == ['+','repunit',1] and d['repunit'] == ['*','Bm1','Jrep']
             and d['Lbig'] == ['*','q','q'] and d['n2'] == ['*','Lbig','q'],
             'q independent of w and n2=q^3')
        need(len(packet['witnesses']) == 20 and 'r' in packet['witnesses'], 'positive parent interface')
    for asymmetric in (False, True):
        base = by[(asymmetric,False,False)]
        bd = {r[0]:r[1:] for r in base['source']}
        for coefficient in (False,True):
            for root in (False,True):
                packet = by[(asymmetric,coefficient,root)]
                pd = {r[0]:r[1:] for r in packet['source']}
                need(pd.keys() == bd.keys(), 'orientation producer inventory')
                need({n for n in pd if pd[n] != bd[n]} <= {'L17','H2'},
                     'only protected auxiliary definitions change')
                for field in ('comparisons','witnesses','fixed_numerals','ordinary_input'):
                    need(packet[field] == base[field], 'orientation interface '+field)
    paired = 0
    for c in (False, True):
        for u in (False, True):
            old, new = by[(False,c,u)], by[(True,c,u)]
            od = {r[0]:r[1:] for r in old['source']}
            nd = {r[0]:r[1:] for r in new['source']}
            need(od.keys() == nd.keys(), 'identical producer names')
            need([n for n in od if od[n] != nd[n]] == ['wn2'], 'only scale producer differs')
            need(od['wn2'] == ['*','w','n2'] and nd['wn2'] == ['*','w','q'], 'literal scale map')
            for field in ('comparisons','witnesses','fixed_numerals','ordinary_input'):
                need(old[field] == new[field], 'paired interface '+field)
            # With the proved X cut, every other definition is identical. This
            # is a full structural source identity, not a numerical sample.
            paired += 1
    return dict(literal_parent_orientations=8, forward_source_pairs=paired,
                retained_protecting_comparisons=16, mathematical_children_per_parent=1,
                child_full_gate_ledgers_claimed=False,
                forward_map='w_asymmetric=q^2*w_symmetric; all other coordinates fixed',
                omitted_index='R=R10b-h*UM-1', inverse_integrality_claimed=False)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--incoming', type=Path, required=True)
    ap.add_argument('--output', type=Path)
    ap.add_argument('--expect', type=Path)
    a = ap.parse_args()
    archive = a.incoming/ARCHIVE_NAME
    need(sha(archive.read_bytes()) == ARCHIVE_PIN, 'archive pin')
    with ZipFile(archive) as z:
        for name, pin in MEMBER_PINS.items():
            need(sha(z.read(name)) == pin, 'member '+name)
    blobs = {}
    for name, pin in SOURCE_PINS.items():
        blobs[name] = (a.root/name).read_bytes()
        need(sha(blobs[name]) == pin, 'current source '+name)
    result = dict(status='PASS', source_sha256=sha(Path(__file__).read_bytes()),
                  archive_sha256=ARCHIVE_PIN, member_pins=MEMBER_PINS, source_pins=SOURCE_PINS,
                  algebra=coefficient_checks(), orientations=source_checks(blobs),
                  scope='Independent exact algebra and literal parent-interface checks supporting a human analytic review. No archived code executed, no complete giant zero constructed, no analytic theorem established by a finite replay, no whole-fiber count or universal arithmetic improvement claimed.')
    if a.expect:
        need(exact(result, json.loads(a.expect.read_text())), 'typed receipt replay')
    if a.output:
        a.output.write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ('status','algebra','orientations')}, sort_keys=True))

if __name__ == '__main__':
    main()
