#!/usr/bin/env python3
"""Independent exact a=2 positivity audit; standard library only.

Reads certificate data, never producer/verifier code. Rebuilds gamma and gap
polynomials, Newton coefficients by finite differences (not Stirling tables),
all eight shifted population faces, and rational SOS expansions. Outputs an
immutable-input digest receipt and a per-gap-instance coverage ledger.
"""
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import product, permutations
from math import comb, factorial, gcd
from pathlib import Path
import json
import time

Z = (0, 0, 0)
EXP = sorted(e for e in product(range(5), repeat=3) if sum(e) <= 4)
PERMS = list(permutations(range(3)))

def need(ok, message):
    if not ok:
        raise AssertionError(message)

def clean(p):
    return {e: c for e, c in p.items() if c}

def add(p, q, factor=1):
    r = dict(p)
    for e, c in q.items():
        r[e] = r.get(e, 0) + factor * c
    return clean(r)

def mul(p, q):
    r = {}
    for e, c in p.items():
        for f, d in q.items():
            k = tuple(e[i] + f[i] for i in range(3))
            r[k] = r.get(k, 0) + c * d
    return clean(r)

def scaled(p, a):
    return clean({e: a*c for e, c in p.items()})

def exponent(e):
    need(isinstance(e, (list, tuple)) and len(e) == 3, 'Bad exponent shape')
    need(all(type(i) is int and i >= 0 for i in e), 'Bad exponent entry')
    return tuple(e)

def poly_pairs(pairs, maxdegree=4):
    p = {}
    for e, c in pairs:
        e = exponent(e)
        need(sum(e) <= maxdegree, 'Degree bound exceeded')
        need(e not in p, 'Duplicate exponent in polynomial encoding')
        p[e] = Fraction(c)
        need(p[e] != 0, 'Zero term in sparse encoding')
    return p

def array_poly(a):
    need(len(a) == len(EXP), 'Bad coefficient-array length')
    need(all(type(c) is int for c in a), 'Noninteger target coefficient')
    return clean(dict(zip(EXP, a)))

def vector(p):
    need(set(p) <= set(EXP), 'Polynomial outside total degree four')
    return tuple(p.get(e, 0) for e in EXP)

def permute(p, perm):
    return {tuple(e[i] for i in perm): c for e, c in p.items()}

def digest(path):
    h = sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024*1024), b''):
            h.update(block)
    return h.hexdigest()

def log(message):
    print(message, flush=True)

def decode_jsonl(path):
    with path.open() as f:
        for line in f:
            yield json.loads(line)

# The exact generalized-binomial polynomial basis, expanded by multiplication.
BINOMIAL_POLYS = {}
for e in EXP:
    p = {Z: Fraction(1)}
    for j, power in enumerate(e):
        unit = tuple(int(i == j) for i in range(3))
        for k in range(power):
            p = mul(p, clean({unit: Fraction(1), Z: Fraction(-k)}))
        p = scaled(p, Fraction(1, factorial(power)))
    BINOMIAL_POLYS[e] = p

# Newton coefficients of x^e, obtained directly from finite differences at zero.
# Independently reconstruct every monomial in rational arithmetic to validate
# the transform once; applying it thereafter uses arbitrary-precision integers.
NEWTON = {}
FACE = {}
for e in EXP:
    column = {}
    for f in product(*(range(k+1) for k in e)):
        c = 1
        for n, k in zip(e, f):
            c *= sum((-1)**(k-j)*comb(k, j)*j**n for j in range(k+1))
        if c:
            column[f] = c
    reconstructed = {}
    for f, c in column.items():
        reconstructed = add(reconstructed, BINOMIAL_POLYS[f], c)
    need(reconstructed == {e: 1}, 'Newton transform reconstruction failure')
    NEWTON[e] = column
    for mask in range(8):
        if any(e[j] and not(mask & (1 << j)) for j in range(3)):
            FACE[mask, e] = {}
        else:
            # Direct binomial theorem for x_j -> 1+y_j on the active face.
            FACE[mask, e] = {
                f: comb(e[0], f[0])*comb(e[1], f[1])*comb(e[2], f[2])
                for f in product(*(range(k+1) for k in e))
            }


def transform(p, columns):
    out = {}
    for e, c in p.items():
        for f, d in columns[e].items():
            out[f] = out.get(f, 0) + c*d
    return clean(out)

FACE_COLUMNS = [{e: FACE[mask, e] for e in EXP} for mask in range(8)]

# Directly expand the ten *unscaled* input gamma basis polynomials using Fraction.
INPUT_BASIS = [BINOMIAL_POLYS[e] for e in
    [(0,0,0),(1,0,0),(0,1,0),(0,0,1),(2,0,0),(0,2,0),(0,0,2),
     (1,1,0),(1,0,1),(0,1,1)]]
TWICE_INPUT_BASIS = []
for p in INPUT_BASIS:
    r = scaled(p, 2)
    need(all(c.denominator == 1 for c in r.values()), '2 gamma not integral')
    TWICE_INPUT_BASIS.append({e: int(c) for e, c in r.items()})


def gamma_row(row):
    result = {}
    for c, p in zip(row, TWICE_INPUT_BASIS):
        if c:
            result = add(result, p, c)
    return result


def recognize_positive_ray(ray):
    """Return a constructive rational certificate, without any producer basis.

    Every nonnegative-coefficient ray is positive on the orthant. Otherwise a
    three-term ray must equal A*y^m*(y^a + b*y^c)^2, with A>0 and b rational.
    """
    if all(c >= 0 for c in ray.values()):
        return 'nonnegative_coefficients'
    need(len(ray) == 3, 'Unexplained nontrivial ray without square metadata')
    pos = [(e, c) for e, c in ray.items() if c > 0]
    neg = [(e, c) for e, c in ray.items() if c < 0]
    need(len(pos) == 2 and len(neg) == 1, 'Ray has no three-term square sign pattern')
    (p, A), (q, C) = pos
    r, B = neg[0]
    need(all(p[j]+q[j] == 2*r[j] for j in range(3)), 'Square exponents mismatch')
    need(B*B == 4*A*C, 'Square discriminant mismatch')
    m = tuple(min(p[j], q[j]) for j in range(3))
    need(all((p[j]-m[j]) % 2 == (q[j]-m[j]) % 2 == 0 for j in range(3)),
         'Square exponent parity mismatch')
    a = tuple((p[j]-m[j])//2 for j in range(3))
    c = tuple((q[j]-m[j])//2 for j in range(3))
    root = {a: Fraction(1), c: B/(2*A)}
    regenerated = mul({m: A}, mul(root, root))
    need(regenerated == ray, 'Constructive rational square reconstruction mismatch')
    return 'rational_binomial_square'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--source', type=Path, default=Path(__file__).resolve().parent.parent/'two-attachment')
    ap.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    args = ap.parse_args()
    D, O = args.source, args.output
    O.mkdir(parents=True, exist_ok=True)
    start = time.time()
    inputs = ['a2_polynomials.jsonl','coefficient_certificates.json',
              'gap2_unresolved_faces.jsonl','gap3_unresolved_faces.jsonl',
              'quartic_sos_basis.json','quartic_sos_aliases.json',
              'quartic_sos_certificates.jsonl','quartic_general_sos.jsonl']
    hashes = {name: digest(D/name) for name in inputs}
    counters = Counter()
    weights = []

    basis_data = json.loads((D/'quartic_sos_basis.json').read_text())
    need(basis_data['exponents'] == [list(e) for e in EXP], 'Exponent-order mismatch')
    need(basis_data['permutations'] == [list(p) for p in PERMS], 'Permutation-table mismatch')
    rays = []
    for meta in basis_data['basis']:
        if 'monomial' in meta:
            need(set(meta) == {'monomial'}, 'Unexpected monomial metadata')
            ray = {exponent(meta['monomial']): Fraction(1)}
        else:
            need(set(meta) == {'multiplier','left','right','u','v'}, 'Unexpected square metadata')
            m, a, b = (exponent(meta[k]) for k in ['multiplier','left','right'])
            u, v = Fraction(meta['u']), Fraction(meta['v'])
            need(u > 0 and v > 0 and a != b, 'Invalid binomial-square roots')
            ray = mul({m: Fraction(1)}, mul({a:u,b:-v}, {a:u,b:-v}))
        need(all(sum(e) <= 4 for e in ray), 'Basis ray degree exceeds four')
        rays.append(ray)
    need(len(rays) == 530, 'Unexpected basis-ray count')

    targets, pending, seen_targets = {}, set(), set()
    for cert in decode_jsonl(D/'quartic_sos_certificates.jsonl'):
        pid = cert['polynomial']
        need(type(pid) is int and pid == len(targets), 'Nonsequential/duplicate target ID')
        p = array_poly(cert['coefficients'])
        v = vector(p)
        need(v not in seen_targets, 'Duplicate normalized target')
        need(gcd(*v) == 1, 'Target not primitive')
        need(v == min(vector(permute(p, t)) for t in PERMS), 'Target not canonical')
        targets[pid] = p
        seen_targets.add(v)
        if cert['terms'] is None:
            pending.add(pid)
            continue
        result = {}
        need(len(cert['terms']) > 0, 'Empty certificate')
        for j, w in cert['terms']:
            need(type(j) is int and 0 <= j < len(rays), 'Invalid basis-ray ID')
            w = Fraction(w)
            need(w > 0, 'Nonpositive certificate weight')
            weights.append(w)
            result = add(result, rays[j], w)
            counters['standard_weighted_rays'] += 1
        need(result == p, 'Incorrect rational standard identity: '+str(pid))
        counters['standard_identities'] += 1
    need(len(targets) == 29215, 'Unexpected normalized-target count')
    log('PASS all 28,881 ordinary-library rational identities; 334 general targets remain')

    general_seen = set()
    for cert in decode_jsonl(D/'quartic_general_sos.jsonl'):
        pid = cert['polynomial']
        need(pid in pending and pid not in general_seen, 'Duplicate or extraneous general certificate')
        general_seen.add(pid)
        need(cert['terms'], 'Empty general certificate')
        result = {}
        for w, pairs, meta in cert['terms']:
            w = Fraction(w)
            need(w > 0, 'Nonpositive general certificate weight')
            weights.append(w)
            ray = poly_pairs(pairs)
            if meta is not None:
                need(len(meta) == 2, 'Bad square metadata')
                m, root_pairs = meta
                m = exponent(m)
                root = poly_pairs(root_pairs)
                regenerated = mul({m: Fraction(1)}, mul(root, root))
                need(regenerated == ray, 'General square metadata fails exact expansion')
                counters['general_explicit_square_rays'] += 1
            else:
                counters['general_'+recognize_positive_ray(ray)+'_rays'] += 1
            result = add(result, ray, w)
            counters['general_weighted_rays'] += 1
        need(result == targets[pid], 'Incorrect rational general identity: '+str(pid))
    need(general_seen == pending, 'Missing general certificates')
    need(len(general_seen) == 334, 'Unexpected general-target count')
    log('PASS all 334 general rational identities and every ray positivity construction')

    # Reconstruct the exceptional identity independently of the stored terms.
    roots = [({(0,1,1):2,(0,1,0):-1,(0,0,1):-1,Z:-40},Fraction(1,4)),
             ({(0,1,0):1,(0,0,1):1,Z:-10},Fraction(27,4)),
             ({(0,1,0):1,(0,0,1):-1},Fraction(54))]
    special = {}
    for root, weight in roots:
        special = add(special, mul(root,root), weight)
    need(special == targets[6481], 'Special identity does not equal target 6481')
    need(sum(c*5**(e[1]+e[2]) for e,c in special.items()) == 0, 'Special interior zero not verified')

    aliases = {}
    for r in json.loads((D/'quartic_sos_aliases.json').read_text()):
        key = (r['id'], r['gap'], r['face'])
        need(key not in aliases, 'Duplicate face alias')
        need(all(type(k) is int for k in key) and 0 <= key[0] < 89863 and key[1] in (2,3) and 0 <= key[2] < 8,
             'Alias outside input domain')
        need(type(r['scale']) is int and r['scale'] > 0, 'Nonpositive/noninteger alias scale')
        need(type(r['permutation']) is int and 0 <= r['permutation'] < 6, 'Invalid alias permutation')
        need(r['polynomial'] in targets, 'Unknown alias target')
        aliases[key] = r
    need(len(aliases) == 39959, 'Unexpected alias count')
    unresolved = {}
    for gap in (2,3):
        for r in decode_jsonl(D/f'gap{gap}_unresolved_faces.jsonl'):
            key = (r['id'],r['gap'],r['face'])
            need(key not in unresolved and r['gap'] == gap, 'Duplicate or inconsistent unresolved face')
            unresolved[key] = array_poly(r['coefficients'])
    need(set(unresolved) == set(aliases), 'Aliases and unresolved-face files disagree')

    advertised = {}
    for r in json.loads((D/'coefficient_certificates.json').read_text()):
        gap = r['gap']
        need(gap in (2,3) and gap not in advertised, 'Duplicate/unknown coefficient-certificate group')
        for key in ['binomial_positive_ids','all_faces_coefficient_positive_ids']:
            ids = r[key]
            need(len(ids) == len(set(ids)), 'Duplicate coefficient-certificate ID')
            need(all(type(i) is int and 0 <= i < 89863 for i in ids), 'Invalid coefficient-certificate ID')
        B, F = map(set, (r['binomial_positive_ids'],r['all_faces_coefficient_positive_ids']))
        need(not B & F, 'Overlapping coefficient-certificate classes')
        advertised[gap] = (B,F)
    need(set(advertised) == {2,3}, 'Missing coefficient-certificate group')

    computed = {k: {'binomial':set(),'all_faces':set(),'sos_inputs':set(),
                    'face_positive':[0]*8,'face_sos':[0]*8} for k in (2,3)}
    used_aliases, used_targets, gamma_seen = set(), set(), set()
    swaps = [0,2,1,3,5,4,6,7,9,8]
    special_links = []
    input_count = 0
    ledger_path = O/'coverage_ledger.jsonl'
    with ledger_path.open('w') as ledger:
        for r in decode_jsonl(D/'a2_polynomials.jsonl'):
            rid, gamma = r['id'],r['gamma']
            need(type(rid) is int and rid == input_count, 'Input IDs not sequential and unique')
            input_count += 1
            need(len(gamma) == 5 and all(len(row) == 10 for row in gamma), 'Bad input gamma shape')
            need(all(type(c) is int and c >= 0 for row in gamma for c in row), 'Nonintegral/negative gamma coefficient')
            need(gamma[0] == [1]+[0]*9, 'Incorrect gamma0')
            flat = tuple(c for row in gamma for c in row)
            swapped = tuple(row[j] for row in gamma for j in swaps)
            need(flat <= swapped, 'Input gamma not x1/x2 canonical')
            need(flat not in gamma_seen, 'Duplicate gamma input')
            gamma_seen.add(flat)
            G = [gamma_row(row) for row in gamma]
            for gap, left, right in [(2,4,9),(3,3,8)]:
                # G_j=2 gamma_j, so each P is exactly 4 times the requested gap.
                P = add(scaled(mul(G[gap],G[gap]),left), mul(G[gap-1],G[gap+1]),-right)
                nb = transform(P,NEWTON)
                result = {'id':rid,'gap':gap}
                C = computed[gap]
                if all(c >= 0 for c in nb.values()):
                    C['binomial'].add(rid)
                    result['certificate'] = 'nonnegative_binomial_coefficients'
                else:
                    face_results = []
                    uses_sos = False
                    for mask in range(8):
                        F = transform(P,FACE_COLUMNS[mask])
                        key = (rid,gap,mask)
                        if all(c >= 0 for c in F.values()):
                            need(key not in aliases, 'Extraneous SOS alias for coefficient-positive face')
                            C['face_positive'][mask] += 1
                            face_results.append({'face':mask,'certificate':'nonnegative_coefficients'})
                            continue
                        uses_sos = True
                        C['face_sos'][mask] += 1
                        need(key in aliases, 'Uncovered population face '+str(key))
                        alias = aliases[key]
                        need(F == unresolved[key], 'Unresolved face not equal reconstructed gamma gap '+str(key))
                        d = gcd(*F.values())
                        need(d == alias['scale'], 'Incorrect face normalization scale '+str(key))
                        primitive = {e:c//d for e,c in F.items()}
                        candidates = [vector(permute(primitive,p)) for p in PERMS]
                        canonical = min(candidates)
                        need(alias['permutation'] == candidates.index(canonical), 'Incorrect canonical permutation '+str(key))
                        pid = alias['polynomial']
                        need(canonical == vector(targets[pid]), 'Face maps to wrong certified target '+str(key))
                        need(permute(F,PERMS[alias['permutation']]) == scaled(targets[pid],d),
                             'Exact face-target identity mismatch '+str(key))
                        used_aliases.add(key)
                        used_targets.add(pid)
                        face_results.append({'face':mask,'polynomial':pid,'scale':d,'permutation':alias['permutation']})
                        if pid == 6481:
                            special_links.append(dict(alias))
                    if uses_sos:
                        C['sos_inputs'].add(rid)
                    else:
                        C['all_faces'].add(rid)
                    result['faces'] = face_results
                ledger.write(json.dumps(result,separators=(',',':'))+'\n')
            if input_count % 10000 == 0:
                log(f'Checked both gaps for {input_count:,} gamma inputs; elapsed {time.time()-start:.1f}s')
    need(input_count == 89863, 'Unexpected gamma-input count')
    need(used_aliases == set(aliases), 'Unused/extraneous alias records')
    need(used_targets == set(targets), 'Unreferenced certificate targets')

    summary = {}
    for gap in (2,3):
        C = computed[gap]
        need((C['binomial'],C['all_faces']) == advertised[gap], 'Advertised coefficient classes differ from exact recomputation')
        need(C['binomial'] | C['all_faces'] | C['sos_inputs'] == set(range(input_count)), 'Incomplete gap input coverage')
        summary[gap] = {k:len(C[k]) for k in ['binomial','all_faces','sos_inputs']}
        summary[gap]['coefficient_positive_faces'] = C['face_positive']
        summary[gap]['sos_faces'] = C['face_sos']
        summary[gap]['total_nonnegative_integer_population_faces_covered'] = 8*input_count
    need(hashes == {name:digest(D/name) for name in inputs}, 'Input files changed during audit')
    receipt = {
        'status':'PASS',
        'scope':'For every supplied canonical a=2 gamma polynomial, both degree-four ULC gaps are nonnegative on all nonnegative integer populations. Core-family enumeration and support-kernel derivation are separate audits. No claim about a=3 or a=4.',
        'arithmetic':'Python arbitrary-precision integers and fractions.Fraction only; no numerical packages, solver, producer, or existing verifier imported or run',
        'gamma_inputs':input_count,'gap_instances':2*input_count,
        'normalized_sos_targets':len(targets),'standard_targets':len(targets)-len(general_seen),
        'general_targets':len(general_seen),'alias_faces':len(aliases),
        'all_weights_strictly_positive':True,'minimum_weight':str(min(weights)),
        'maximum_weight_denominator':max(w.denominator for w in weights),
        'weighted_ray_counts':dict(counters),'gap_breakdown':summary,
        'special_target':6481,'special_target_original_faces':special_links,
        'input_sha256':hashes,'audit_code_sha256':digest(Path(__file__).resolve()),
        'coverage_ledger_sha256':digest(ledger_path),'seconds':round(time.time()-start,3),
    }
    (O/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    log(json.dumps(receipt,indent=2))

if __name__ == '__main__':
    main()
