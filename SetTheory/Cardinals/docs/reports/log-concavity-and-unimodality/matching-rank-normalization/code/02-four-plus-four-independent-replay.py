#!/usr/bin/env python3
"""Independent finite certificate for graph-generic rank-four incidence.

Reconstructs every coefficient from explicit injective coordinate tuples.
Does not import or execute the producer.  Its JSON is read only after all
coefficient vectors have been constructed, for a complete hash comparison.
All mathematical checks are explicit exceptions (also active under -O).
"""
from collections import Counter
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, permutations, product
from pathlib import Path
import json
import time
import sys

BASE = Path(__file__).resolve().parent.parent / "primary"
HERE = Path(__file__).resolve().parent
FROZEN = ('check_generic_six_profiles.py',
          'check_generic_six_profiles.json')


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def normalize(pattern):
    seen = {}
    result = []
    for label in pattern:
        if label == 0:
            result.append(0)
        else:
            if label not in seen:
                seen[label] = len(seen) + 1
            result.append(seen[label])
    return tuple(result)


def plane_types():
    # Every partition of nonloop coordinate labels is represented in this
    # tiny enumeration; normalize and quotient coordinate permutations.
    types = set()
    labeled = set()
    for raw in product(range(5), repeat=4):
        pat = normalize(raw)
        if len(set(pat) - {0}) < 2:
            continue
        labeled.add(pat)
        types.add(min(normalize(p) for p in permutations(pat)))
    return sorted(types), len(labeled)


ASSIGNMENTS = {r: tuple(permutations(range(4), r)) for r in (2, 3, 4)}


def coordinate_images(rows):
    # Enumerate all ordered coordinate injections, without endpoint DP.
    return frozenset(tuple(sorted(a)) for a in ASSIGNMENTS[len(rows)]
                     if all(mask & (1 << col) for mask, col in zip(rows, a)))


def plane_minor(H, i, j):
    # A representative of each parallel pattern.  Actual minor values
    # are immaterial, but this independently realizes the rank predicate.
    vi = (0, 0) if H[i] == 0 else (1, H[i] - 1)
    vj = (0, 0) if H[j] == 0 else (1, H[j] - 1)
    return vi[0] * vj[1] - vi[1] * vj[0]


def main():
    started = time.monotonic()
    before = {name: digest(BASE / name) for name in FROZEN}
    Htypes, labeled_count = plane_types()
    require(len(Htypes) == 7, ('plane orbit count', Htypes))
    expected_types = [(0, 0, 1, 2), (0, 1, 1, 2), (0, 1, 2, 3),
                      (1, 1, 1, 2), (1, 1, 2, 2), (1, 1, 2, 3), (1, 2, 3, 4)]
    require(Htypes == expected_types, ('plane representatives', Htypes))
    masks = tuple(range(1, 16))
    images = {r: {rows: coordinate_images(rows)
                  for rows in combinations_with_replacement(masks, r)}
              for r in (2, 3, 4)}
    missing = {rows: tuple(next(i for i in range(4) if i not in image)
                           for image in im)
               for rows, im in images[3].items()}
    rows_profiles = tuple(combinations_with_replacement(masks, 6))
    require(len(rows_profiles) == 38760, 'six-row multiset count')
    pairs = tuple(combinations(range(6), 2))
    quadruples = tuple(tuple(k for k in range(6) if k not in p) for p in pairs)
    # Canonical unordered partitions are determined by the part with label 0.
    triples = tuple((0,) + t for t in combinations(range(1, 6), 2))
    other_triples = tuple(tuple(k for k in range(6) if k not in t) for t in triples)
    require(len(pairs) == 15 and len(triples) == 10, 'partition counts')
    prepared = []
    for rows in rows_profiles:
        prepared.append((rows,
            tuple((tuple(rows[i] for i in p),
                   bool(images[4][tuple(rows[i] for i in q)]))
                  for p, q in zip(pairs, quadruples)),
            tuple((missing[tuple(rows[i] for i in t)],
                   missing[tuple(rows[i] for i in u)])
                  for t, u in zip(triples, other_triples))))
    result = []
    for H in Htypes:
        minors = {(i, j): plane_minor(H, i, j) for i in range(4) for j in range(4)}
        complements = {}
        for rows, ims in images[2].items():
            complements[rows] = any(
                minors[tuple(i for i in range(4) if i not in image)] != 0
                for image in ims)
        hist = Counter()
        qd_hist = Counter()
        coeff_hash, full_hash = sha256(), sha256()
        for rows, pair_data, triple_data in prepared:
            Q = sum(int(is_basis and complements[pair]) for pair, is_basis in pair_data)
            D = sum(int(any(minors[i, j] != 0 for i in left for j in right))
                    for left, right in triple_data)
            coefficient = Q - D
            require(coefficient >= 0, ('negative', H, rows, Q, D))
            hist[coefficient] += 1
            qd_hist[Q, D] += 1
            coeff_hash.update(f'{rows}:{coefficient}\n'.encode('ascii'))
            full_hash.update(f'{rows}:{Q}:{D}\n'.encode('ascii'))
        rec = dict(H=H, profiles=sum(hist.values()), least=min(hist),
                   coefficient_counts=dict(sorted(hist.items())),
                   sha256=coeff_hash.hexdigest(), Q_D_sha256=full_hash.hexdigest(),
                   Q_D_counts=[[q, d, count] for (q, d), count in sorted(qd_hist.items())])
        result.append(rec)
        print(json.dumps({k: rec[k] for k in ('H', 'profiles', 'least', 'sha256')},
                         separators=(',', ':')), flush=True)

    # Compare only after the independent vectors have all been reconstructed.
    reference = json.loads((BASE / 'check_generic_six_profiles.json').read_text())
    require(len(reference) == len(result), 'reference type count')
    for rec, ref in zip(result, reference):
        for key in ('H', 'profiles', 'least', 'sha256'):
            require(list(rec[key]) == ref[key] if key == 'H' else rec[key] == ref[key],
                    ('reference mismatch', key, rec['H']))
        require({int(k): v for k, v in ref['coefficient_counts'].items()}
                == rec['coefficient_counts'], ('histogram mismatch', rec['H']))
        require(ref['negative_count'] == 0, ('reference negative count', rec['H']))
    after = {name: digest(BASE / name) for name in FROZEN}
    require(before == after, 'frozen input mutation')
    report = dict(status='pass', method='explicit injective coordinate tuples',
                  profiles=7 * len(rows_profiles), plane_types=7,
                  labeled_plane_partitions=labeled_count,
                  rows_per_type=len(rows_profiles), all_hashes_match=True,
                  all_coefficients_nonnegative=True, frozen_input_sha256=before,
                  verifier_sha256=digest(Path(__file__).resolve()),
                  seconds=time.monotonic() - started, records=result)
    if '--save-certificate' in sys.argv:
        (HERE.parent.parent / 'data' / 'independent_certificate.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('status', 'profiles', 'all_hashes_match', 'seconds')}), flush=True)


if __name__ == '__main__':
    main()
