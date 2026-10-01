#!/usr/bin/env python3
"""Fresh exact support and determinant replay of the coupled top bound."""
from collections import Counter, defaultdict
from itertools import combinations, combinations_with_replacement, permutations
from hashlib import sha256
from pathlib import Path
import json
import time
import sys
from replay import coordinate_images, digest, plane_minor, plane_types, require

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / "primary"
FROZEN = ('check_top_coupled_five.py',
          'check_top_coupled_five.json', 'check_top_coupled_six.py',
          'check_top_coupled_six.json')


def parity(seq):
    return -1 if sum(seq[i] > seq[j] for i in range(len(seq))
                     for j in range(i + 1, len(seq))) % 2 else 1


COFACTORS = {i: tuple(((-1) ** i * parity(p), p)
                      for p in permutations(tuple(j for j in range(4) if j != i)))
             for i in range(4)}


def normal(vectors):
    return tuple(sum(sign * vectors[0][p[0]] * vectors[1][p[1]] * vectors[2][p[2]]
                     for sign, p in COFACTORS[i]) for i in range(4))


def check_single_minor():
    # Expand the universal full-support five-row polynomial.  Restricting
    # row supports merely deletes monomials, so this checks every support.
    # The triples have ordered row roles (a,b,c) and (a,d,e).
    polys = defaultdict(Counter)
    nominal_terms = 0
    for i, j in combinations(range(4), 2):
        for first, second, outer in ((i, j, 1), (j, i, -1)):
            for s, p in COFACTORS[first]:
                for t, q in COFACTORS[second]:
                    key = (tuple(sorted((p[0], q[0]))), p[1], p[2], q[1], q[2])
                    polys[key][i, j] += outer * s * t
                    nominal_terms += 1
    survived = 0
    zero = 0
    for monomial, coeffs in polys.items():
        nonzero = {minor: value for minor, value in coeffs.items() if value}
        require(len(nonzero) <= 1, ('multiple H minors', monomial, nonzero))
        survived += bool(nonzero)
        zero += not nonzero
    return dict(nominal_terms=nominal_terms, distinct_monomials=len(polys),
                nonzero_monomials=survived, canceled_monomials=zero,
                maximum_nonzero_H_minors_per_monomial=1)


def main():
    start = time.monotonic()
    before = {name: digest(BASE / name) for name in FROZEN}
    # The evaluation matrix is certificate input; no result counts are used.
    five_input = json.loads((BASE / 'check_top_coupled_five.json').read_text())
    values = five_input['values']
    require(len(values) == 5 and all(len(row) == 4 for row in values), 'matrix size')
    require(all(type(x) is int for row in values for x in row), 'matrix integrality')
    symbolic_check = check_single_minor()
    Htypes, _ = plane_types()
    masks = range(1, 16)
    images = {r: {rows: coordinate_images(rows)
                  for rows in combinations_with_replacement(masks, r)}
              for r in (2, 3, 4)}
    missing = {rows: tuple(next(i for i in range(4) if i not in image) for image in ims)
               for rows, ims in images[3].items()}
    records = []
    for count in (5, 6):
        subsets = {r: tuple(combinations(range(count), r)) for r in (2, 3, 4)}
        subset_sets = {r: tuple(frozenset(s) for s in subsets[r]) for r in (2, 3, 4)}
        all_labels = frozenset(range(count))
        def covering(r, s, unordered=False):
            return tuple((i, j) for i, x in enumerate(subset_sets[r])
                         for j, y in enumerate(subset_sets[s])
                         if (not unordered or i < j) and x | y == all_labels)
        ab_pairs = covering(4, 4)
        bt_pairs = covering(4, 3)
        bp_pairs = covering(4, 2)
        tt_pairs = covering(3, 3, True)
        expected = {5: (20, 30, 20, 15), 6: (90, 60, 15, 10)}[count]
        require(tuple(map(len, (ab_pairs, bt_pairs, bp_pairs, tt_pairs))) == expected,
                ('union counting', count))
        prepared = []
        for rows in combinations_with_replacement(masks, count):
            basis_flags = tuple(bool(images[4][tuple(rows[i] for i in s)])
                                for s in subsets[4])
            triple_missing = tuple(missing[tuple(rows[i] for i in s)] for s in subsets[3])
            pair_rows = tuple(tuple(rows[i] for i in s) for s in subsets[2])
            A = sum(basis_flags[i] and basis_flags[j] for i, j in ab_pairs)
            normals = None
            if count == 5:
                vectors = tuple(tuple(values[i][j] if rows[i] & (1 << j) else 0
                                      for j in range(4)) for i in range(5))
                normals = tuple(normal(tuple(vectors[i] for i in s)) for s in subsets[3])
                # This also catches sign/index errors in the independently
                # expanded cofactors, without using a second determinant code.
                for s, cofactor in zip(subsets[3], normals):
                    require(all(sum(vectors[i][j] * cofactor[j] for j in range(4)) == 0
                                for i in s), ('annihilator identity', rows, s))
            prepared.append((rows, basis_flags, triple_missing, pair_rows, A, normals))
        require(len(prepared) == {5: 11628, 6: 38760}[count], ('row count', count))
        for H in Htypes:
            minors = {(i, j): plane_minor(H, i, j) for i in range(4) for j in range(4)}
            good_pair = {rows: any(minors[tuple(j for j in range(4) if j not in image)]
                                       != 0 for image in ims)
                         for rows, ims in images[2].items()}
            hist, joint = Counter(), Counter()
            stream, full_stream = sha256(), sha256()
            determinant_stream = sha256()
            for rows, bases, miss, pairs, A, normals in prepared:
                triples_good = tuple(any(H[i] != 0 for i in possibilities)
                                     for possibilities in miss)
                pair_good = tuple(good_pair[p] for p in pairs)
                B = sum(bases[i] and triples_good[j] for i, j in bt_pairs)
                Q = sum(bases[i] and pair_good[j] for i, j in bp_pairs)
                if count == 6:
                    D = sum(any(minors[u, v] != 0 for u in miss[i] for v in miss[j])
                            for i, j in tt_pairs)
                else:
                    # Cauchy--Binet, unlike the producer's projected 2-vectors.
                    evaluated = tuple(sum((normals[i][u] * normals[j][v]
                                          - normals[i][v] * normals[j][u]) * minors[u, v]
                                         for u, v in combinations(range(4), 2))
                                      for i, j in tt_pairs)
                    D = sum(value != 0 for value in evaluated)
                    determinant_stream.update(f'{rows}:{evaluated}\n'.encode('ascii'))
                c = 7 * D + A + B - 6 * Q
                require(c >= 0, ('negative coupled coefficient', count, H, rows, A, B, Q, D))
                hist[c] += 1
                joint[A, B, Q, D] += 1
                stream.update(f'{rows}:{c}:{D}\n'.encode('ascii'))
                full_stream.update(f'{rows}:{A}:{B}:{Q}:{D}\n'.encode('ascii'))
            rec = dict(labels=count, H=H, profiles=len(prepared), minimum=min(hist),
                       coefficient_counts=dict(sorted(hist.items())), sha256=stream.hexdigest(),
                       A_B_Q_D_sha256=full_stream.hexdigest(),
                       joint_counts=[[a, b, q, d, num] for (a, b, q, d), num in sorted(joint.items())])
            if count == 5:
                rec['all_witness_determinants_sha256'] = determinant_stream.hexdigest()
                rec['evaluated_determinants'] = len(prepared) * len(tt_pairs)
            records.append(rec)
            print(json.dumps({k: rec[k] for k in ('labels', 'H', 'profiles', 'minimum', 'sha256')}), flush=True)

    five_ref = json.loads((BASE / 'check_top_coupled_five.json').read_text())['results']
    six_ref = json.loads((BASE / 'check_top_coupled_six.json').read_text())
    require(len(five_ref) == len(six_ref) == 7, 'reference orbit count')
    for rec, ref in zip(records, five_ref + six_ref):
        require(list(rec['H']) == ref['H'], 'H reference mismatch')
        for key in ('minimum', 'sha256'):
            require(rec[key] == ref[key], ('reference mismatch', rec['labels'], rec['H'], key))
        require(ref['negative_count'] == 0, 'reference negative count')
    after = {name: digest(BASE / name) for name in FROZEN}
    require(before == after, 'frozen input changed during replay')
    output = dict(status='pass', profiles=sum(r['profiles'] for r in records),
                  five_label_profiles=81396, six_label_profiles=271320,
                  witnessed_determinants=sum(r.get('evaluated_determinants', 0) for r in records),
                  all_hashes_match=True, all_checked_lower_coefficients_nonnegative=True,
                  single_minor_symbolic_check=symbolic_check, evaluation_matrix=values,
                  frozen_input_sha256=before, verifier_sha256=digest(Path(__file__).resolve()),
                  coordinate_verifier_sha256=digest(HERE / 'replay.py'),
                  seconds=time.monotonic() - start, records=records)
    if '--save-certificate' in sys.argv:
        (HERE.parent.parent / 'data' / 'independent_coupled_certificate.json').write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({k: output[k] for k in ('status', 'profiles', 'witnessed_determinants', 'all_hashes_match', 'seconds')}), flush=True)


if __name__ == '__main__':
    main()
