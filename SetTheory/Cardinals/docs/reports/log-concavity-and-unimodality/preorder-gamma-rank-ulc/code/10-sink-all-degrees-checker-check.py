#!/usr/bin/env python3
"""Independent, standard-library-only exact checker.

No producer module is imported or executed. Monomials are sorted tuples of
variable IDs (not producer exponent-vector objects). Input certificates alone
use the producer's documented exponent-vector convention.

Usage: python check.py --source DIR [--output DIR]

DIR can contain the 218 certificate files directly, or contain them in the
producer's all-cloud-cubic subdirectory. No earlier theorem archive is needed.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, permutations, product
from pathlib import Path
import argparse
import json
import time


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(*polys):
    ans = {}
    for p in polys:
        for term, coefficient in p.items():
            ans[term] = ans.get(term, 0) + coefficient
    return {term: value for term, value in ans.items() if value}


def scale(p, coefficient):
    return {term: coefficient * value for term, value in p.items()
            if coefficient * value}


def multiply(p, q):
    ans = {}
    for a, x in p.items():
        for b, y in q.items():
            term = tuple(sorted(a + b))
            ans[term] = ans.get(term, 0) + x * y
    return {term: value for term, value in ans.items() if value}


def monomial(ids=(), coefficient=1):
    return {tuple(sorted(ids)): coefficient} if coefficient else {}


def elementary(ids, k):
    return add(*(monomial(s) for s in combinations(ids, k)))


def substitute(p, replacements):
    result = {}
    for term, value in p.items():
        summand = monomial((), value)
        for variable in term:
            summand = multiply(summand, replacements.get(variable,
                                                       monomial((variable,))))
        result = add(result, summand)
    return result


def encode_polynomial(p):
    return [[list(term), str(coefficient)]
            for term, coefficient in sorted(p.items())]


def polynomial_digest(p):
    raw = json.dumps(encode_polynomial(p), separators=(',', ':')).encode()
    return sha256(raw).hexdigest()


def arc(rows, i, j):
    # Physical vertices 0..3 are core; higher IDs are universal sinks.
    return i < 4 and (j >= 4 or bool(rows[i] & (1 << j)))


def perfect_matching_exists(rows, tails, heads):
    # Boolean `any`: multiple witnessing matchings never create multiplicity.
    return any(all(arc(rows, i, j) for i, j in zip(tails, image))
               for image in permutations(heads))


def literal_grouped_supports(rows):
    """Exact rank kernels with E1,E2,E3,E4 treated as variables 8..11.

    Fix the selected core tails S and core heads H. All sink subsets of the
    required size are equivalent for matching feasibility, so one fixed set
    of distinct dummy sinks tests their shared indicator. Their monomial sum
    is exactly E_(k-|H|). There are no feasible sink tails.
    """
    result = []
    for rank in range(5):
        terms = {}
        for tails in combinations(range(4), rank):
            remaining = tuple(i for i in range(4) if i not in tails)
            for h in range(min(rank, len(remaining)) + 1):
                for core_heads in combinations(remaining, h):
                    sinks = rank - h
                    heads = core_heads + tuple(range(4, 4 + sinks))
                    if perfect_matching_exists(rows, tails, heads):
                        variables = tails + tuple(4 + j for j in core_heads)
                        if sinks:
                            variables += (7 + sinks,)
                        term = tuple(sorted(variables))
                        require(term not in terms, 'Duplicate grouped support')
                        terms[term] = 1
        result.append(terms)
    return result


def literal_full_supports_hall(rows, sink_count):
    """Ungrouped cross-check including all physical tails, using Hall's test.

    This does not use the grouped-kernel reduction or the matching-permutation
    predicate. Distinct sink-head variables are 8,9,... .
    """
    vertices = tuple(range(4 + sink_count))
    result, endpoint_pairs = [], 0
    for rank in range(5):
        terms = {}
        for tails in combinations(vertices, rank):
            other = tuple(v for v in vertices if v not in tails)
            for heads in combinations(other, rank):
                endpoint_pairs += 1
                feasible = True
                for size in range(1, rank + 1):
                    for selected in combinations(tails, size):
                        neighborhood = {j for i in selected for j in heads
                                        if arc(rows, i, j)}
                        if len(neighborhood) < size:
                            feasible = False
                            break
                    if not feasible:
                        break
                if feasible:
                    require(all(i < 4 for i in tails), 'Feasible sink tail')
                    term = tuple(sorted(tails + tuple(4+j for j in heads)))
                    require(term not in terms, 'Duplicate ungrouped support')
                    terms[term] = 1
        result.append(terms)
    return result, endpoint_pairs


def stated_core_formula(rows):
    """Construct the mathematical a,b,c,d definitions separately."""
    a = add(*(monomial((i, 4+j)) for i in range(4) for j in range(4)
              if rows[i] & (1 << j)))
    b = {}
    for heads in combinations(range(4), 2):
        x, y = tuple(i for i in range(4) if i not in heads)
        j, k = heads
        feasible = ((rows[x] & (1 << j) and rows[y] & (1 << k))
                    or (rows[x] & (1 << k) and rows[y] & (1 << j)))
        if feasible:
            b = add(b, monomial((x, y, 4+j, 4+k)))
    c, d = {}, {}
    for j in range(4):
        neighbors = {i for i in range(4) if rows[i] & (1 << j)}
        others = tuple(i for i in range(4) if i != j)
        for selected in combinations(others, 2):
            if neighbors.intersection(selected):
                c = add(c, monomial(selected + (4+j,)))
        if neighbors:
            d = add(d, monomial(others + (4+j,)))
    e = [elementary(range(4), k) for k in range(5)]
    E = [monomial()] + [monomial((7+k,)) for k in range(1, 5)]
    return [monomial(), add(a, multiply(e[1], E[1])),
            add(b, multiply(c, E[1]), multiply(e[2], E[2])),
            add(multiply(d, E[2]), multiply(e[3], E[3])),
            multiply(e[4], E[4])]


def relabel(rows, permutation):
    # permutation maps old physical labels to new labels.
    new = [0] * 4
    for i in range(4):
        for j in range(4):
            if rows[i] & (1 << j):
                new[permutation[i]] |= 1 << permutation[j]
    return tuple(new)


def graph_orbits(all_rows):
    remaining, answer = set(all_rows), {}
    while remaining:
        seed = min(remaining)
        orbit = {relabel(seed, p) for p in permutations(range(4))}
        require(orbit <= remaining, 'Permutation orbits overlap incorrectly')
        remaining.difference_update(orbit)
        answer[min(orbit)] = orbit
    return answer


def is_preorder(rows):
    relation = {(i, i) for i in range(4)}
    relation |= {(i, j) for i in range(4) for j in range(4)
                 if rows[i] & (1 << j)}
    return all((i, k) in relation for i, j in relation for j2, k in relation
               if j == j2)


def reduced_gap(grouped):
    A, B = monomial((8,)), monomial((9,))
    E1 = add(A, B)
    E2 = add(multiply(A, B), scale(multiply(B, B), Fraction(1, 2)))
    E3 = add(scale(multiply(A, multiply(B, B)), Fraction(1, 2)),
             scale(multiply(B, multiply(B, B)), Fraction(1, 6)))
    g = [substitute(grouped[k], {8:E1, 9:E2, 10:E3}) for k in range(1, 4)]
    gap = add(scale(multiply(g[1], g[1]), 4),
              scale(multiply(g[0], g[2]), -12))
    G1, G2, G3 = g[0], scale(g[1], 2), scale(g[2], 6)
    alternative = add(multiply(G2, G2), scale(multiply(G1, G3), -2))
    require(gap == alternative, 'Scaled-gap convention mismatch')
    require(all(c.denominator == 1 for c in gap.values()),
            'Reduced gap unexpectedly has nonintegral coefficients')
    require(all(sum(v < 4 for v in t) == 4
                and sum(v >= 4 for v in t) == 4 for t in gap),
            'Unexpected gap bidegree')
    return gap


def parse_exponent(raw):
    require(isinstance(raw, list) and len(raw) == 10, 'Bad exponent dimension')
    require(all(type(x) is int and x >= 0 for x in raw), 'Bad exponent value')
    return tuple(v for v, count in enumerate(raw) for _ in range(count))


def parse_rational(raw):
    require(isinstance(raw, str), 'Certificate coefficient must be exact string')
    return Fraction(raw)


def check_certificate(cert, rows, gap):
    require(cert['rows'] == list(rows), 'Certificate graph mismatch')
    require(cert['scaled_gap'] ==
            '4*(gamma2^2-3 gamma1 gamma3) at maximal E3 cone',
            'Certificate convention mismatch')
    total = {}
    for weight_raw, (multiplier_raw, square_terms) in cert['terms']:
        weight = parse_rational(weight_raw)
        require(weight > 0, 'Square coefficient is not positive')
        multiplier = parse_exponent(multiplier_raw)
        require(len(square_terms) >= 1, 'Empty square polynomial')
        square = {}
        for exponent_raw, coefficient_raw in square_terms:
            term = parse_exponent(exponent_raw)
            coefficient = parse_rational(coefficient_raw)
            require(coefficient != 0, 'Zero square-polynomial coefficient')
            require(term not in square, 'Duplicate square-polynomial monomial')
            square[term] = coefficient
        expansion = multiply(monomial(multiplier, weight), multiply(square, square))
        require(all(sum(v < 4 for v in t) == 4 and len(t) == 8 for t in expansion),
                'Unexpected square summand bidegree')
        total = add(total, expansion)
    remainder = add(gap, scale(total, -1))
    require(all(c >= 0 for c in remainder.values()),
            'Negative remainder coefficient')
    require(add(total, remainder) == gap, 'Reconstruction mismatch')
    return remainder


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    started = time.monotonic()
    cert_dir = (args.source/'all-cloud-cubic'
                if (args.source/'all-cloud-cubic').is_dir() else args.source)
    certificates = sorted(cert_dir.glob('certificate_*.json'))
    require({p.name for p in certificates} ==
            {'certificate_'+str(i)+'.json' for i in range(218)},
            'Certificate file names or count do not match all 218 classes')
    # Provenance only: these optional producer files are hashed, never executed.
    producer_sources = [args.source/name for name in
                        ('core_kernel.py','run_cloud_cubic.py','precise_sos.py')
                        if (args.source/name).is_file()]
    source_files = sorted(certificates + producer_sources)
    source_hashes = {p.name:sha256(p.read_bytes()).hexdigest() for p in source_files}
    choices = [[row for row in range(16) if not (row & (1 << i))]
               for i in range(4)]
    all_rows = list(product(*choices))
    require(len(set(all_rows)) == 4096, 'Wrong number of loopless labeled cores')
    orbits = graph_orbits(all_rows)
    require(len(orbits) == 218, 'Wrong number of permutation classes')
    require(set().union(*orbits.values()) == set(all_rows), 'Orbit coverage incomplete')
    require(sum(map(len, orbits.values())) == 4096, 'Orbit multiplicity error')
    representatives = sorted(orbits)
    # All 4096 labeled graphs, not only the representatives, get exact support
    # formula comparisons. Representatives are retained for certificate checks.
    kernels, support_pairs_checked = {}, 0
    for rows in all_rows:
        literal = literal_grouped_supports(rows)
        expected = stated_core_formula(rows)
        require(literal == expected, 'Boolean support formula mismatch: '+str(rows))
        support_pairs_checked += sum(len(p) for p in literal)
        if rows in orbits:
            kernels[rows] = literal
    full_endpoint_pairs = 0
    for rows in representatives:
        for n in range(5):
            direct, tested = literal_full_supports_hall(rows, n)
            full_endpoint_pairs += tested
            expanded = [substitute(p, {7+k:elementary(range(8, 8+n), k)
                                       for k in range(1, 5)})
                        for p in kernels[rows]]
            require(direct == expanded,
                    'Ungrouped Hall enumeration mismatch: '+str((rows, n)))
    records, total_squares, coefficientwise_count, preorder_count = [], 0, 0, 0
    square_size_histogram = Counter()
    binomial_only_certificates = 0
    for i, rows in enumerate(representatives):
        gap = reduced_gap(kernels[rows])
        preorder = is_preorder(rows)
        negatives = sum(c < 0 for c in gap.values())
        cert_path = cert_dir / ('certificate_'+str(i)+'.json')
        cert = json.loads(cert_path.read_text())
        remainder = check_certificate(cert, rows, gap)
        squares = len(cert['terms'])
        square_sizes = [len(entry[1][1]) for entry in cert['terms']]
        square_size_histogram.update(square_sizes)
        binomial_only_certificates += all(size == 2 for size in square_sizes)
        coefficientwise_count += negatives == 0
        preorder_count += preorder
        total_squares += squares
        records.append({'id':i, 'rows':list(rows), 'orbit_size':len(orbits[rows]),
                        'kernel_terms':len(gap), 'initial_negative_terms':negatives,
                        'positive_weight_polynomial_squares':squares,
                        'largest_square_polynomial_support':max(square_sizes,default=0),
                        'strictly_positive_remainder_terms':len(remainder),
                        'minimum_nonzero_remainder':str(min(remainder.values()))
                            if remainder else None,
                        'maximum_remainder_denominator':max(
                            (c.denominator for c in remainder.values()), default=1),
                        'kernel_sha256':polynomial_digest(gap),
                        'remainder_sha256':polynomial_digest(remainder),
                        'status':'PASS'})
    require(preorder_count == 33, 'Preorder count mismatch')
    require(source_hashes == {p.name:sha256(p.read_bytes()).hexdigest()
                             for p in source_files}, 'Source files changed during audit')
    receipt = {
        'status':'PASS', 'completed_utc':datetime.now(timezone.utc).isoformat(),
        'checker_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'standard_library_only':True, 'producer_code_imported_or_executed':False,
        'arithmetic':'Exact integers and fractions.Fraction; no floating-point proof steps',
        'variables':['u0','u1','u2','u3','v0','v1','v2','v3','A','B'],
        'scaled_gap':'Q = 4*(gamma2^2 - 3*gamma1*gamma3) = G2^2 - 2*G1*G3 at maximal E3',
        'boolean_counting':'Every feasible ordered disjoint support counted once',
        'labeled_core_formula_checks':4096, 'ranks_checked_per_core':[0,1,2,3,4],
        'feasible_grouped_support_terms_across_labeled_cores':support_pairs_checked,
        'ungrouped_hall_formula_checks':218*5,
        'ungrouped_hall_sink_counts':[0,1,2,3,4],
        'ungrouped_hall_ordered_disjoint_endpoint_pairs_tested':full_endpoint_pairs,
        'independent_permutation_classes':218,
        'orbit_size_histogram':dict(sorted(Counter(map(len,orbits.values())).items())),
        'preorder_classes':preorder_count,
        'coefficientwise_nonnegative_kernels':coefficientwise_count,
        'nonempty_certificates':sum(bool(r['positive_weight_polynomial_squares'])
                                    for r in records),
        'total_positive_weight_polynomial_squares':total_squares,
        'binomial_only_certificates':binomial_only_certificates,
        'certificates_with_larger_squares':218-binomial_only_certificates,
        'square_polynomial_support_size_histogram':dict(sorted(square_size_histogram.items())),
        'total_reconstructed_positive_remainder_terms':sum(
            r['strictly_positive_remainder_terms'] for r in records),
        'all_exact_identities_and_remainders_passed':True,
        'sources_unchanged':True, 'source_sha256':source_hashes,
        'prior_archive_dependency':False,
        'scope':'Certifies gamma2^2 >= 3*gamma1*gamma3 for arbitrary nonnegative activities '
                'and every finite independent universal-sink cloud over any loopless four-core. '
                'Together with the actual-degree first-gap theorem and the degree-four '
                'last-gap theorem this gives rank-ULC at every actual degree 0 through 4.',
        'elapsed_seconds':round(time.monotonic()-started,6), 'records':records}
    args.output.mkdir(parents=True, exist_ok=True)
    (args.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items()
                      if k not in {'records','source_sha256'}},indent=2))


if __name__ == '__main__':
    main()
