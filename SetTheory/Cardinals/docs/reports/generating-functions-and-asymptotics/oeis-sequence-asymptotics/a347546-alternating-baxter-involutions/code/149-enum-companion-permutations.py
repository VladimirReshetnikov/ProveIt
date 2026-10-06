"""Independent finite permutation checks with explicit conventions and bounds."""
from functools import lru_cache
from itertools import combinations, permutations
from math import comb, factorial
from exact import require

COUNTEREXAMPLES = (
    (11,19,15,17,16,18,13,14,12,20,1,9,7,8,3,5,4,6,2,10),
    (11,19,17,18,13,15,14,16,12,20,1,9,5,7,6,8,3,4,2,10),
)


def validate_permutation(p):
    if any(type(v) is not int for v in p) or sorted(p) != list(range(1, len(p)+1)):
        raise ValueError("expected a permutation of 1,...,n")


def inverse(p):
    validate_permutation(p)
    result = [0]*len(p)
    for position, value in enumerate(p, 1):
        result[value-1] = position
    return tuple(result)


def is_involution(p):
    return inverse(p) == tuple(p)


def alternating(p, *, ascent=True):
    return all((a < b) == (ascent if i % 2 == 0 else not ascent)
               for i, (a, b) in enumerate(zip(p, p[1:])))


def baxter_value(p):
    """Min 2021 p.253, literally every i<j<k<l, strict inequalities.

    ai+1=al and al<aj imply ak>al;
    al+1=ai and ai<ak imply aj>ai.
    No positional adjacency is imposed on this predicate.
    """
    for i, j, k, l in combinations(range(len(p)), 4):
        ai, aj, ak, al = p[i], p[j], p[k], p[l]
        if ai+1 == al and al < aj and not ak > al:
            return False
        if al+1 == ai and ai < ak and not aj > ai:
            return False
    return True


def baxter_vincular(p):
    """Avoid 2-41-3 and 3-14-2: central positions j and j+1 adjacent."""
    n = len(p)
    for j in range(1, n-2):
        middle_left, middle_right = p[j], p[j+1]
        for i in range(j):
            left = p[i]
            for l in range(j+2, n):
                right = p[l]
                if middle_right < left < right < middle_left:
                    return False
                if middle_left < right < left < middle_right:
                    return False
    return True


def classical_separable(p):
    for i, j, k, l in combinations(range(len(p)), 4):
        a, b, c, d = p[i], p[j], p[k], p[l]
        if c < a < d < b or b < d < a < c:
            return False
    return True


def involutions(n):
    """Generate every involution once via the least unassigned position.

    Each step chooses its fixed point or its unique larger transposition partner.
    No alternation, Baxter property, or structural lemma prunes this generator.
    """
    if type(n) is not int or n < 0:
        raise ValueError("n must be a nonnegative integer")
    image = [0]*n
    def visit():
        try:
            i = image.index(0)
        except ValueError:
            yield tuple(image)
            return
        image[i] = i+1
        yield from visit()
        image[i] = 0
        for j in range(i+1, n):
            if not image[j]:
                image[i], image[j] = j+1, i+1
                yield from visit()
                image[i] = image[j] = 0
    yield from visit()


def direct_sum(a, b):
    return tuple(a) + tuple(len(a)+v for v in b)


def skew_sum(a, b):
    return tuple(len(b)+v for v in a) + tuple(b)


@lru_cache(maxsize=None)
def structural_class(m, reverse=False):
    """Unrestricted double-alternating even classes from Min-Park S1/S2.

    This enumeration assumes those published structural lemmas; it is not an
    independent proof of their completeness. It imposes NO involution condition.
    """
    if not m:
        return ((),)
    objects = []
    if reverse:
        for k in range(1, m+1):
            for beta in structural_class(k-1, False):
                initial = skew_sum(skew_sum((1,), beta), (1,))
                for sigma in structural_class(m-k, True):
                    objects.append(direct_sum(initial, sigma))
    else:
        for k in range(m):
            for sigma in structural_class(m-k-1, True):
                initial = direct_sum(direct_sum((1,), sigma), (1,))
                for beta in structural_class(k, False):
                    objects.append(skew_sum(initial, beta))
    require(len(objects) == len(set(objects)), "structural grammar duplicated an object")
    require(len(objects) == comb(2*m, m)//(m+1), "Catalan class total failed")
    return tuple(objects)


def counterexample_evidence():
    records = []
    for p in COUNTEREXAMPLES:
        validate_permutation(p)
        alpha = tuple(v-10 for v in p[:10])
        alpha_partner = p[10:]
        sigma = tuple(v-1 for v in alpha[1:-1])
        properties = {
            "ascent_first_alternating": alternating(p),
            "involution": is_involution(p),
            "baxter_all_quadruples_value_adjacency": baxter_value(p),
            "baxter_positional_vincular": baxter_vincular(p),
            "classical_separable": classical_separable(p),
            "outer_blocks_are_inverse_partners": inverse(alpha) == alpha_partner,
            "first_outer_block_is_not_involution": not is_involution(alpha),
            "sigma_reverse_alternating": alternating(sigma, ascent=False),
            "sigma_inverse_reverse_alternating": alternating(inverse(sigma), ascent=False),
            "sigma_baxter_value": baxter_value(sigma),
            "sigma_baxter_vincular": baxter_vincular(sigma),
            "sigma_is_not_involution": not is_involution(sigma),
        }
        require(all(properties.values()), "counterexample validation failed")
        records.append({"permutation": list(p), "alpha": list(alpha),
                        "alpha_inverse": list(alpha_partner), "sigma": list(sigma),
                        "quadruples_examined_by_literal_predicate": comb(20, 4),
                        "properties": properties})
    require(inverse(tuple(records[0]["sigma"])) == tuple(records[1]["sigma"]),
            "the two sigma blocks are not inverse partners")
    return records


def exhaustive_evidence(expected, permutation_bound=8, involution_bound=12, structural_m=10):
    predicate_checks = []
    for n in range(permutation_bound+1):
        total = accepted = 0
        for p in permutations(range(1, n+1)):
            left, right = baxter_value(p), baxter_vincular(p)
            require(left == right, "Baxter predicate disagreement at " + repr(p))
            total += 1
            accepted += int(left)
        require(total == factorial(n), "permutation generator count failed")
        predicate_checks.append({"n": n, "permutations": total, "baxter": accepted})
    direct_checks = []
    telephone = [1, 1]
    for n in range(2, involution_bound+1):
        telephone.append(telephone[-1] + (n-1)*telephone[-2])
    for n in range(involution_bound+1):
        total = alternate = value_count = vincular_count = 0
        for p in involutions(n):
            total += 1
            if alternating(p):
                alternate += 1
                value_ok, vincular_ok = baxter_value(p), baxter_vincular(p)
                require(value_ok == vincular_ok, "involution predicate mismatch")
                value_count += int(value_ok)
                vincular_count += int(vincular_ok)
        require(total == telephone[n], "involution generator total failed")
        require(value_count == vincular_count == expected[n], "direct count mismatch")
        direct_checks.append({"n": n, "all_involutions": total,
                              "alternating_involutions": alternate,
                              "value_count": value_count, "vincular_count": vincular_count})
    grammar_checks = []
    for m in range(structural_m+1):
        parity_counts = []
        for reverse in (False, True):
            objects = structural_class(m, reverse)
            accepted = []
            for p in objects:
                require(alternating(p, ascent=not reverse), "grammar alternation failed")
                pinv = inverse(p)
                require(alternating(pinv, ascent=not reverse), "grammar inverse alternation failed")
                if p == pinv:
                    require(baxter_value(p) and baxter_vincular(p),
                            "grammar involution failed literal Baxter predicates")
                    accepted.append(p)
            n = 2*m + int(reverse)
            require(len(accepted) == expected[n], "structural filtered count mismatch")
            parity_counts.append(len(accepted))
        grammar_checks.append({"m": m, "unrestricted_B_2m": len(structural_class(m)),
                               "unrestricted_RB_2m": len(structural_class(m, True)),
                               "even_involutions": parity_counts[0],
                               "odd_involutions_via_initial_fixed_point": parity_counts[1]})
    full_twenty = set(structural_class(10)) if structural_m >= 10 else set()
    require(structural_m < 10 or all(p in full_twenty for p in COUNTEREXAMPLES),
            "counterexamples absent from unrestricted grammar")
    return {
        "all_permutations_predicate_comparison": {"inclusive_length_bound": permutation_bound,
                                                    "rows": predicate_checks},
        "all_involutions_without_pruning": {"inclusive_length_bound": involution_bound,
                                             "rows": direct_checks},
        "structural_grammar": {"inclusive_half_length_bound": structural_m,
                               "rows": grammar_checks,
                               "dependency": "Min-Park 2006 unrestricted structural lemmas S1-S3",
                               "baxter_checks": "Both literal predicates on every accepted involution; not every unrestricted grammar object"},
        "scope": "Finite computations check stated bounds only. Direct exhaustive enumeration is independent of structural lemmas through n=12. The length-20 grammar check depends on S1-S3. No asymptotic or all-n theorem is inferred from finite agreement."
    }
