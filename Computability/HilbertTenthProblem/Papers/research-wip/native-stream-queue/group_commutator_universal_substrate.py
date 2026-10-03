#!/usr/bin/env python3
"""Finite exact audits for the group-commutator universal-substrate theorem.

This does not implement Higman's embedding algorithm, produce a universal
finite presentation, or encode variable-length subgroup products arithmetically.
Free words are tuples of signed, nonzero generator indices.  Every assertion
uses exact integers, free reduction, or an independent finite quotient oracle.
"""
import argparse
from itertools import combinations, product
import json
from pathlib import Path
import random


EMPTY = ()
A, B = (1,), (2,)


def reduce_word(word):
    result = []
    for letter in word:
        assert isinstance(letter, int) and letter
        if result and result[-1] == -letter:
            result.pop()
        else:
            result.append(letter)
    return tuple(result)


def inverse(word):
    return tuple(-letter for letter in reversed(word))


def multiply(*words):
    return reduce_word(letter for word in words for letter in word)


def power(word, exponent):
    return multiply(*(word if exponent >= 0 else inverse(word)
                      for _ in range(abs(exponent))))


def conjugate(word, by):
    return multiply(by, word, inverse(by))


def commutator(left, right):
    """[g,h] = g h g^-1 h^-1, throughout this packet."""
    return multiply(left, right, inverse(left), inverse(right))


def shifted_a(index):
    return conjugate(A, power(B, -index))


def defining_relator(index):
    assert index > 0
    return commutator(shifted_a(index), A)


def reduced_words(rank, maximum_length):
    result, current = [EMPTY], [EMPTY]
    alphabet = tuple(range(1, rank+1))+tuple(range(-rank, 0))
    for _ in range(maximum_length):
        current = [word+(letter,) for word in current for letter in alphabet
                   if not word or word[-1] != -letter]
        result.extend(current)
    return result


def free_graph_reduce(word):
    """Free vertex words only: no graph commutations are silently applied."""
    result = []
    for index, sign in word:
        assert sign in (-1, 1)
        if result and result[-1] == (index, -sign):
            result.pop()
        else:
            result.append((index, sign))
    return tuple(result)


def semidirect_coordinates(word):
    """Write a free a,b word as (vertex word) b^exponent.

    With a_i=b^-i a b^i, b^m a b^-m=a_-m.  Graph relators can be
    imposed afterwards; this coordinate audit itself needs no word oracle.
    """
    vertices, exponent = [], 0
    for letter in word:
        assert abs(letter) in (1, 2)
        if abs(letter) == 2:
            exponent += 1 if letter > 0 else -1
        else:
            vertices.append((-exponent, letter))
    return free_graph_reduce(vertices), exponent


def expand_coordinates(vertices, exponent):
    return multiply(*(power(shifted_a(index), sign) for index, sign in vertices),
                    power(B, exponent))


def presentation_checks():
    edges = diagonals = roundtrips = shifts = 0
    for i, j in product(range(-9, 10), repeat=2):
        actual = commutator(shifted_a(i), shifted_a(j))
        if i == j:
            assert actual == EMPTY
            diagonals += 1
        else:
            base = power(defining_relator(abs(i-j)), 1 if i > j else -1)
            assert actual == conjugate(base, power(B, -min(i, j)))
            edges += 1
        for shift in range(-3, 4):
            assert conjugate(shifted_a(i), power(B, -shift)) == shifted_a(i+shift)
            shifts += 1
    rng = random.Random(206031)
    for word in reduced_words(2, 5):
        assert expand_coordinates(*semidirect_coordinates(word)) == word
        roundtrips += 1
    for _ in range(512):
        vertices = free_graph_reduce((rng.randrange(-12, 13), rng.choice((-1, 1)))
                                     for _ in range(rng.randrange(25)))
        exponent = rng.randrange(-12, 13)
        assert semidirect_coordinates(expand_coordinates(vertices, exponent)) == (vertices, exponent)
        roundtrips += 1
    assert commutator(shifted_a(0), A) == EMPTY
    return dict(signed_edge_free_identities=edges, diagonal_identities=diagonals,
                shift_identities=shifts, free_semidirect_coordinate_roundtrips=roundtrips,
                orientation='a_i=b^-i a b^i; b^-1 a_i b=a_(i+1)',
                scope='Free identities and substitutions, not an algorithm for arbitrary graph-group equality.')


def graph_retraction_checks():
    fixtures = missing_pairs = checked_relations = translations = 0
    vertices = tuple(range(-3, 9))
    for mask in range(1 << 5):
        distances = {i+1 for i in range(5) if mask & (1 << i)}
        graph_edges = [(i, j) for i, j in combinations(vertices, 2) if j-i in distances]
        for i, j in combinations(vertices, 2):
            for shift in range(-3, 4):
                assert (abs(i-j) in distances) == (abs((i+shift)-(j+shift)) in distances)
                translations += 1
            if j-i in distances:
                continue
            images = {vertex: A if vertex == i else B if vertex == j else EMPTY
                      for vertex in vertices}
            for u, v in graph_edges:
                assert commutator(images[u], images[v]) == EMPTY
                checked_relations += 1
            assert len(commutator(images[i], images[j])) == 4
            missing_pairs += 1
        fixtures += 1
    return dict(finite_distance_set_fixtures=fixtures, missing_edge_retractions=missing_pairs,
                defining_relations_checked_under_retractions=checked_relations,
                translated_edge_predicates=translations,
                scope='Retraction is on the graph-group kernel, not on its semidirect product. '
                      'Finite fixtures illustrate the general proof; no r.e. membership is numerically decided.')


def substitute(word, images):
    return multiply(*(power(images[abs(letter)], 1 if letter > 0 else -1) for letter in word))


def tietze_checks():
    rng = random.Random(206032)
    cases = definitions = 0
    choices = reduced_words(3, 3)
    for _ in range(128):
        image_a, image_b = rng.choice(choices), rng.choice(choices)
        images = {1: (1,), 2: (2,), 3: (3,), 4: image_a, 5: image_b}
        for named, target in ((4, image_a), (5, image_b)):
            assert substitute(multiply((named,), inverse(target)), images) == EMPTY
            definitions += 1
        for x in (0, 1, 2, 7):
            named = commutator(conjugate((4,), power((5,), -x)), (4,))
            expected = commutator(conjugate(image_a, power(image_b, -x)), image_a)
            assert substitute(named, images) == expected
            cases += 1
    return dict(named_generator_definition_substitutions=definitions,
                input_word_substitutions=cases,
                scope='Only the Tietze word substitutions are tested. Injectivity of the supplied '
                      'image words comes from the external effective Higman embedding theorem.')


def fibre_generators(rank, relators):
    return tuple(((i,), (i,)) for i in range(1, rank+1))+tuple((EMPTY, r) for r in relators)


def evaluate_pair_word(word, generators):
    left, right = EMPTY, EMPTY
    for letter in word:
        first, second = generators[abs(letter)-1]
        if letter < 0:
            first, second = inverse(first), inverse(second)
        left, right = multiply(left, first), multiply(right, second)
    return left, right


def normal_product(factors, relators):
    return multiply(*(conjugate(power(relators[index], sign), by)
                      for by, index, sign in factors))


def normal_witness(factors, rank):
    """A word in diagonal and (1,R_j) generators evaluating to (1,N)."""
    return multiply(*(multiply(by, (sign*(rank+index+1),), inverse(by))
                      for by, index, sign in factors))


def pair_witness(left, factors, rank):
    return multiply(left, normal_witness(factors, rank))


def abelian_oracle(word):
    return tuple(sum(1 if letter == i else -1 if letter == -i else 0 for letter in word)
                 for i in (1, 2))


def swap_table():
    """Independently find exact conjugates for all four signed adjacent swaps."""
    relator, result = commutator(A, B), {}
    for bsign, asign in product((-1, 1), repeat=2):
        correction = commutator((2*bsign,), (asign,))
        options = [(by, sign) for by in reduced_words(2, 2) for sign in (-1, 1)
                   if conjugate(power(relator, sign), by) == correction]
        assert options
        result[bsign, asign] = options[0]
    return result


def abelian_derivation(word, swaps):
    """Bubble-sort to a^p b^q, recording every relator application."""
    current, factors = reduce_word(word), []
    while True:
        position = next((i for i in range(len(current)-1)
                         if abs(current[i]) == 2 and abs(current[i+1]) == 1), None)
        if position is None:
            break
        first, second = current[position:position+2]
        local, sign = swaps[first//2, second]
        factors.append((multiply(current[:position], local), 0, sign))
        current = multiply(current[:position], (second, first), current[position+2:])
    assert current == multiply(power(A, abelian_oracle(word)[0]), power(B, abelian_oracle(word)[1]))
    return factors, current


def cyclic_oracle(word, modulus):
    return abelian_oracle(word)[0] % modulus


def cyclic_derivation(word, modulus):
    """For <a,b | a^m,b>, collect b conjugates, then powers of a^m."""
    exponent, factors = 0, []
    for letter in word:
        if abs(letter) == 1:
            exponent += letter
        else:
            factors.append((power(A, exponent), 1, letter//2))
    assert exponent % modulus == 0
    quotient = exponent//modulus
    factors += [(EMPTY, 0, 1 if quotient > 0 else -1)]*abs(quotient)
    return factors


def fibre_product_checks():
    rng = random.Random(206033)
    random_derivations = abelian_pairs = cyclic_pairs = negative_pairs = inverse_witnesses = 0
    choices, swaps = reduced_words(2, 3), swap_table()
    relator_sets = ((commutator(A, B),), (power(A, 2), B), (power(A, 3), power(B, 2)))
    for relators in relator_sets:
        generators = fibre_generators(2, relators)
        for _ in range(256):
            factors = [(rng.choice(choices), rng.randrange(len(relators)), rng.choice((-1, 1)))
                       for _ in range(rng.randrange(9))]
            normal = normal_product(factors, relators)
            left = rng.choice(choices)
            assert evaluate_pair_word(normal_witness(factors, 2), generators) == (EMPTY, normal)
            assert evaluate_pair_word(pair_witness(left, factors, 2), generators) == (left, multiply(left, normal))
            # The target (N,1), including explicit inverse subgroup generators.
            witness = multiply(normal, inverse(normal_witness(factors, 2)))
            assert evaluate_pair_word(witness, generators) == (normal, EMPTY)
            inverse_witnesses += sum(letter < 0 for letter in witness)
            random_derivations += 1
    relators = (commutator(A, B),)
    generators = fibre_generators(2, relators)
    for left, right in product(choices, repeat=2):
        if abelian_oracle(left) != abelian_oracle(right):
            negative_pairs += 1
            continue
        factors, remainder = abelian_derivation(multiply(inverse(left), right), swaps)
        assert remainder == EMPTY
        assert normal_product(factors, relators) == multiply(inverse(left), right)
        assert evaluate_pair_word(pair_witness(left, factors, 2), generators) == (left, right)
        abelian_pairs += 1
    for modulus in (2, 3, 5):
        relators = (power(A, modulus), B)
        generators = fibre_generators(2, relators)
        for left, right in product(choices, repeat=2):
            if cyclic_oracle(left, modulus) != cyclic_oracle(right, modulus):
                negative_pairs += 1
                continue
            normal = multiply(inverse(left), right)
            factors = cyclic_derivation(normal, modulus)
            assert normal_product(factors, relators) == normal
            assert evaluate_pair_word(pair_witness(left, factors, 2), generators) == (left, right)
            cyclic_pairs += 1
    assert inverse_witnesses > 0
    return dict(random_normal_closure_derivations=random_derivations,
                abelian_quotient_constructive_pairs=abelian_pairs,
                finite_cyclic_quotient_constructive_pairs=cyclic_pairs,
                quotient_separated_nonmembers=negative_pairs,
                negative_generator_occurrences=inverse_witnesses,
                scope='Constructive exact words in finitely many subgroup generators and their inverses. '
                      'Z^2 and cyclic presentations are independent toy quotient oracles, not universal examples.')


def permutation_multiply(left, right):
    return tuple(left[right[i]] for i in range(3))


def permutation_inverse(value):
    return tuple(value.index(i) for i in range(3))


def s3_oracle(word):
    images = {1: (1, 0, 2), 2: (1, 2, 0)}
    result = (0, 1, 2)
    for letter in word:
        value = images[abs(letter)]
        result = permutation_multiply(result, value if letter > 0 else permutation_inverse(value))
    return result


def erase_cyclic_blocks(word, modulus):
    """Record deletions of b^m and b^-m; caller checks the final remainder."""
    current, factors = reduce_word(word), []
    while True:
        found = next(((i, sign) for i in range(len(current)-modulus+1) for sign in (-1, 1)
                      if current[i:i+modulus] == (2*sign,)*modulus), None)
        if found is None:
            break
        position, sign = found
        factors.append((current[:position], 1, sign))
        current = multiply(current[:position], current[position+modulus:])
    return factors, current


def conjugated_fibre_checks():
    # S3=<a,b | a^2,b^3,(ab)^2>.  The independent permutation oracle
    # distinguishes x mod3: a and b^-x a b^x commute exactly for 3|x.
    relators = (power(A, 2), power(B, 3), power(multiply(A, B), 2))
    assert all(s3_oracle(word) == (0, 1, 2) for word in relators)
    generators = fibre_generators(2, relators)
    conjugated = tuple((conjugate(left, A), right) for left, right in generators)
    rng = random.Random(206034)
    transported = positives = negatives = 0
    for _ in range(512):
        word = tuple(rng.choice((-1, 1))*rng.randrange(1, len(generators)+1)
                     for _ in range(rng.randrange(21)))
        left, right = evaluate_pair_word(word, generators)
        image_left, image_right = evaluate_pair_word(word, conjugated)
        assert (image_left, image_right) == (conjugate(left, A), right)
        assert s3_oracle(left) == s3_oracle(right)
        assert s3_oracle(conjugate(image_left, inverse(A))) == s3_oracle(image_right)
        transported += 1
    for x in range(1, 97):
        target = shifted_a(x)
        left, right = conjugate(target, inverse(A)), target
        belongs = s3_oracle(left) == s3_oracle(right)
        assert belongs == (s3_oracle(commutator(target, A)) == (0, 1, 2)) == (x % 3 == 0)
        if belongs:
            normal = multiply(inverse(left), right)
            factors, remainder = erase_cyclic_blocks(normal, 3)
            assert remainder == EMPTY and normal_product(factors, relators) == normal
            witness = pair_witness(left, factors, 2)
            assert evaluate_pair_word(witness, generators) == (left, right)
            assert evaluate_pair_word(witness, conjugated) == (target, target)
            positives += 1
        else:
            negatives += 1
    return dict(arbitrary_signed_generator_word_transports=transported,
                diagonal_target_positive_witnesses=positives,
                diagonal_target_quotient_separated_nonmembers=negatives,
                positive_input_range=[1, 96], toy_language='positive multiples of 3',
                scope='Fixed conjugated subgroup, target (b^-x a b^x,b^-x a b^x). '
                      'Finite S3 quotient is illustrative; general equivalence is a theorem in the note.')


SOURCES = (
    dict(url='https://arxiv.org/abs/1908.10153', section='Theorem 1.1',
         audited_claim='Higman embedding: finitely generated recursively presented groups '
                       'embed in finitely presented groups; relators may be recursively enumerable.'),
    dict(url='https://arxiv.org/abs/2507.04347', section='Algorithm 1.1; Section 2.1; version 8',
         audited_claim='An explicit finite presentation and embedding generator-image words '
                       'are algorithmically obtainable from an effectively enumerable presentation. '
                       'The general route is used, without the optional shorter-route hypotheses.'),
    dict(url='https://arxiv.org/abs/0810.0690', section='Section 1, introductory fibre-product definition',
         audited_claim='For a finite presentation, the Mihailova subgroup is generated by diagonal '
                       'basis pairs and (1,relator) pairs. Later concise/Peiffer-aspherical hypotheses '
                       'concern a different recursive-presentation theorem and are not needed here.'),
)


def verify():
    return dict(status='PASS_GROUP_COMMUTATOR_UNIVERSAL_SUBSTRATE',
                presentation=presentation_checks(), graph_retractions=graph_retraction_checks(),
                named_tietze_extension=tietze_checks(), fibre_products=fibre_product_checks(),
                conjugated_diagonal_target=conjugated_fibre_checks(),
                primary_sources=SOURCES,
                source_audit_boundary='The cited primary texts were read during mathematical review. '
                                      'This executable stores that provenance; it does not reprove or execute Higman embedding.',
                effectivity='An enumerator for positive S enumerates relators [b^-n a b^n,a]. '
                            'Effective embedding yields finite H and named-generator image words; '
                            'two Tietze definitions preserve these names without changing H.',
                limits='No concrete universal finite presentation or numerical universal subgroup generator list '
                       'is constructed here. No fixed-size arithmetic certificate for variable-length products '
                       'is supplied. Free-word length, embedding size, product selection and product-history '
                       'encoding remain outside this checker; no complete Diophantine bound improves.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n')
    else:
        assert json.loads(receipt.read_text()) == result, 'receipt mismatch'
    print(result['status'])
    print('Exact graph/presentation identities, constructive fibre-product words, and conjugated diagonal targets pass.')
