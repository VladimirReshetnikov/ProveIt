"""Structural certificates directly from explicit or run-encoded braids.

This specializes the existing Seifert/Rasmussen criteria to the path
multigraph of a braid.  It avoids planar-diagram expansion for binary run
exponents.  The optional signature experiment below is rigorously dominated
by this Rasmussen interval, so it is not used in recognition.
"""
from __future__ import annotations


def _counts(strands, runs, check=None):
    if type(strands) is not int or strands < 1:
        raise ValueError('strands must be a positive integer')
    counts = {}
    permutation = {}
    crossings = exponent = 0
    for position, item in enumerate(runs):
        if check is not None and position % 1024 == 0:
            check()
        try:
            generator, power = item
        except (TypeError, ValueError) as exc:
            raise ValueError('runs must be pairs (generator, exponent)') from exc
        if (type(generator) is not int or type(power) is not int
                or not 1 <= generator < strands or power == 0):
            raise ValueError('invalid generator or zero/noninteger exponent')
        pair = counts.setdefault(generator, [0, 0])
        pair[0 if power > 0 else 1] += abs(power)
        crossings += abs(power)
        exponent += power
        if power & 1:
            i = generator - 1
            permutation[i], permutation[i + 1] = (
                permutation.get(i + 1, i + 1), permutation.get(i, i))
    if len(counts) != strands - 1:
        raise ValueError('the braid closure is not a knot: unused strand separator')
    seen = set()
    components = strands - len(permutation)
    for start in permutation:
        if start in seen:
            continue
        components += 1
        current = start
        while current not in seen:
            seen.add(current)
            current = permutation[current]
    if components != 1:
        raise ValueError('the braid closure is a link, not a knot')
    if check is not None:
        check()
    return counts, crossings, exponent


def _pack(weights, check=None):
    """Maximum-weight independent set of the generator-index path."""
    best = [0] * (len(weights) + 1)
    take = [False] * len(weights)
    for index, weight in enumerate(weights):
        if check is not None and index % 1024 == 0:
            check()
        used = weight + (best[index - 1] if index else 0)
        if used > best[index]:
            best[index + 1] = used
            take[index] = True
        else:
            best[index + 1] = best[index]
    chosen = []
    index = len(weights) - 1
    while index >= 0:
        if take[index]:
            chosen.append(index + 1)
            index -= 2
        else:
            index -= 1
    return best[-1], tuple(reversed(chosen))


def structural_runs_certificate(strands, runs, *, check=None):
    """Apply established structural criteria without expanding signed runs.

    Each run is a pair (positive generator index, nonzero signed exponent).
    The original permutation is checked. INCONCLUSIVE is not a knot verdict.
    """
    counts, n, exponent = _counts(strands, runs, check)
    positive_support = sum(pair[0] != 0 for pair in counts.values())
    negative_support = sum(pair[1] != 0 for pair in counts.values())
    mixed = sum(bool(pair[0] and pair[1]) for pair in counts.values())
    twice_genus = n - strands + 1
    artin_lower = exponent + strands - 2 * positive_support - 1
    artin_upper = exponent - strands + 2 * negative_support + 1
    # The production PD Seifert evaluator assigns a negative crossing sign
    # to Diagram.from_braid's positive Artin generator. Match those existing
    # output fields; retain the explicit Artin convention separately.
    lower, upper = -artin_upper, -artin_lower
    if twice_genus < 0 or twice_genus % 2 or upper - lower != 2 * mixed:
        raise ArithmeticError('inconsistent one-component braid profile')
    if twice_genus == 0:
        status, criterion = 'UNKNOT', 'seifert-genus-zero'
    elif mixed == 0:
        status, criterion = 'KNOTTED', 'homogeneous-seifert-genus'
    elif lower > 0 or upper < 0:
        status, criterion = 'KNOTTED', 'rasmussen-interval'
    else:
        status, criterion = 'INCONCLUSIVE', 'structural-braid-inconclusive'
    return {
        'schema': 'source-braid-structural-v1', 'status': status,
        'criterion': criterion, 'strands': strands, 'crossings': n,
        'writhe': -exponent, 'seifert_circles': strands,
        'positive_components': strands - negative_support,
        'negative_components': strands - positive_support,
        'homogeneity_defect': mixed, 'canonical_genus': twice_genus // 2,
        'rasmussen_interval': [lower, upper],
        'artin_exponent_sum': exponent,
        'artin_rasmussen_interval': [artin_lower, artin_upper],
        'source': 'original checked braid',
    }


def structural_word_certificate(strands, word, *, check=None):
    def runs():
        for letter in word:
            if type(letter) is not int or letter == 0:
                raise ValueError('braid letters must be nonzero integers')
            yield abs(letter), 1 if letter > 0 else -1
    return structural_runs_certificate(strands, runs(), check=check)


def verify_structural_runs_certificate(strands, runs, certificate):
    """Replay the exact source calculation; this is not a theorem prover."""
    try:
        return certificate == structural_runs_certificate(strands, runs)
    except (TypeError, ValueError, ArithmeticError):
        return False


def signature_runs_certificate(strands, runs, *, check=None):
    """One-sided signature certificate from integer run pairs, without expansion.

    The input must have a one-component closure.  Invalid input raises
    ValueError.  ``INCONCLUSIVE`` means that this particular subform bound
    does not exclude zero signature, never that the knot is trivial.
    """
    counts, crossings, exponent = _counts(strands, runs, check)
    choices = []
    for column, sign in enumerate((1, -1)):
        weights = [max(0, counts[i][column] - 1) for i in range(1, strands)]
        score, selected = _pack(weights, check)
        choices.append((score, sign, column, selected))
    score, sign, column, selected = max(choices, key=lambda value: value[0])
    form_dimension = crossings - strands + 1
    bound = max(0, 2 * score - form_dimension)
    return {
        'schema': 'seifert-definite-subform-v1',
        'status': 'KNOTTED' if bound else 'INCONCLUSIVE',
        'method': 'braid-signature-subform',
        'strands': strands, 'crossings': crossings, 'exponent_sum': exponent,
        'seifert_form_dimension': form_dimension,
        'sign': sign,
        'selected_generators': [
            {'generator': i, 'occurrences': counts[i][column]}
            for i in selected
        ],
        'definite_subspace_dimension': score,
        'signature_abs_lower_bound': bound,
        'positive_packing_weight': choices[0][0],
        'negative_packing_weight': choices[1][0],
    }


def signature_certificate(strands, word, *, check=None):
    """The same certificate from an explicit signed Artin word."""
    def runs():
        for letter in word:
            if type(letter) is not int or letter == 0:
                raise ValueError('braid letters must be nonzero integers')
            yield abs(letter), 1 if letter > 0 else -1
    return signature_runs_certificate(strands, runs(), check=check)


def verify_signature_runs_certificate(strands, runs, certificate):
    """Recheck a positive witness without running the optimization algorithm.

    Optimality is unnecessary for soundness.  This verifier recomputes input
    counts and the original permutation, checks disjoint strand pairs and
    retained multiplicities, and checks the strict inertia inequality.
    """
    try:
        counts, n, exponent = _counts(strands, runs)
        if not isinstance(certificate, dict):
            return False
        if certificate.get('schema') != 'seifert-definite-subform-v1':
            return False
        if certificate.get('status') != 'KNOTTED':
            return False
        sign = certificate['sign']
        if type(sign) is not int or sign not in (-1, 1):
            return False
        column = 0 if sign > 0 else 1
        selected = certificate['selected_generators']
        if not isinstance(selected, list):
            return False
        score = 0
        previous = -1
        for item in selected:
            index, occurrence = item['generator'], item['occurrences']
            if (type(index) is not int or type(occurrence) is not int
                    or not 1 <= index < strands or index <= previous + 1
                    or occurrence < 2 or counts[index][column] != occurrence):
                return False
            previous = index
            score += occurrence - 1
        d = n - strands + 1
        expected = {
            'method': 'braid-signature-subform', 'strands': strands,
            'crossings': n, 'exponent_sum': exponent,
            'seifert_form_dimension': d,
            'definite_subspace_dimension': score,
            'signature_abs_lower_bound': 2 * score - d,
        }
        return 2 * score > d and all(certificate.get(k) == v for k, v in expected.items())
    except (KeyError, TypeError, ValueError, OverflowError):
        return False


def verify_signature_certificate(strands, word, certificate):
    try:
        word = tuple(word)
        if any(type(letter) is not int or letter == 0 for letter in word):
            return False
        return verify_signature_runs_certificate(
            strands, [(abs(x), 1 if x > 0 else -1) for x in word], certificate)
    except (TypeError, ValueError):
        return False
