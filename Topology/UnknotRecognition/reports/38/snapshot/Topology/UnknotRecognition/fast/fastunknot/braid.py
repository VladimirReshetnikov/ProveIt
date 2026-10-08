"""Certified braid shortcuts and exact recognition for at most three strands.

For a knot closure, Bennequin's inequality and its mirror imply
``abs(exponent_sum) <= strands - 1`` if the knot is trivial.  Violation is a
linear one-sided obstruction for any strand count.

For three strands the quotient B_3 / centre is C_2 * C_3.  Put
``x = sigma_1 sigma_2 sigma_1`` and ``y = sigma_1 sigma_2``.  A stack computes
the reduced word, then cyclic reduction determines its conjugacy class.  At
exponent sums 2 and -2 the unknot classes have cyclic words y and y^2;
at exponent sum 0 the cyclic word has two x's, one y and one y^2.

An independent matrix backend uses the specialization of reduced Burau at
t=-1: sigma_1 -> [[1,1],[0,1]], sigma_2 -> [[1,0],[-1,1]].  Together with the
Bennequin bound, ``abs(2 - trace(matrix)) == 1`` characterizes the unknot among
three-braid knot closures.  See the accompanying article for proofs, including
the lift from C_2 * C_3 and the small-trace conjugacy classification.

Neither backend computes Khovanov homology, nor supplies a general
quasi-polynomial unknot algorithm.  Inputs are explicit braid words.
"""
from __future__ import annotations

from collections import deque

from .diagram import DiagramError


# 0 means x (order two); 1,2 mean y,y^2 (order three).
_IMAGE = {1: (2, 0), -1: (0, 1), 2: (0, 2), -2: (1, 0)}
_ALPHABET = "XYZ"


def _checked_word(strands, word, check=None):
    """Validate the word and its one-component closure without creating PD."""
    if check is not None:
        check()
    if type(strands) is not int or strands < 1:
        raise DiagramError("strands must be a positive integer")
    try:
        word = tuple(word)
    except TypeError as exc:
        raise DiagramError("braid word must be an iterable of integers") from exc
    if strands > len(word) + 1:
        raise DiagramError("too few crossings for a one-component closure")
    permutation = list(range(strands))
    exponent = 0
    for position, generator in enumerate(word):
        if type(generator) is not int or not 1 <= abs(generator) < strands:
            raise DiagramError("braid generators must satisfy 1 <= |g| < strands")
        if check is not None and position % 1024 == 0:
            check()
        exponent += 1 if generator > 0 else -1
        i = abs(generator) - 1
        permutation[i], permutation[i + 1] = permutation[i + 1], permutation[i]
    current = permutation[0]
    length = 1
    while current != 0:
        current = permutation[current]
        length += 1
    if length != strands:
        raise DiagramError("the braid closure is a link, not a knot")
    return word, exponent


def free_product_normal_form(word, *, check=None):
    """Return a cyclically reduced C2*C3 word and exact operation counters.

    ``word`` must already be a word in +/-1,+/-2.  The returned representative
    is invariant under conjugation only up to cyclic rotation; the decision
    predicates below have that invariance.  No conjugator search is performed.
    """
    stack = []
    maximum = token_operations = 0
    for position, generator in enumerate(word):
        if check is not None and position % 1024 == 0:
            check()
        for token in _IMAGE[generator]:
            token_operations += 1
            if stack and (stack[-1] == 0) == (token == 0):
                previous = stack.pop()
                if token != 0:
                    product = (previous + token) % 3
                    if product:
                        stack.append(product)
            else:
                stack.append(token)
            maximum = max(maximum, len(stack))
    reduced_length = len(stack)
    cyclic = deque(stack)
    conjugations = 0
    while len(cyclic) > 1 and (cyclic[0] == 0) == (cyclic[-1] == 0):
        if check is not None and conjugations % 1024 == 0:
            check()
        first, last = cyclic.popleft(), cyclic.pop()
        conjugations += 1
        if first != 0:
            product = (last + first) % 3
            if product:
                cyclic.append(product)
    return tuple(cyclic), {
        "token_operations": token_operations,
        "cyclic_conjugations": conjugations,
        "max_stack_tokens": maximum,
        "reduced_tokens": reduced_length,
        "cyclic_tokens": len(cyclic),
    }


def burau_at_minus_one(word, *, check=None):
    """Integral 2x2 Burau product, using only additions and subtractions.

    ``word`` must already be a word in +/-1,+/-2.  Multiplication is on the
    right.  At most two integer additions are needed for each input letter.
    The entries have O(len(word)) bits, so this backend uses O(n^2) bit time.
    """
    a, b, c, d = 1, 0, 0, 1
    for position, generator in enumerate(word):
        if check is not None and position % 1024 == 0:
            check()
        if generator == 1:
            b, d = a + b, c + d
        elif generator == -1:
            b, d = b - a, d - c
        elif generator == 2:
            a, c = a - b, c - d
        elif generator == -2:
            a, c = a + b, c + d
        else:
            raise DiagramError("three-braid generators must be +/-1 or +/-2")
    return ((a, b), (c, d))


def braid_certificate(strands, word, *, backend="free-product", use_braid_reduction=True, check=None):
    """Validate an explicit braid word and return an exact decision witness.

    UNKNOT/KNOTTED is a complete decision for one-, two-, and three-braid knot
    closures.  More strands first use the Bennequin obstruction, then optionally
    a checked singleton endpoint destabilization.  Unresolved inputs return
    INCONCLUSIVE.  This raw-word API avoids PD conversion.

    ``check`` is an optional cooperative budget callback, called regularly.
    Matrix witnesses use signed hexadecimal strings to remain JSON-safe even
    when entries exceed Python's decimal integer conversion digit limit.
    """
    if backend not in ("free-product", "matrix"):
        raise ValueError("braid backend must be 'free-product' or 'matrix'")
    word, exponent = _checked_word(strands, word, check)
    result = {
        "status": "INCONCLUSIVE", "method": "braid-bennequin-inconclusive",
        "strands": strands, "input_letters": len(word), "exponent_sum": exponent,
        "bennequin_bound_for_unknot": strands - 1,
    }
    linear_complexity = {
        "domain": "explicit braid word",
        "word_ram_time": "O(n + m)",
        "conservative_bit_time": "O((n + m) log(n + m + 2))",
        "variables": "n=input letters, m=strands",
    }
    if abs(exponent) > strands - 1:
        result.update(status="KNOTTED", method="braid-bennequin", complexity=linear_complexity)
        return result
    if strands <= 2:
        # B1 is trivial.  A knot closure in B2 has odd exponent; the preceding
        # obstruction leaves exactly the two one-crossing unknot classes.
        result.update(status="UNKNOT", method="braid-at-most-two", complexity=linear_complexity)
        return result
    if strands > 3:
        if use_braid_reduction:
            from .braid_reduction import singleton_reduce
            reduced_strands, reduced_word, reduction = singleton_reduce(
                strands, word, check=(lambda: None) if check is None else check)
            result["strand_reduction"] = reduction
            if reduced_strands < strands:
                following = braid_certificate(reduced_strands, reduced_word, backend=backend,
                                              use_braid_reduction=False, check=check)
                result.update(
                    status=following["status"],
                    method="braid-destabilization:" + following["method"],
                    after_reduction=following,
                    complexity={"domain": "explicit m-strand braid of n letters with endpoint descent",
                                "word_ram_time": "O(n*m)",
                                "conservative_bit_time": "O(n*m*log(n + m + 2))"},
                )
                if backend == "matrix":
                    result["complexity"] = {
                        "domain": "explicit m-strand braid of n letters with endpoint descent",
                        "bit_time": "O(n*m*log(n + m + 2) + n^2)",
                    }
        return result
    if backend == "free-product":
        cyclic, stats = free_product_normal_form(word, check=check)
        trivial = ((exponent == 2 and cyclic == (1,))
                   or (exponent == -2 and cyclic == (2,))
                   or (exponent == 0 and len(cyclic) == 4
                       and cyclic.count(0) == 2 and cyclic.count(1) == cyclic.count(2) == 1))
        result.update(
            status="UNKNOT" if trivial else "KNOTTED", method="three-braid-free-product",
            quotient="B3/centre = <X,Y | X^2=Y^3=1>; Z=Y^2",
            cyclic_word="".join(_ALPHABET[token] for token in cyclic),
            free_product_stats=stats, complexity=linear_complexity,
        )
    else:
        matrix = burau_at_minus_one(word, check=check)
        trace = matrix[0][0] + matrix[1][1]
        determinant = abs(2 - trace)
        result.update(
            status="UNKNOT" if determinant == 1 else "KNOTTED", method="three-braid-matrix",
            matrix_hex=[[hex(entry) for entry in row] for row in matrix],
            trace_hex=hex(trace), knot_determinant_hex=hex(determinant),
            max_entry_bits=max(abs(entry).bit_length() for row in matrix for entry in row),
            complexity={"domain": "explicit three-braid word of n letters",
                        "bit_time": "O(n^2)", "bit_space": "O(n)"},
        )
    return result
