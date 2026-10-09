"""Independent verifier: no import from the optimizer or its persistent trie.

Local B3 equality is checked by a central normal form in <x,y | x^2=y^3>,
not by the optimizer's quotient-node/exponent keys. The verifier checks only
soundness of the replacements, not search optimality or saturation claims.
"""
from __future__ import annotations
from collections.abc import Callable, Iterable
from .common import validate_word, input_digest


def b3_central_form(word: Iterable[int]) -> tuple[int, tuple[tuple[int, int], ...]]:
    """Return (central_power, alternating_factors) for a word in +/-1,+/-2.

    Factors (0,1) and (1,j) mean x and y^j respectively. Every Artin letter
    is expanded as z^{-1} times two positive factors, z=x^2=y^3.
    """
    central = 0
    factors: list[tuple[int, int]] = []
    for g in word:
        if g == 1:
            expansion = ((1, 2), (0, 1))
        elif g == -1:
            expansion = ((0, 1), (1, 1))
        elif g == 2:
            expansion = ((0, 1), (1, 2))
        elif g == -2:
            expansion = ((1, 1), (0, 1))
        else:
            raise ValueError('B3 letters must be +/-1 or +/-2')
        central -= 1
        for family, power in expansion:
            if factors and factors[-1][0] == family:
                power += factors.pop()[1]
                carry, power = divmod(power, 2 if family == 0 else 3)
                central += carry
            if power:
                factors.append((family, power))
    return central, tuple(factors)


def local_equal(source: Iterable[int], target: int = 0) -> bool:
    """Check equality to an empty word or one letter in a rank-two parabolic.

    Inputs here are already validated signed Artin letters in the ambient
    group. A false result makes no claim about equality in higher-rank groups.
    """
    source = tuple(source)
    if type(target) is not int:
        return False
    support = sorted({abs(g) for g in source})
    if not support:
        return target == 0
    if len(support) > 2 or (target and abs(target) not in support):
        return False
    expected = 0 if target == 0 else (1 if target > 0 else -1)
    if len(support) == 1:
        return sum(1 if g > 0 else -1 for g in source) == expected
    if support[1] > support[0] + 1:
        first = sum(1 if g > 0 else -1 for g in source if abs(g) == support[0])
        second = sum(1 if g > 0 else -1 for g in source if abs(g) == support[1])
        return (first, second) == ((expected, 0) if target and abs(target) == support[0]
                                  else (0, expected))
    local = [((1 if abs(g) == support[0] else 2) * (1 if g > 0 else -1))
             for g in source]
    if target:
        local.append(-((1 if abs(target) == support[0] else 2) * expected))
    return b3_central_form(local) == (0, ())


def verify(strands: int, word: Iterable[int], certificate: dict, *,
           check: Callable[[], None] | None = None) -> tuple[tuple[int, ...], dict[str, int]]:
    """Replay a certificate using a linked list with stable/fresh node IDs.

    Each successful rule strictly shortens the live word. A radius-one
    certificate removes at most 3n/2 nodes in total, including fresh nodes.
    Thus verification takes O(n) word operations and O(n log(n+s)) bit time.
    Invalid certificates raise ValueError; budget callback exceptions propagate.
    """
    word = validate_word(strands, word)
    check = (lambda: None) if check is None else check
    check()
    if not isinstance(certificate, dict) or certificate.get('kind') != 'rank-two-braid-shortening-v1':
        raise ValueError('unknown certificate kind')
    n = len(word)
    if certificate.get('strands') != strands or certificate.get('input_length') != n:
        raise ValueError('certificate input dimensions differ')
    if certificate.get('input_sha256') != input_digest(strands, word):
        raise ValueError('certificate is for a different input word')
    radius = certificate.get('radius')
    if type(radius) is not int or radius not in (0, 1):
        raise ValueError('invalid certificate radius')
    steps = certificate.get('steps')
    if not isinstance(steps, list) or len(steps) > n // 2:
        raise ValueError('invalid or excessively long replacement transcript')
    values = list(word)
    previous = [i - 1 for i in range(n)]
    following = [i + 1 for i in range(n)]
    if n:
        following[-1] = -1
    alive = [True] * n
    head = 0 if n else -1
    removed = introduced = 0
    for step_number, step in enumerate(steps):
        if step_number & 255 == 0:
            check()
        if not isinstance(step, dict):
            raise ValueError('replacement step must be a dictionary')
        first, last, target = (step.get(k) for k in ('first', 'last', 'target'))
        if any(type(k) is not int for k in (first, last, target)):
            raise ValueError('step IDs and target must be integers')
        if not (0 <= first < len(values) and 0 <= last < len(values)
                and alive[first] and alive[last]):
            raise ValueError('replacement endpoint is not a live node')
        if target and (radius == 0 or not 1 <= abs(target) < strands):
            raise ValueError('replacement target is not allowed')
        block_ids: list[int] = []
        node = first
        while node != -1:
            block_ids.append(node)
            if node == last:
                break
            node = following[node]
        if node == -1:
            raise ValueError('replacement endpoints are reversed or disconnected')
        if len(block_ids) <= int(target != 0):
            raise ValueError('replacement does not strictly shorten')
        source = tuple(values[i] for i in block_ids)
        if not local_equal(source, target):
            raise ValueError('claimed local braid equality is false')
        # The parity assertion is an extra guard, not an assumption of correctness.
        if (len(block_ids) - int(target != 0)) % 2:
            raise ValueError('impossible parity in a braid equality')
        left, right = previous[first], following[last]
        if target:
            fresh = len(values)
            values.append(target)
            previous.append(left)
            following.append(right)
            alive.append(True)
            if left == -1:
                head = fresh
            else:
                following[left] = fresh
            if right != -1:
                previous[right] = fresh
            introduced += 1
        else:
            if left == -1:
                head = right
            else:
                following[left] = right
            if right != -1:
                previous[right] = left
        for old in block_ids:
            alive[old] = False
        removed += len(block_ids)
    output: list[int] = []
    node = head
    while node != -1:
        output.append(values[node])
        node = following[node]
    claimed = certificate.get('output_word')
    if not isinstance(claimed, list) or any(type(g) is not int for g in claimed) or claimed != output:
        raise ValueError('claimed output is not the replay result')
    if removed > n + introduced or introduced > n // 2:
        raise ValueError('replacement accounting failed')
    return tuple(output), {'input_nodes': n, 'removed_nodes': removed,
                           'introduced_nodes': introduced, 'output_nodes': len(output),
                           'verified_steps': len(steps)}
