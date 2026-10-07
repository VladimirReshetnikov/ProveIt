"""Checked elementary Markov descent to at most three strands.

This recognizes a sufficient condition for destabilization, not a complete
braid-index algorithm.  In particular it need not reduce Morton's four-braid
unknot.  Every successful step has a compact replayable certificate.
"""
from __future__ import annotations

from collections import deque


def _validate(strands, word):
    if type(strands) is not int or strands < 1:
        raise ValueError("strands must be a positive integer")
    word = tuple(word)
    if any(type(g) is not int or not 1 <= abs(g) < strands for g in word):
        raise ValueError("invalid Artin generator")
    return word


def _free_cyclic(word, check):
    stack = []
    for index, generator in enumerate(word):
        if index & 255 == 0:
            check()
        if stack and stack[-1] == -generator:
            stack.pop()
        else:
            stack.append(generator)
    ends = deque(stack)
    while len(ends) > 1 and ends[0] == -ends[-1]:
        ends.popleft()
        ends.pop()
        if len(ends) & 255 == 0:
            check()
    return tuple(ends)


def _delete_endpoint(strands, word, side, position):
    endpoint = strands - 1 if side == "right" else 1
    if side not in ("left", "right") or not 0 <= position < len(word):
        raise ValueError("invalid endpoint step")
    if abs(word[position]) != endpoint:
        raise ValueError("step points to the wrong generator")
    if sum(abs(g) == endpoint for g in word) != 1:
        raise ValueError("endpoint generator is not a singleton")
    # Cyclically rotate u sigma v into v u sigma, then destabilize.
    remaining = word[position + 1:] + word[:position]
    if side == "left":
        remaining = tuple(g - 1 if g > 0 else g + 1 for g in remaining)
    return remaining


def singleton_reduce(strands, word, check=lambda: None):
    """Return (strands, word, certificate), stopping once strands <= 3.

    At most max(original_strands-3, 0) endpoint steps are made.  With L input letters
    the straightforward algorithm uses O(L*strands) word operations.  It
    neither increases the word length nor changes the isotopy class of its
    closure.  A failed search makes no claim about minimal braid index.
    """
    word = _validate(strands, word)
    original_strands, original_length = strands, len(word)
    steps = []
    while True:
        check()
        word = _free_cyclic(word, check)
        if strands <= 3:
            break
        right = [i for i, g in enumerate(word) if abs(g) == strands - 1]
        left = [i for i, g in enumerate(word) if abs(g) == 1]
        if len(right) == 1:
            side, position = "right", right[0]
        elif len(left) == 1:
            side, position = "left", left[0]
        else:
            break
        steps.append({"strands": strands, "length": len(word), "side": side,
                      "position": position, "generator": word[position]})
        word = _delete_endpoint(strands, word, side, position)
        strands -= 1
    certificate = {"kind": "singleton-markov-descent-v1",
                   "input_strands": original_strands, "input_length": original_length,
                   "steps": steps, "final_strands": strands, "final_word": list(word)}
    return strands, word, certificate


def verify_singleton_reduction(strands, word, certificate, check=lambda: None):
    """Replay supplied choices; raise ValueError if any claimed move is invalid.

    The verifier does not search for a reducible endpoint and does not trust
    an asserted final braid.  An empty or prematurely stopped certificate is
    legal: it proves exactly the reductions it contains, never completeness.
    """
    word = _validate(strands, word)
    if not isinstance(certificate, dict):
        raise ValueError("certificate must be a dictionary")
    if certificate.get("kind") != "singleton-markov-descent-v1":
        raise ValueError("unknown reduction certificate")
    if (certificate.get("input_strands") != strands or
            certificate.get("input_length") != len(word)):
        raise ValueError("certificate is for a different input size")
    steps = certificate.get("steps")
    if not isinstance(steps, list):
        raise ValueError("missing reduction steps")
    for step in steps:
        check()
        if not isinstance(step, dict):
            raise ValueError("reduction step must be a dictionary")
        word = _free_cyclic(word, check)
        if strands <= 3 or step.get("strands") != strands or step.get("length") != len(word):
            raise ValueError("invalid intermediate braid size")
        position = step.get("position")
        if type(position) is not int or not 0 <= position < len(word):
            raise ValueError("invalid generator position")
        if step.get("generator") != word[position]:
            raise ValueError("claimed generator differs from the input")
        word = _delete_endpoint(strands, word, step.get("side"), position)
        strands -= 1
    word = _free_cyclic(word, check)
    if certificate.get("final_strands") != strands or certificate.get("final_word") != list(word):
        raise ValueError("claimed final braid is not the replay result")
    return strands, word
