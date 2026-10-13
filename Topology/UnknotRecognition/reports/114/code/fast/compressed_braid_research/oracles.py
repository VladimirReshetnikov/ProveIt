"""Independent explicit controls, not the full maintained fastunknot backend."""
from collections import deque


def tokens_reduce(tokens):
    stack = []
    for token in tokens:
        if stack and (stack[-1] == 1) == (token == 1):
            old = stack.pop()
            if token != 1 and old == token:
                stack.append(5 - token)
        else:
            stack.append(token)
    return stack


def cyclic_tokens(tokens):
    result = deque(tokens_reduce(tokens))
    while len(result) > 1 and (result[0] == 1) == (result[-1] == 1):
        first, last = result.popleft(), result.pop()
        if first != 1 and first == last:
            result.append(5 - first)
    return list(result)


def explicit(word):
    """Source-derived stack control, including component and writhe gates."""
    p, exponent = [0, 1, 2], 0
    for g in word:
        i = abs(g) - 1
        p[i], p[i + 1] = p[i + 1], p[i]
        exponent += 1 if g > 0 else -1
    if p[0] == 0 or p[p[0]] == 0:
        return 'LINK'
    if abs(exponent) > 2:
        return 'KNOTTED'
    image = {1: (3, 1), -1: (1, 2), 2: (1, 3), -2: (2, 1)}
    c = cyclic_tokens(token for g in word for token in image[g])
    good = ((exponent == 2 and c == [2]) or (exponent == -2 and c == [3]) or
            (exponent == 0 and len(c) == 4 and sorted(c) == [1, 1, 2, 3]))
    return 'UNKNOT' if good else 'KNOTTED'


def matrix(word):
    """Independent integer Burau determinant plus Bennequin control."""
    A, B, C, D = 1, 0, 0, 1
    p, e = [0, 1, 2], 0
    for g in word:
        i = abs(g) - 1
        p[i], p[i + 1] = p[i + 1], p[i]
        e += 1 if g > 0 else -1
        if g == 1:
            B, D = A + B, C + D
        elif g == -1:
            B, D = B - A, D - C
        elif g == 2:
            A, C = A - B, C - D
        elif g == -2:
            A, C = A + B, C + D
    if p[0] == 0 or p[p[0]] == 0:
        return 'LINK'
    return 'UNKNOT' if abs(e) <= 2 and abs(2 - A - D) == 1 else 'KNOTTED'
