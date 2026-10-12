"""Small independent reference oracles, not part of the polynomial-time route.

The faithful Artin action can expand exponentially. Use it only for bounded
validation. It is intentionally unrelated to Garside's normal form.
"""
from __future__ import annotations

def reduce_free(word):
    stack = []
    for a in word:
        if stack and stack[-1] == -a:
            stack.pop()
        else:
            stack.append(a)
    return tuple(stack)


def inverse_word(word):
    return tuple(-a for a in reversed(word))


def artin_action(b, word, max_letters=1000000):
    images = [tuple([i + 1]) for i in range(b)]
    for a in word:
        i = abs(a) - 1
        u, v = images[i], images[i + 1]
        if a > 0:
            images[i], images[i + 1] = reduce_free(u + v + inverse_word(u)), u
        else:
            images[i], images[i + 1] = v, reduce_free(inverse_word(v) + u + v)
        if sum(map(len, images)) > max_letters:
            raise RuntimeError("small Artin-action oracle exceeded its expansion cap")
    return tuple(images)


def brute_kernel(b, word, *, cyclic=False, support_cap=None):
    """Exhaustive interval DP using faithful free-group actions, not prefix keys."""
    word = tuple(word)
    n = len(word)
    targets = [(0, artin_action(b, ()))]
    targets += [(a, artin_action(b, (a,))) for i in range(1, b) for a in (i, -i)]
    answer = n
    for cut in range(max(1, n) if cyclic else 1):
        w = word[cut:] + word[:cut]
        dp = list(range(n + 1))
        for j in range(1, n + 1):
            dp[j] = dp[j - 1] + 1
            for i in range(j):
                block = w[i:j]
                if support_cap is not None and len(set(map(abs, block))) > support_cap:
                    continue
                image = artin_action(b, block)
                for target, expected in targets:
                    if image == expected:
                        dp[j] = min(dp[j], dp[i] + int(target != 0))
        answer = min(answer, dp[n])
    return answer


def c2c3_quotient(word):
    # x has order 2; y has order 3. Tokens: x=0, y=1, y^2=2.
    images = {1:(2,0), -1:(0,1), 2:(0,2), -2:(1,0)}
    stack = []
    for a in word:
        for token in images[a]:
            if not stack or (stack[-1] == 0) != (token == 0):
                stack.append(token)
            elif token == 0:
                stack.pop()
            else:
                total = (stack.pop() + token) % 3
                if total:
                    stack.append(total)
    return tuple(stack)


def old_barrier(h):
    u, v = (1,2,3,1,2,1), (3,2,1,3,2,3)
    return (u + inverse_word(v)) * h + (1,2,3)


def geodesic_unknot(m):
    return (1,) * (m + 1) + (2,) + (-1,) * m
