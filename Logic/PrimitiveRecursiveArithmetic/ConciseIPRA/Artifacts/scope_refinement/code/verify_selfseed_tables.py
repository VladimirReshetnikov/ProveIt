"""Finite checks of displayed term tables; not a universal proof certificate."""
import json


def C(n, a):
    return a + 1 if n == 0 else a


def epsilon(a, b):
    return int(a == b)


def neg(b):
    return epsilon(b, 0)


def conjunction(b, c):
    return epsilon(C(b, epsilon(c, 0)), 0)


def disjunction(b, c):
    return neg(conjunction(neg(b), neg(c)))


def increment(b, a):
    return C(epsilon(b, 0), a)


def countdown(k, v):
    value = 0
    for r in range(1, k + 1):
        condition = 0
        for i in range(1, min(r, k - 1) + 1):
            condition = disjunction(condition, epsilon(v, i))
        condition = disjunction(condition, epsilon(v, k + 1) if r == k else 0)
        value = increment(neg(condition), value)
    return value


def cycle(r, v):
    value = 0
    for i in range(r):
        for _ in range(i + 1):
            value = increment(epsilon(v, i), value)
    return value


def check(limit=39):
    rows = 0
    chain_rows = 0
    cycle_rows = 0
    for k in range(1, limit + 1):
        q = [k + 1] + [k - j for j in range(1, k + 1)]
        if len(set(q)) != k + 1:
            raise ValueError('Distinctness check failed')
        for v in range(k + 10):
            actual = countdown(k, v)
            expected = v - 1 if 1 <= v < k else k - 1 if v == k + 1 else k
            if actual != expected or actual == q[0]:
                raise ValueError(('Countdown table', k, v, actual, expected))
            rows += 1
            for j in range(1, k + 1):
                if (actual == q[j]) != (v == q[j - 1]):
                    raise ValueError(('Unique chain predecessor', k, v, j))
                chain_rows += 1
        state = k + 1
        for j in range(1, k + 1):
            state = countdown(k, state)
            if state != q[j]:
                raise ValueError(('Finite orbit', k, j, state))
        for v in range(k + 10):
            actual = cycle(k, v)
            expected = v + 1 if v < k else 0
            if actual != expected:
                raise ValueError(('Cycle table', k, v, actual, expected))
            state = v
            for _ in range(k):
                state = cycle(k, state)
            if state == v:
                raise ValueError(('Forbidden cycle fixed point', k, v))
            cycle_rows += 1
    return {'result': 'PASS', 'maximum_external_index': limit,
            'countdown_table_rows': rows, 'chain_equivalence_rows': chain_rows,
            'cycle_table_rows': cycle_rows,
            'scope': 'Finite standard-value checks of displayed constructions only; the universal theorem is proved in writing.'}


if __name__ == '__main__':
    print(json.dumps(check(), indent=2))
