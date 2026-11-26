"""Compute the full defect sequence over a fixed coefficient ring.

The examples use finite unramified extensions, with uniformizer p and q=p^f.
None of the reciprocal recurrences use coefficients modulo p**r.
"""

from check_branch_poles import division_polynomials, multiply, pole


def coefficient_cycle(p, q, heights):
    """Return a, m, finite coefficient prefix, start and period, for t>=1."""
    t = max(heights)
    m = heights.count(t)
    a = q ** (t - 1)
    modulus = p**m
    omega = sum(q**h for h in heights)
    # To divide coefficients by the powers p**ceil(i/a), build the original
    # finite polynomial once with extra precision. Its degree bounds i.
    largest_index = (omega - len(heights)) // (q - 1)
    ceil_div = lambda j: (j + a - 1) // a
    build_modulus = p ** (m + ceil_div(largest_index))
    factors = division_polynomials(p, q, build_modulus, t)
    product = {0: 1}
    for h in heights:
        product = multiply(product, factors[h], build_modulus)
    normalized = {}
    for degree, value in product.items():
        i, remainder = divmod(omega - degree, q - 1)
        assert remainder == 0
        c_i, remainder = divmod(value, p ** ceil_div(i))
        assert remainder == 0
        if i > 0 and c_i % modulus:
            normalized[i] = c_i % modulus
    memory = max(normalized)
    prefix = [1]
    seen = {}
    while True:
        j = len(prefix)
        if j >= memory:
            state = (j % a, tuple(prefix[-memory:]))
            if state in seen:
                return a, m, prefix, seen[state], j - seen[state]
            seen[state] = j
        total = 0
        for i, coefficient in normalized.items():
            if i <= j:
                shift = ceil_div(i) + ceil_div(j - i) - ceil_div(j)
                total += coefficient * prefix[j - i] * p**shift
        prefix.append(-total % modulus)


def defect(level, p, q, cycle):
    a, m, prefix, start, period = cycle
    for loss in range(1 + (m - 1) * a):
        j = a * (level - 1) - loss
        if j < 0:
            continue
        if j >= len(prefix):
            j = start + (j - start) % period
        if prefix[j] % p ** (loss // a + 1):
            return (q - 1) * loss
    raise AssertionError("lower bound violated")


def main():
    examples = [(2, 2, [2, 2]), (2, 2, [1, 2, 2, 2]),
                (3, 3, [1, 1, 1]), (2, 4, [1, 2, 2])]
    for p, q, heights in examples:
        cycle = coefficient_cycle(p, q, heights)
        a, m, _, start, period = cycle
        assert period % a == 0
        omega = sum(q**h for h in heights)
        D = (q - 1) * a
        for r in range(1, 15):
            direct = pole(p, q, heights, r)
            assert direct == omega + D * (r - 1) - defect(r, p, q, cycle)
        first = 1 + (start + a - 1) // a + (m - 1)
        print(f"p={p}, q={q}, contacts={heights}")
        print(f"Guaranteed period {period//a} from r={first} by state repetition.")
        print(f"Defects at r=1..14: {[defect(r,p,q,cycle) for r in range(1,15)]}")
        print(f"T at r=10^12: {omega + D * (10**12-1) - defect(10**12,p,q,cycle)}")


if __name__ == "__main__":
    main()
