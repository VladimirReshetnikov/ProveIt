"""Check primal and dual Fourier-weight certificates using exact fractions."""
from fractions import Fraction


def power_coefficients(exponent, length):
    """Taylor coefficients of (1-z)^(-exponent) up to length-1."""
    values = [Fraction(1)]
    for k in range(1, length):
        values.append(values[-1] * (exponent + k - 1) / k)
    return values


def check(degree, block_length, alpha):
    length = min(block_length, degree // 2 + 1)
    c = power_coefficients(alpha, length)
    targets = power_coefficients(2 * alpha, block_length)
    reciprocal = power_coefficients(-alpha, length)
    ends = [min(i, degree - i) for i in range(degree + 1)]
    vector = [c[i] if i < length else 0 for i in ends]
    mean = sum(entry**2 for entry in vector)
    for j, target in enumerate(targets):
        gain = sum(vector[i] * vector[j-i] for i in range(j+1))
        assert gain >= target
        if j < length:
            assert gain == target

    weights = [Fraction(1)] * length
    if degree == 2 * length - 2:
        weights[-1] = Fraction(1, 2)
    y = [weight * ci for weight, ci in zip(weights, c)]
    multiplier = [
        sum(reciprocal[h] * y[i+h] for h in range(length - i))
        for i in range(length)
    ]
    assert min(multiplier) > 0
    for i in range(length):
        assert sum(c[j] * multiplier[i+j] for j in range(length-i)) == y[i]
    dual_bound = 2 * sum(lam * target for lam, target in zip(multiplier, targets))
    assert dual_bound == mean
    return mean


if __name__ == "__main__":
    examples = 0
    for degree in range(1, 25):
        for length in range(1, degree + 1):
            for alpha in map(Fraction, ["1/5", "1/3", "1/2", "2/3", "4/5"]):
                check(degree, length, alpha)
                examples += 1
    example = check(4, 4, Fraction(1, 3))
    assert example == Fraction(184, 81)
    print(f"Verified {examples} finite primal-dual pairs. N=r=4, alpha=1/3: {example}.")
