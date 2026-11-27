"""Two exact least-period certificates for mixed Lubin--Tate contacts over Q_2.

The two calculations use integer recurrence modulo 2^m and independently
monic polynomial division modulo 2^r. Run with Python 3.8 or later.
"""


def multiply(left, right):
    out = [0] * (len(left) + len(right) - 1)
    for i, c in enumerate(left):
        for j, d in enumerate(right):
            out[i + j] += c * d
    return out


def denominator(depths):
    """Canonical iterates f^h(X) for f(X)=2X+X^2, then their product."""
    forms = [[0, 1]]
    for _ in range(max(depths)):
        prev = forms[-1]
        square = multiply(prev, prev)
        for i, value in enumerate(prev):
            square[i] += 2 * value
        forms.append(square)
    poly = [1]
    for depth in depths:
        poly = multiply(poly, forms[depth])
    return poly


def reduced_defects(depths, count):
    """Reciprocal coefficients H_i, scaled by 2^ceil(i/D), modulo 2^m."""
    D = 2 ** (max(depths) - 1)
    m = depths.count(max(depths))
    coeff = denominator(depths)[::-1]
    scale = lambda i: (i + D - 1) // D
    terms = []
    for i, value in enumerate(coeff[1:], start=1):
        if value:
            divisor = 2 ** scale(i)
            assert value % divisor == 0
            terms.append((i, value // divisor))
    scaled = [1]
    for j in range(1, D * (count - 1) + 1):
        total = sum(c * scaled[j-i] * 2 ** (scale(i)+scale(j-i)-scale(j))
                    for i, c in terms if i <= j)
        scaled.append((-total) % (2 ** m))
    out = []
    for n in range(count):
        for loss in range(min(D*n, D*(m-1))+1):
            if scaled[D*n-loss] % (2 ** (loss//D+1)):
                out.append(loss)
                break
        else:
            raise AssertionError("The proved defect bound was exceeded")
    return out


def direct_defect(poly, n, D):
    """Least t with X^t=0 in (Z/2^(n+1))[X]/poly."""
    degree = len(poly)-1
    remainder = [1] + [0]*(degree-1)
    modulus = 2 ** (n+1)
    for t in range(degree + D*n + 1):
        if not any(remainder):
            return degree + D*n - t
        lead = remainder[-1]
        remainder = [(-lead*poly[0]) % modulus] + [
            (remainder[i-1]-lead*poly[i]) % modulus for i in range(1, degree)]
    raise AssertionError("The upper bound was exceeded")


def main():
    for depths, expected in [([2]*5, 32), ([2]*5+[1]*2, 64)]:
        # p=q=2, e=1, h=4. The theorem gives period dividing 64 from n=7.
        start, bound, D = 7, 64, 2
        losses = reduced_defects(depths, start+2*bound)
        poly = denominator(depths)
        for n, loss in enumerate(losses):
            assert loss == direct_defect(poly, n, D)
        word = losses[start:start+bound]
        assert word == losses[start+bound:start+2*bound]
        period = next(s for s in (1, 2, 4, 8, 16, 32, 64)
                      if all(word[i] == word[(i+s) % bound] for i in range(bound)))
        assert period == expected
        witness = next(i for i in range(bound) if word[i] != word[(i+period//2)%bound])
        print(f"depths={tuple(depths)}, proved period bound={bound}, least period={period}")
        n = start + witness
        print(f"  half-period witness: delta({n})={losses[n]}, "
              f"delta({n+period//2})={losses[n+period//2]}")
        print(f"  direct quotient and reciprocal calculations agree for {len(losses)} precisions")


if __name__ == "__main__":
    main()
