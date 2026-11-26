"""Verify the interval extremizers and the two-prime density bound using integers."""
from fractions import Fraction


def interval_profile(last_length):
    """Return maximum size, mandatory indices and possible indices at each length."""
    rank = [0] * (last_length + 1)
    mandatory = [0] * (last_length + 1)
    possible = [0] * (last_length + 1)

    def visit(selected, available, size):
        while available:
            bit = available & -available
            available ^= bit
            t = bit.bit_length() - 1
            mask = selected | bit
            length = t + 1
            if rank[length] < size + 1:
                rank[length] = size + 1
                mandatory[length] = possible[length] = mask
            elif rank[length] == size + 1:
                mandatory[length] &= mask
                possible[length] |= mask
            # The newly forbidden right endpoints are 2t-x for earlier points x.
            blocked = 0
            previous = selected
            while previous:
                point = previous & -previous
                previous ^= point
                blocked |= 1 << (2*t - (point.bit_length()-1))
            visit(mask, available & ~blocked, size + 1)

    visit(0, (1 << last_length)-1, 0)
    # Up to here the masks for length n refer to sets whose maximum is n-1.
    for n in range(1,last_length + 1):
        if rank[n-1] > rank[n]:
            rank[n] = rank[n-1]
            mandatory[n], possible[n] = mandatory[n-1], possible[n-1]
        elif rank[n-1] == rank[n]:
            mandatory[n] &= mandatory[n-1]
            possible[n] |= possible[n-1]
    return rank, mandatory, possible


def fraction_to_decimal(x, digits):
    """Round a nonnegative rational upwards to the specified decimal places."""
    scale = 10**digits
    n = -(-x.numerator*scale//x.denominator)
    return f"{n//scale}.{n%scale:0{digits}d}"


if __name__ == "__main__":
    L = 32
    rank, must, may = interval_profile(L)
    for side, row in [(9,4), (20,7), (30,4)]:
        assert must[side-row] & 1
        assert not ((may[side] >> row) & 1)
        print(f"side {side}, row {row}: maximum of length {side-row} "
              f"(size {rank[side-row]}) contains 0; maximum of length "
              f"{side} (size {rank[side]}) omits {row}.")
    print("Ranks for interval lengths 0 through", L, rank)
    # Each next rank increment is 0 or 1.
    upper1 = sum(Fraction(rank[n] - rank[n-1],2**n) for n in range(1, L+1))
    error = Fraction(1,2**L)
    improvement = Fraction(1,4)*sum(Fraction(1,2**k) for k in (8,19,29))
    upper2 = upper1 + error - improvement
    print("Dyadic enclosure for one-prime bound:",upper1,upper1 + error)
    print("Improvement when q=2:", improvement)
    print("Rational upper bound:", upper2)
    print("Rounded upward to 12 places:", fraction_to_decimal(upper2, 12))
