"""Finite-support representation of ordinal powers below epsilon_0.

All ordinal arguments use the canonical tuples from arithmetic.py.
A support is a tuple of (position, digit) pairs, positions decreasing
strictly and digits nonzero. encode and decode both take the radix
and the exponent/domain bound.
"""
from itertools import groupby
from operator import itemgetter

from arithmetic import ZERO, ONE, OMEGA, W, nat, succ, add, mul, power, growth
from check import divide, terms_up_to


def encode(base, exponent, support):
    """Map a finite support on I_exponent to its ordinal below base**exponent."""
    if base == ZERO and exponent != ZERO:
        raise ValueError("there is no function from a nonempty interval to zero")
    value = ZERO
    previous = None
    for position, digit in support:
        if position >= exponent or (previous is not None and position >= previous):
            raise ValueError("positions must decrease strictly below the exponent")
        if not ZERO < digit < base:
            raise ValueError("each listed digit must be positive and below the base")
        value = add(value, mul(power(base, position), digit))
        previous = position
    return value


def decode(base, exponent, value):
    """Invert encode using grouped Cantor exponents and bounded ordinal division."""
    if base <= ONE:
        if value == ZERO and (base == ONE or exponent == ZERO):
            return ()
        raise ValueError("value lies outside this zero- or unit-base power")

    block_size = growth(base)
    outer_entries = (divide(entry, block_size) for entry in value)
    support = []
    for block, members in groupby(outer_entries, key=itemgetter(0)):
        coefficient = tuple(remainder for _, remainder in members)
        # C < base**fuel by the head bound in the proof. The block is nonempty.
        fuel = len(coefficient) + 1 if base < OMEGA else len(coefficient[0]) + 1
        offset = mul(OMEGA, block)
        ascending_digits = []
        for i in range(fuel):
            if coefficient == ZERO:
                break
            coefficient, digit = divide(coefficient, base)
            if digit:
                ascending_digits.append((add(offset, nat(i)), digit))
        assert coefficient == ZERO, "the block exceeded the proved finite digit bound"
        support.extend(reversed(ascending_digits))

    if support and support[0][0] >= exponent:
        raise ValueError("value lies outside the given ordinal power")
    return tuple(support)


def selfcheck():
    two, three = nat(2), nat(3)
    w2 = W(two)
    radices = [two, three, OMEGA, succ(OMEGA), mul(OMEGA, two),
               add(w2, OMEGA), succ(w2), W(OMEGA)]
    bounds = [ZERO, ONE, two, three, OMEGA, succ(OMEGA),
              mul(OMEGA, two), w2, succ(w2)]
    values = terms_up_to(6) + [nat(13), nat(17), add(w2, OMEGA),
                               add(W(OMEGA), nat(5))]
    recovered = 0
    for base in radices:
        for bound in bounds:
            ceiling = power(base, bound)
            for value in values:
                if value >= ceiling:
                    try:
                        decode(base, bound, value)
                    except ValueError:
                        continue
                    raise AssertionError("accepted value outside its power")
                digits = decode(base, bound, value)
                assert encode(base, bound, digits) == value
                recovered += 1

    supports_checked = 0
    positions = (succ(w2), add(OMEGA, two), OMEGA, two, ONE, ZERO)
    bound = succ(positions[0])
    for base in radices:
        nonzero = [d for d in (ONE, two, OMEGA, succ(OMEGA), w2) if d < base]
        samples = {()}
        # Include every occupied-position mask and some infinite digits.
        for shift in range(len(nonzero)):
            for mask in range(1, 1 << len(positions)):
                sample = tuple((s, nonzero[(i + shift) % len(nonzero)])
                               for i, s in enumerate(positions) if mask & (1 << i))
                samples.add(sample)
        previous = None
        for digits in sorted(samples):
            value = encode(base, bound, digits)
            assert decode(base, bound, value) == digits
            assert previous is None or previous < value
            previous = value
        supports_checked += len(samples)

    assert decode(three, OMEGA, nat(17)) == ((two, ONE), (ONE, two), (ZERO, two))
    for base, bound in ((ZERO, ZERO), (ONE, ZERO), (ONE, OMEGA)):
        assert encode(base, bound, ()) == ZERO and decode(base, bound, ZERO) == ()
    for invalid in (lambda: encode(ZERO, ONE, ()), lambda: decode(ZERO, ONE, ZERO),
                    lambda: decode(ONE, OMEGA, ONE),
                    lambda: encode(two, OMEGA, ((ONE, ONE), (ONE, ONE))),
                    lambda: encode(two, OMEGA, ((OMEGA, ONE),)),
                    lambda: encode(two, ONE, ((ZERO, two),))):
        try:
            invalid()
        except ValueError:
            continue
        raise AssertionError("accepted an invalid value or function")
    print(f"Checked {recovered} value round trips and {supports_checked} digit-list "
          f"round trips, with strict comparison, over {len(radices)} radices.")


if __name__ == "__main__":
    selfcheck()
