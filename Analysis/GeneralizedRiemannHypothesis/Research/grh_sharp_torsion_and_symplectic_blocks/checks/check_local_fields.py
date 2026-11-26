"""Finite checks for the order-four torsion problem. Uses integer arithmetic only."""
from fractions import Fraction
from itertools import product
from math import gcd


def capped_v2(x, bound=4):
    """Return the 2-adic valuation, truncated at an integer bound."""
    if x == 0:
        return bound
    return min(bound, (abs(x) & -abs(x)).bit_length() - 1)


def capped_defect(linear, constant, ramified):
    """Max of min(2,v(u^2+1)) in the indicated quadratic integer ring.

    In the basis 1, pi, write pi^2=linear*pi+constant.  For the ramified
    fields pi is a uniformizer. In the unramified case its residue and 1
    form a basis over F_2. Reduction of both coefficients mod 4 suffices.
    """
    best = Fraction(0)
    for a, b in product(range(4), repeat=2):
        c = a*a + constant*b*b + 1
        d = 2*a*b + linear*b*b
        v = min(Fraction(capped_v2(c)),
                Fraction(capped_v2(d)) + (Fraction(1, 2) if ramified else 0))
        best = max(best, min(2, v))
    return best


def test_quadratic_fields():
    # label, pi, linear coefficient of pi^2, constant coefficient, ramification
    examples = (
        ("-1", "i-1", -2, -2, True, 2),
        ("3", "sqrt(3)-1", -2, 2, True, 2),
        ("5", "(1+sqrt(5))/2", 1, 1, False, 1),
        ("2", "sqrt(2)", 0, 2, True, Fraction(3, 2)),
        ("-2", "sqrt(-2)", 0, -2, True, Fraction(3, 2)),
        ("10", "sqrt(10)", 0, 10, True, Fraction(3, 2)),
        ("-10", "sqrt(-10)", 0, -10, True, Fraction(3, 2)),
    )
    print("radicand  capped quadratic defect  strict tolerance cutoff")
    for d, basis, linear, constant, ramified, expected in examples:
        defect = capped_defect(linear, constant, ramified)
        assert defect == expected, (basis, defect)
        print(f"{d:>8}  {str(defect):>23}  {str(Fraction(defect-1, 2)):>23}")


def check_residue_degrees():
    count = 0
    for p, e, h in product((2, 3, 5, 7, 11), range(1, 65), range(1, 8)):
        n = (p-1)*p**(h-1)
        d = n//gcd(n, e)
        classes = {pow(x, d, p) for x in range(1, p)}
        wild = gcd(p**(h-1), e)
        assert len(classes) == gcd(e, p-1)
        assert d*len(classes) == n//wild
        count += 1
    print(f"Residue degree identities checked on {count} parameter triples.")


if __name__ == "__main__":
    test_quadratic_fields()
    check_residue_degrees()
