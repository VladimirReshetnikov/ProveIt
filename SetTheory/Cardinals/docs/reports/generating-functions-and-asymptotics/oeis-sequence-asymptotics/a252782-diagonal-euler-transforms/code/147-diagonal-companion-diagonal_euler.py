"""Exact arithmetic for the frozen diagonal Euler theorems.

No floating point, optional dependencies, network access, or assert statements.
The three coefficient engines intentionally do not call one another.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import comb, factorial

Q6 = Fraction(8, 9)
LEADING_PHASE = (Fraction(1), Fraction(4, 3), Fraction(2))


def integer(value, name, minimum=0):
    if type(value) is not int:
        raise TypeError(f"{name} must be an integer (not bool or float)")
    if value < minimum:
        raise ValueError(f"{name} must be at least {minimum}")
    return value


def rational(value, name):
    if type(value) not in (int, Fraction):
        raise TypeError(f"{name} must be int or Fraction")
    return Fraction(value)


def residue(value):
    integer(value, "residue")
    if value not in (0, 1, 2):
        raise ValueError("residue must be 0, 1, or 2")
    return value


def sign(value):
    integer(value, "epsilon", -1)
    if value not in (-1, 1):
        raise ValueError("epsilon must be -1 or +1")
    return value


def falling(m, order):
    """Polynomial falling factorial, also valid for rational/negative m."""
    m = rational(m, "m")
    integer(order, "order")
    result = Fraction(1)
    for i in range(order):
        result *= m - i
    return result


def euler_row(exponent, degree, epsilon):
    """Euler logarithmic-derivative recurrence, exponent fixed for whole row."""
    integer(exponent, "exponent")
    integer(degree, "degree")
    sign(epsilon)
    divisors = [0] * (degree + 1)
    for d in range(1, degree + 1):
        color_factor = d ** (exponent + 1)
        for multiple in range(d, degree + 1, d):
            k = multiple // d
            divisors[multiple] += epsilon ** (k - 1) * color_factor
    row = [1] + [0] * degree
    for s in range(1, degree + 1):
        numerator = sum(divisors[j] * row[s - j] for j in range(1, s + 1))
        quotient, remainder = divmod(numerator, s)
        if remainder:
            raise ArithmeticError("Euler recurrence did not give an integer")
        row[s] = quotient
    return tuple(row)


def direct_product_row(exponent, degree, epsilon):
    """Multiply binomial product factors directly; no logarithmic recurrence."""
    integer(exponent, "exponent")
    integer(degree, "degree")
    sign(epsilon)
    row = [1] + [0] * degree
    for j in range(1, degree + 1):
        colors = j ** exponent
        next_row = [0] * (degree + 1)
        for multiplicity in range(degree // j + 1):
            if epsilon == 1:
                ways = comb(colors + multiplicity - 1, multiplicity)
            else:
                ways = comb(colors, multiplicity) if multiplicity <= colors else 0
            for old_degree in range(degree - j * multiplicity + 1):
                next_row[old_degree + j * multiplicity] += row[old_degree] * ways
        row = next_row
    return tuple(row)


def logarithmic_atom_row(exponent, degree, epsilon):
    """Multiply exp(t*x^(jk)) series, isolating (3,1) until the final step.

    This uses individual logarithmic atoms, not the Euler recurrence or
    binomial factors. Rational cancellation is exact, including fermionic signs.
    """
    integer(exponent, "exponent")
    integer(degree, "degree")
    sign(epsilon)
    off_core = [Fraction(1)] + [Fraction(0)] * degree
    for j in range(1, degree + 1):
        for k in range(1, degree // j + 1):
            if (j, k) == (3, 1):
                continue
            d = j * k
            weight = Fraction(epsilon ** (k - 1) * j ** exponent, k)
            coefficients = [Fraction(1)]
            for b in range(1, degree // d + 1):
                coefficients.append(coefficients[-1] * weight / b)
            multiplied = []
            for s in range(degree + 1):
                multiplied.append(sum((off_core[s - d * b] * coefficients[b]
                                       for b in range(s // d + 1)), Fraction(0)))
            off_core = multiplied
    result = []
    for s in range(degree + 1):
        value = sum((off_core[s - 3 * b] * Fraction(3 ** (exponent * b), factorial(b))
                     for b in range(s // 3 + 1)), Fraction(0))
        if value.denominator != 1:
            raise ArithmeticError("Atom series did not give an integer")
        result.append(value.numerator)
    return tuple(result)


def diagonal(n, epsilon, method="euler"):
    integer(n, "n")
    sign(epsilon)
    engines = {"euler": euler_row, "product": direct_product_row,
               "atoms": logarithmic_atom_row}
    if not isinstance(method, str):
        raise TypeError("method must be a string")
    if method not in engines:
        raise ValueError("method must be euler, product, or atoms")
    return engines[method](n, n, epsilon)[n]


def normalization(n):
    integer(n, "n")
    m = n // 3
    return Fraction(3 ** (m * n), factorial(m))


def leading_model(n):
    """Exact L_r(n); n=1 lies outside residue-one factorial model domain."""
    integer(n, "n")
    m, r = divmod(n, 3)
    if r == 1:
        if m == 0:
            raise ValueError("residue-one leading model requires n >= 4")
        return Fraction(3 * 4 ** n * 3 ** ((m - 1) * n), 2 * factorial(m - 1))
    return normalization(n) * (2 ** n if r == 2 else 1)


@dataclass(frozen=True, order=True)
class Atom:
    j: int
    k: int

    def __post_init__(self):
        integer(self.j, "j", 1)
        integer(self.k, "k", 1)
        if (self.j, self.k) == (3, 1):
            raise ValueError("the core atom (3,1) is not a defect")

    @property
    def degree(self):
        return self.j * self.k

    @property
    def loss6(self):
        return Fraction(self.j ** 6, 9 ** self.degree)


@dataclass(frozen=True)
class Profile:
    """Canonical sparse off-core multiplicity array; coefficients are unsigned."""
    entries: tuple

    def __post_init__(self):
        if type(self.entries) is not tuple:
            raise TypeError("profile entries must be a tuple")
        previous = None
        for item in self.entries:
            if type(item) is not tuple or len(item) != 2 or type(item[0]) is not Atom:
                raise TypeError("profile entries must be (Atom, positive int) pairs")
            atom, multiplicity = item
            integer(multiplicity, "multiplicity", 1)
            if previous is not None and atom <= previous:
                raise ValueError("profile atoms must be unique and sorted")
            previous = atom

    @property
    def degree(self):
        return sum(atom.degree * b for atom, b in self.entries)

    @property
    def sign_exponent(self):
        return sum((atom.k - 1) * b for atom, b in self.entries)

    @property
    def coefficient(self):
        denominator = 1
        for atom, b in self.entries:
            denominator *= atom.k ** b * factorial(b)
        return Fraction(1, denominator)

    @property
    def ell(self):
        return self.degree // 3

    @property
    def phase(self):
        numerator = 1
        for atom, b in self.entries:
            numerator *= atom.j ** b
        return Fraction(numerator, 3 ** self.ell)

    @property
    def loss6(self):
        loss = Fraction(1)
        for atom, b in self.entries:
            loss *= atom.loss6 ** b
        return loss

    def signed_coefficient(self, epsilon):
        sign(epsilon)
        return self.coefficient * epsilon ** self.sign_exponent


def degree_bound(r, absolute_floor):
    """First D0 with 9^r*(8/9)^D0 < T^6, proving every retained D < D0."""
    residue(r)
    floor = rational(absolute_floor, "absolute_floor")
    if floor <= 0:
        raise ValueError("absolute_floor must be positive")
    target = floor ** 6
    bound, d0 = Fraction(9 ** r), 0
    while bound >= target:
        bound *= Q6
        d0 += 1
    return d0


def eligible_atoms(r, absolute_floor):
    residue(r)
    floor = rational(absolute_floor, "absolute_floor")
    d0 = degree_bound(r, floor)
    threshold = floor ** 6 / 9 ** r
    atoms = []
    for degree in range(1, d0):
        for j in range(1, degree + 1):
            if degree % j == 0 and (j, degree // j) != (3, 1):
                atom = Atom(j, degree // j)
                if atom.loss6 >= threshold:
                    atoms.append(atom)
    return tuple(sorted(atoms))


@dataclass(frozen=True)
class Enumeration:
    residue: int
    absolute_floor: Fraction
    degree_exclusive: int
    atoms: tuple
    profiles: tuple
    odd_only: bool


def enumerate_sectors(r, absolute_floor, odd_only=False):
    """Exhaustive exact sixth-power pruning, inclusive at the phase floor.

    Each off-core loss j^6/9^(jk) is in (0,1). Thus a product >= B can
    contain only factors >= B. Increasing any multiplicity reduces the loss
    and increases D; each failed necessary condition permanently ends a loop.
    """
    residue(r)
    floor = rational(absolute_floor, "absolute_floor")
    if type(odd_only) is not bool:
        raise TypeError("odd_only must be bool")
    d0 = degree_bound(r, floor)
    atoms = eligible_atoms(r, floor)
    threshold = floor ** 6 / 9 ** r
    results = []

    def visit(index, degree, loss, entries):
        if degree >= d0 or loss < threshold:
            return
        if index == len(atoms):
            if degree % 3 == r:
                profile = Profile(tuple(entries))
                if profile.phase < floor:
                    raise ArithmeticError("sixth-power and phase comparisons disagree")
                if not odd_only or profile.sign_exponent % 2:
                    results.append(profile)
            return
        atom = atoms[index]
        b, new_degree, new_loss = 0, degree, loss
        while new_degree < d0 and new_loss >= threshold:
            visit(index + 1, new_degree, new_loss,
                  entries + ([(atom, b)] if b else []))
            b += 1
            new_degree += atom.degree
            new_loss *= atom.loss6

    visit(0, 0, Fraction(1), [])
    results.sort(key=lambda p: (-p.phase, p.ell, p.entries))
    return Enumeration(r, floor, d0, atoms, tuple(results), odd_only)


def grouped_terms(enumeration, epsilon=1, difference=False):
    """Map (relative phase, falling degree) to the A/Z rational coefficient."""
    if type(enumeration) is not Enumeration:
        raise TypeError("enumeration must be Enumeration")
    sign(epsilon)
    if type(difference) is not bool:
        raise TypeError("difference must be bool")
    terms = {}
    for p in enumeration.profiles:
        coefficient = (2 * p.coefficient if p.sign_exponent % 2 else Fraction(0)) \
            if difference else p.signed_coefficient(epsilon)
        if coefficient:
            key = (p.phase / LEADING_PHASE[enumeration.residue], p.ell)
            terms[key] = terms.get(key, Fraction(0)) + coefficient
    return {key: value for key, value in terms.items() if value}


def all_profiles_through(degree):
    """Unpruned small-degree reference enumerator, for identity and prune tests."""
    integer(degree, "degree")
    atoms = tuple(sorted(Atom(j, k) for j in range(1, degree + 1)
                         for k in range(1, degree // j + 1) if (j, k) != (3, 1)))
    results = []

    def visit(index, left, entries):
        if index == len(atoms):
            results.append(Profile(tuple(entries)))
            return
        atom = atoms[index]
        for b in range(left // atom.degree + 1):
            visit(index + 1, left - b * atom.degree,
                  entries + ([(atom, b)] if b else []))
    visit(0, degree, [])
    return tuple(results)


def profile_identity(n, epsilon):
    """Literal finite identity (E), via unpruned profiles; intended for small n."""
    integer(n, "n")
    sign(epsilon)
    m, r = divmod(n, 3)
    value = Fraction(0)
    for p in all_profiles_through(n):
        if p.degree % 3 == r:
            value += p.signed_coefficient(epsilon) * falling(m, p.ell) * p.phase ** n
    return value * normalization(n)


def bernoulli_numbers(order):
    """B_1=-1/2 convention, from sum binom(n+1,k) B_k = 0."""
    integer(order, "order")
    values = [Fraction(1)]
    for n in range(1, order + 1):
        values.append(-sum((comb(n + 1, k) * values[k] for k in range(n)),
                           Fraction(0)) / (n + 1))
    return tuple(values)


def bernoulli_polynomial(order, x):
    integer(order, "order")
    x = rational(x, "x")
    numbers = bernoulli_numbers(order)
    return sum((comb(order, k) * numbers[k] * x ** (order - k)
                for k in range(order + 1)), Fraction(0))


def shifted_stirling_coefficient(r, k):
    """Exact g_(r,k) in inverse theorem (I2), not a numerical inverse solver."""
    residue(r)
    integer(k, "k", 1)
    b = Fraction(1) - Fraction((0, 4, 2)[r], 3)
    return Fraction((-1) ** (k + 1) * 3 ** k, k * (k + 1)) * bernoulli_polynomial(k + 1, b)


def tail_onset_sixth_power(n):
    """Exact equivalent of 2*n^(1/3)*q^n <= 1/2, with no roots/logs."""
    integer(n, "n", 1)
    return 4096 * n ** 2 * Q6 ** n
