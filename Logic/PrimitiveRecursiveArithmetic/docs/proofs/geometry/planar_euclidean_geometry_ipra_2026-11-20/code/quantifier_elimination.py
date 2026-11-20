"""Quantifier elimination over real closed fields, for small examples.

The matrix is a SymPy Boolean combination of rational polynomial relations.
Give quantifiers outermost first to qe(). Coefficient operations are over QQ
rational functions. Whenever specialization matters, the coefficient program
requests a polynomial sign, then resumes separately on all three branches.
Use real Symbols without extra sign assumptions. The prefix is in prenex order.
The resulting guards may include branches with inconsistent sign conditions.
"""
from functools import lru_cache
from itertools import product
import sympy as sp
from sympy.core.relational import Relational
from sympy.logic.boolalg import BooleanFunction

from sign_cells import INDICATOR


class Branch(Exception):
    """A sign not yet fixed by the current guard."""


class InvalidDenominator(Exception):
    """A branch that contradicts a prior division guard."""


@lru_cache(maxsize=8192)
def factors(expr):
    return sp.factor_list(expr)


class Coefficients:
    def __init__(self, signs):
        self.signs = signs

    def sign_polynomial(self, p):
        if p == 0:
            return 0
        content, factorization = factors(p)
        if any(self.signs.get(factor) == 0 for factor, _ in factorization):
            return 0
        result = 1 if content > 0 else -1
        for factor, exponent in factorization:
            if factor not in self.signs:
                raise Branch(factor)
            s = self.signs[factor]
            if s == 0:
                return 0
            result *= s ** exponent
        return result

    def sign(self, e):
        p, q = sp.cancel(e).as_numer_denom()
        denominator = self.sign_polynomial(q)
        if not denominator:
            raise InvalidDenominator()
        return self.sign_polynomial(p) * denominator

    def trim(self, f):
        terms = list(f)
        while terms and self.sign(terms[-1]) == 0:
            terms.pop()
        return tuple(terms)

    def divide(self, f, g):
        """Both inputs already have their true specialized degrees."""
        assert g
        rem = list(f)
        quo = [sp.S.Zero] * max(0, len(f) - len(g) + 1)
        while len(rem) >= len(g):
            offset = len(rem) - len(g)
            factor = sp.cancel(rem[-1] / g[-1])
            quo[offset] = factor
            # The leading term cancels identically.
            rem.pop()
            for j in range(len(g) - 1):
                rem[offset+j] -= factor * g[j]
            rem = list(self.trim(rem))
        return tuple(quo), tuple(rem)

    def gcd(self, f, g):
        while g:
            f, g = g, self.divide(f, g)[1]
        return tuple(sp.cancel(x / f[-1]) for x in f)

    def squarefree(self, f):
        if not f:
            return ()
        return self.divide(f, self.gcd(f, derivative(f)))[0]

    def tail(self, f, right):
        if not f:
            return 0
        leading = self.sign(f[-1])
        return leading if right or len(f) % 2 else -leading

    def query(self, d, w):
        if len(d) < 2:
            return 0
        z = self.divide(self.trim(times(derivative(d), w)), d)[1]
        if not z:
            return 0
        common = self.gcd(d, z)
        a = self.divide(d, common)[0]
        b = self.divide(z, common)[0]
        chain = [a, b]
        while True:
            rem = self.divide(chain[-2], chain[-1])[1]
            if not rem:
                break
            chain.append(tuple(-x for x in rem))

        def variations(right):
            signs = [self.tail(f, right) for f in chain]
            return sum(x != y for x, y in zip(signs, signs[1:]))

        return variations(False) - variations(True)

    def some_at_root(self, d, polys, accepts):
        if len(d) < 2:
            return False
        powers = [(ONE, p, times(p, p)) for p in polys]

        @lru_cache(maxsize=None)
        def query(exponents):
            w = ONE
            for row, e in zip(powers, exponents):
                w = times(w, row[e])
            return self.query(d, w)

        for signs in product((-1, 0, 1), repeat=len(polys)):
            if not accepts(signs):
                continue
            scaled_count = 0
            for terms in product(*(INDICATOR[s] for s in signs)):
                coefficient = 1
                for _, c in terms:
                    coefficient *= c
                scaled_count += coefficient * query(tuple(e for e, _ in terms))
            if scaled_count > 0:
                return True
        return False

    def exists(self, polys, accepts):
        polys = [self.trim(p) for p in polys]
        if any(accepts(tuple(self.tail(p, side) for p in polys))
               for side in (False, True)):
            return True
        p = ONE
        for f in polys:
            if len(f) > 1:
                p = times(p, f)
        p = self.squarefree(p)
        if len(polys) == 1 and accepts((0,)):
            if self.query(p, ONE) > 0:
                return True
            if not accepts((-1,)) and not accepts((1,)):
                return False
        return self.some_at_root(p, polys, accepts) or self.some_at_root(
            self.squarefree(derivative(p)), polys, accepts)


ONE = (sp.S.One,)


def times(f, g):
    if not f or not g:
        return ()
    result = [sp.S.Zero] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            result[i+j] += a*b
    return tuple(result)


def derivative(f):
    return tuple(i*f[i] for i in range(1, len(f)))


def exists(variable, formula):
    """Return a quantifier-free formula equivalent to exists variable, formula."""
    formula = sp.sympify(formula)
    if not isinstance(variable, sp.Symbol):
        raise TypeError("a quantified variable must be an ordinary symbol")
    def validate(node):
        if isinstance(node, Relational):
            if node.has(sp.Float):
                raise ValueError("use exact rational coefficients")
            return
        if node in (sp.true, sp.false):
            return
        if not isinstance(node, BooleanFunction):
            raise ValueError("the matrix must be a Boolean combination of polynomial comparisons")
        for child in node.args:
            validate(child)

    validate(formula)
    atoms = sorted(formula.atoms(Relational), key=sp.default_sort_key)
    generators = sorted(formula.free_symbols, key=sp.default_sort_key)
    for atom in atoms:
        if generators:
            sp.Poly(atom.lhs - atom.rhs, *generators, domain=sp.QQ)
    if variable not in formula.free_symbols:
        return formula
    polys = [tuple(reversed(sp.Poly(a.lhs - a.rhs, variable).all_coeffs()))
             for a in atoms]

    @lru_cache(maxsize=None)
    def accepts(signs):
        return bool(formula.xreplace(
            {a: a.func(s, 0) for a, s in zip(atoms, signs)}))

    def tree(guards):
        try:
            return sp.sympify(Coefficients(guards).exists(polys, accepts))
        except InvalidDenominator:
            # This case has no parameter tuples.
            return sp.false
        except Branch as request:
            polynomial, = request.args
        results = [tree({**guards, polynomial: sign}) for sign in (-1, 0, 1)]
        if results[0] == results[1] == results[2]:
            return results[0]
        guards = [polynomial < 0, sp.Eq(polynomial, 0), polynomial > 0]
        return sp.Or(*(sp.And(g, v) for g, v in zip(guards, results)))

    return tree({})


def qe(prefix, matrix):
    """Eliminate a prenex prefix of ('forall'|'exists', real symbol) pairs."""
    result = sp.sympify(matrix)
    for quantifier, symbol in reversed(prefix):
        if quantifier == 'exists':
            result = exists(symbol, result)
        elif quantifier == 'forall':
            result = sp.Not(exists(symbol, sp.Not(result)))
        else:
            raise ValueError("use 'exists' or 'forall'")
    return result
