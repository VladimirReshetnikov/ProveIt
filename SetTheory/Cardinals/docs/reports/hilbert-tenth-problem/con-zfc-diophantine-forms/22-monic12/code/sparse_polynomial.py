"""Small dependency-free sparse polynomial ring for finite certificate checks."""
from collections import defaultdict

class Ring:
    def __init__(self, names):
        self.names = tuple(names)
        self.n = len(names)
        self.zero_monomial = (0,) * self.n
        self.variables = {name: Polynomial(self, {tuple(int(i == j) for i in range(self.n)): 1})
                          for j, name in enumerate(names)}

    def coerce(self, x):
        if isinstance(x, Polynomial):
            assert x.ring is self
            return x
        assert isinstance(x, int)
        return Polynomial(self, {self.zero_monomial: x} if x else {})

class Polynomial:
    def __init__(self, ring, terms):
        self.ring = ring
        self.terms = {m: c for m, c in terms.items() if c}

    def __add__(self, other):
        other = self.ring.coerce(other)
        terms = dict(self.terms)
        for m, c in other.terms.items():
            terms[m] = terms.get(m, 0) + c
            if terms[m] == 0:
                del terms[m]
        return Polynomial(self.ring, terms)
    __radd__ = __add__

    def __neg__(self):
        return Polynomial(self.ring, {m:-c for m,c in self.terms.items()})
    def __sub__(self, other):
        return self + -self.ring.coerce(other)
    def __rsub__(self, other):
        return self.ring.coerce(other) + -self

    def __mul__(self, other):
        other = self.ring.coerce(other)
        terms = defaultdict(int)
        for a, x in self.terms.items():
            for b, y in other.terms.items():
                terms[tuple(i+j for i,j in zip(a,b))] += x*y
        return Polynomial(self.ring, terms)
    __rmul__ = __mul__

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        result, current = self.ring.coerce(1), self
        while exponent:
            if exponent & 1:
                result = result*current
            exponent //= 2
            if exponent:
                current = current*current
        return result

    def __eq__(self, other):
        try:
            other = self.ring.coerce(other)
        except (TypeError, AssertionError):
            return False
        return self.terms == other.terms

    def substitute(self, substitutions):
        values = {name:self.ring.coerce(substitutions.get(name,p))
                  for name,p in self.ring.variables.items()}
        cache = {(name,0):self.ring.coerce(1) for name in self.ring.names}
        result = self.ring.coerce(0)
        for monomial, coefficient in self.terms.items():
            term = self.ring.coerce(coefficient)
            for name, exponent in zip(self.ring.names, monomial):
                if not exponent:
                    continue
                key = (name,exponent)
                if key not in cache:
                    cache[key] = values[name]**exponent
                term *= cache[key]
            result += term
        return result

    def degree(self, variable_count=None):
        if variable_count is None:
            variable_count = self.ring.n
        return max((sum(m[:variable_count]) for m in self.terms),default=-1)

    def free_variables(self):
        return {name for m in self.terms for name,power in zip(self.ring.names,m) if power}

    def coefficient(self, powers):
        monomial = tuple(powers.get(name,0) for name in self.ring.names)
        return self.terms.get(monomial,0)

    def json_terms(self):
        return [{'powers':list(m),'coefficient':c} for m,c in sorted(self.terms.items(),reverse=True)]

    def __str__(self):
        if not self.terms:
            return '0'
        out=[]
        for m,c in sorted(self.terms.items(),reverse=True):
            factors=[name if e==1 else f'{name}^{e}' for name,e in zip(self.ring.names,m) if e]
            term='*'.join(factors)
            if not factors or abs(c)!=1:
                term=str(abs(c))+('*'+term if factors else '')
            if not out:
                out.append(('-' if c<0 else '')+term)
            else:
                out.append((' - ' if c<0 else ' + ')+term)
        return ''.join(out)
