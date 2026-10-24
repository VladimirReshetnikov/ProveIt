"""Small exact sparse-polynomial engine; Python standard library only.

Monomials are sorted tuples of (symbol, exponent). Fixed ports remain symbolic;
degree() counts only the explicitly supplied existential variables.
"""
import ast


class Poly:
    def __init__(self, terms=None):
        self.terms = {m: c for m, c in (terms or {}).items() if c}

    @classmethod
    def integer(cls, n):
        return cls({(): n})

    @classmethod
    def symbol(cls, name):
        return cls({((name, 1),): 1})

    @staticmethod
    def coerce(value):
        return value if isinstance(value, Poly) else Poly.integer(value)

    def __add__(self, other):
        out = dict(self.terms)
        for m, c in self.coerce(other).terms.items():
            out[m] = out.get(m, 0) + c
        return Poly(out)

    __radd__ = __add__

    def __neg__(self):
        return Poly({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) + -self

    def __mul__(self, other):
        out = {}
        for m, c in self.terms.items():
            for n, d in self.coerce(other).terms.items():
                powers = dict(m)
                for v, e in n:
                    powers[v] = powers.get(v, 0) + e
                key = tuple(sorted(powers.items()))
                out[key] = out.get(key, 0) + c*d
        return Poly(out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        if not isinstance(exponent, int) or exponent < 0:
            raise ValueError('only fixed nonnegative integer exponents')
        result, base = Poly.integer(1), self
        while exponent:
            if exponent & 1:
                result = result * base
            exponent //= 2
            # Avoid constructing the entirely unused final squared power.
            # This performance-only change preserves binary exponentiation.
            if exponent:
                base = base * base
        return result

    def __eq__(self, other):
        return self.terms == self.coerce(other).terms

    def symbols(self):
        return {v for m in self.terms for v, _ in m}

    def degree(self, variables):
        variables = set(variables)
        return max((sum(e for v, e in m if v in variables)
                    for m in self.terms), default=-1)

    def substitute(self, replacements):
        out = Poly()
        for monomial, coefficient in self.terms.items():
            term = Poly.integer(coefficient)
            for name, exponent in monomial:
                term = term * replacements.get(name, Poly.symbol(name))**exponent
            out = out + term
        return out

    def coefficient(self, variable_powers, variables):
        """Coefficient in the existential variables, as a polynomial in ports."""
        variables = set(variables)
        wanted = tuple(sorted((k, v) for k, v in variable_powers.items() if v))
        out = {}
        for m, c in self.terms.items():
            if tuple((v, e) for v, e in m if v in variables) == wanted:
                fixed = tuple((v, e) for v, e in m if v not in variables)
                out[fixed] = out.get(fixed, 0) + c
        return Poly(out)

    def expression(self):
        if not self.terms:
            return '0'
        parts = []
        for m, c in sorted(self.terms.items()):
            factors = [str(c)]
            factors += [v if e == 1 else v+'**'+str(e) for v, e in m]
            parts.append('*'.join(factors))
        return ' + '.join(parts)

    def records(self):
        return [{'coefficient': c, 'powers': dict(m)}
                for m, c in sorted(self.terms.items())]


def parse(text, aliases=None):
    aliases = aliases or {}
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return Poly.integer(node.value)
        if isinstance(node, ast.Name):
            return aliases.get(node.id, Poly.symbol(node.id))
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -visit(node.operand)
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow):
                if not isinstance(node.right, ast.Constant):
                    raise ValueError('nonconstant exponent')
                return visit(node.left)**node.right.value
            left, right = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add): return left + right
            if isinstance(node.op, ast.Sub): return left - right
            if isinstance(node.op, ast.Mult): return left * right
        raise ValueError('unsupported polynomial syntax: '+ast.dump(node))
    return visit(ast.parse(text, mode='eval').body)


def require(condition, message):
    if not condition:
        raise ValueError(message)
