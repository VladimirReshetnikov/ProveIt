"""Solution-preserving polynomial-to-counter-schedule frontends.

Uses compiler.py, Python 3.10+, and the standard library. Coefficients are
expanded in unary; this is an exact research frontend, not a binary-size
optimized expression compiler. All variables and gate values range over N.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import json

from compiler import (Poly, Empty, Concat, Repeat, Transition, Compiler,
                      word_expression, parameters)


def sequence(expressions):
    out = Empty()
    for expr in expressions:
        out = Concat(out, expr)
    return out


def monomial_block(label: str, coefficient: int, monomial: tuple[str, ...]):
    if coefficient < 0:
        raise ValueError('A monomial block needs a nonnegative coefficient')
    out = word_expression([label] * coefficient)
    for variable in monomial:
        out = Repeat(out, variable)
    return out


def separated_scheme(equations: list[Poly]):
    """One counter per equation; no new repetition parameters.

    Every expansion is lexicographically sorted. All increments precede all
    decrements. Zero-to-zero execution is equivalent to all equations = 0.
    """
    if not equations:
        raise ValueError('Provide at least one equation')
    p = len(equations)
    net = {}
    positive, negative = [], []
    for j, polynomial in enumerate(equations):
        inc, dec = f'a+{j:06d}', f'b-{j:06d}'
        unit = tuple(int(i == j) for i in range(p))
        zero = (0,) * p
        net[inc] = Transition(zero, unit)
        net[dec] = Transition(unit, zero)
        positive.append(sequence(monomial_block(inc, c, m)
                                 for m, c in polynomial.terms.items() if c > 0))
        negative.append(sequence(monomial_block(dec, -c, m)
                                 for m, c in polynomial.terms.items() if c < 0))
    return net, Concat(sequence(positive), sequence(negative))


@dataclass
class QuadraticSystem:
    equations: list[Poly]
    recipes: list[tuple[str, Poly]]
    originals: set[str]

    def lift(self, values: dict[str, int]) -> dict[str, int]:
        if set(values) != self.originals:
            raise ValueError(f'Expected original variables {sorted(self.originals)}')
        if any(type(v) is not int or v < 0 for v in values.values()):
            raise ValueError('Inputs must be natural numbers')
        out = dict(values)
        for name, expression in self.recipes:
            out[name] = expression.value(out)
        return out

    def quartic(self) -> Poly:
        return sum((f*f for f in self.equations), Poly())


def quadratize(polynomial: Poly) -> QuadraticSystem:
    """Unique nonnegative arithmetic-circuit lift; no signed witness pairs."""
    originals = {v for monomial in polynomial.terms for v in monomial}
    equations, recipes = [], []

    def wire(expression):
        expression = Poly.cast(expression)
        i = len(recipes)
        name = f'gate{i}'
        while name in originals:
            name = '_' + name
        var = Poly.var(name)
        recipes.append((name, expression))
        equations.append(var - expression)
        return var

    def half(sign):
        terms = []
        for monomial, coefficient in polynomial.terms.items():
            if sign * coefficient <= 0:
                continue
            c = abs(coefficient)
            factors = [Poly.var(v) for v in monomial]
            if c != 1 or not factors:
                factors.insert(0, Poly.cast(c))
            value = factors[0]
            for factor in factors[1:]:
                value = wire(value * factor)
            terms.append(value)
        if not terms:
            return Poly.cast(0)
        total = terms[0]
        for term in terms[1:]:
            total = wire(total + term)
        return total

    lhs, rhs = half(1), half(-1)
    equations.append(lhs - rhs)
    assert all(f.degree <= 2 for f in equations)
    return QuadraticSystem(equations, recipes, originals)


def repetition_depth(expression) -> int:
    if isinstance(expression, Repeat):
        return 1 + repetition_depth(expression.body)
    if isinstance(expression, Concat):
        return max(repetition_depth(expression.left), repetition_depth(expression.right))
    return 0


def main():
    x, y, z = (Poly.var(v) for v in ('x', 'y', 'z'))
    polynomial = x*y*z + 2*z - x*x - 3
    system = quadratize(polynomial)
    quartic = system.quartic()
    presentations = [([polynomial], 3), (system.equations, 2), ([quartic], 4)]
    compiled = []
    for equations, depth in presentations:
        net, expression = separated_scheme(equations)
        assert repetition_depth(expression) <= depth
        builder = Compiler(net, canonical=True).compile(expression)
        compiled.append((builder, parameters(expression), len(equations)))
    checks = 0
    successes = []
    for values in product(range(4), repeat=3):
        original = dict(zip(('x', 'y', 'z'), values))
        lifted = system.lift(original)
        expected = polynomial.value(original) == 0
        assert (all(f.value(lifted) == 0 for f in system.equations)) == expected
        checks += 1
        for builder, pars, p in compiled:
            inputs = {'k:'+name: lifted[name] for name in pars}
            inputs.update({f'{end}:{j}': 0 for end in ('m', 'n') for j in range(p)})
            assert (builder.energy(builder.construct(inputs)) == 0) == expected
            checks += 1
        changed = dict(lifted)
        changed[system.recipes[0][0]] += 1
        assert not all(f.value(changed) == 0 for f in system.equations)
        checks += 1
        if expected:
            successes.append(original)
    result = {
        'status': 'PASS', 'total_checks': checks,
        'polynomial': 'x*y*z + 2*z - x*x - 3',
        'grid': 'x,y,z in {0,1,2,3}',
        'quadratic_equations': len(system.equations),
        'unique_gate_parameters': len(system.recipes),
        'quartic_degree': quartic.degree,
        'presentations': [
            {'counters': p, 'repetition_depth_bound': bound,
             'witnesses': len(builder.recipes), 'equations': len(builder.residuals)}
            for (builder, _, p), (_, bound) in zip(compiled, presentations)],
        'successful_original_tuples': successes,
        'scope': 'Finite frontend checks; not a formal proof of the general theorems.'
    }
    destination = Path(__file__).resolve().parents[1] / 'verification' / 'substrate_results.json'
    destination.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
