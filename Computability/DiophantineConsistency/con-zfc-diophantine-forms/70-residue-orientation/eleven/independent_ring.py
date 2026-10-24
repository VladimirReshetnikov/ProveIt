#!/usr/bin/env python3
"""Independent sparse-ring audit; does not import the construction builder.

This checks finite polynomial and coefficient claims, not the unbounded
Pell/compiler argument. Uses only the Python standard library.
"""
from pathlib import Path
import ast
import gzip
import hashlib
import json

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def read(name):
    return json.loads((ROOT / name).read_text())


class Ring:
    """Sparse integer polynomials with sorted (variable, exponent) keys."""
    def __init__(self, terms):
        self.terms = {m: c for m, c in terms.items() if c}

    @classmethod
    def numeral(cls, value):
        return cls({(): value})

    @classmethod
    def variable(cls, name):
        return cls({((name, 1),): 1})

    def __add__(self, other):
        if isinstance(other, int):
            other = Ring.numeral(other)
        result = self.terms.copy()
        for m, c in other.terms.items():
            result[m] = result.get(m, 0) + c
        return Ring(result)

    __radd__ = __add__

    def __neg__(self):
        return Ring({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        if isinstance(other, int):
            other = Ring.numeral(other)
        return self + (-other)

    def __rsub__(self, other):
        return -self + other

    def __mul__(self, other):
        if isinstance(other, int):
            other = Ring.numeral(other)
        result = {}
        for m, c in self.terms.items():
            for n, d in other.terms.items():
                powers = dict(m)
                for x, p in n:
                    powers[x] = powers.get(x, 0) + p
                key = tuple(sorted(powers.items()))
                result[key] = result.get(key, 0) + c * d
        return Ring(result)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, 'invalid exponent')
        result = Ring.numeral(1)
        for _ in range(exponent):
            result = result * self
        return result

    def __eq__(self, other):
        if isinstance(other, int):
            other = Ring.numeral(other)
        return self.terms == other.terms

    def variables(self):
        return {name for monomial in self.terms for name, _ in monomial}

    def degree(self, variables):
        return max(sum(p for name, p in monomial if name in variables)
                   for monomial in self.terms)

    def coefficient(self, unknown_monomial, variables):
        result = {}
        wanted = tuple(sorted(unknown_monomial.items()))
        for monomial, value in self.terms.items():
            projected = tuple((name, p) for name, p in monomial if name in variables)
            if projected == wanted:
                fixed = tuple((name, p) for name, p in monomial if name not in variables)
                result[fixed] = value
        return Ring(result)


def expand(expression, symbols):
    def visit(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return Ring.numeral(node.value)
        if isinstance(node, ast.Name):
            return symbols[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -visit(node.operand)
        if isinstance(node, ast.BinOp):
            left = visit(node.left)
            if isinstance(node.op, ast.Pow):
                require(isinstance(node.right, ast.Constant), 'nonliteral exponent')
                return left ** node.right.value
            right = visit(node.right)
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.Sub):
                return left - right
            if isinstance(node.op, ast.Mult):
                return left * right
        raise RuntimeError('nonpolynomial syntax')
    return visit(ast.parse(expression, mode='eval').body)

