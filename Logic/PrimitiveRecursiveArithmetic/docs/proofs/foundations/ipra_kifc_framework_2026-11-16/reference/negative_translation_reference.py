"""Finite syntax reference for the retained negative-translation layer.

This module is *not* a proof of the object-theory theorems.  It independently
checks the syntax transformations used by the human proof and Lean blueprint:

* atom-preserving Goedel--Gentzen translation;
* simultaneous substitution under de Bruijn binders;
* preservation of quantifier-freeness;
* the syntactic retained fragment; and
* classical equivalence of a formula with its translation on finite models.

The Lean implementation must still construct ``Prf PRAAx`` derivations.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Callable, Mapping, Sequence, TypeAlias


@dataclass(frozen=True)
class Var:
    index: int

    def __post_init__(self) -> None:
        if self.index < 0:
            raise ValueError("de Bruijn index must be nonnegative")


@dataclass(frozen=True)
class Const:
    value: int


@dataclass(frozen=True)
class Fun:
    name: str
    args: tuple["Term", ...]


Term: TypeAlias = Var | Const | Fun


@dataclass(frozen=True)
class Eq:
    left: Term
    right: Term


@dataclass(frozen=True)
class Bot:
    pass


@dataclass(frozen=True)
class And:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Or:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class Imp:
    left: "Formula"
    right: "Formula"


@dataclass(frozen=True)
class All:
    body: "Formula"


@dataclass(frozen=True)
class Ex:
    body: "Formula"


Formula: TypeAlias = Eq | Bot | And | Or | Imp | All | Ex

BOT = Bot()


def neg(formula: Formula) -> Formula:
    return Imp(formula, BOT)


def negative(formula: Formula) -> Formula:
    """Atom-preserving negative translation used in the report."""
    match formula:
        case Eq():
            return formula
        case Bot():
            return BOT
        case And(left, right):
            return And(negative(left), negative(right))
        case Or(left, right):
            return neg(And(neg(negative(left)), neg(negative(right))))
        case Imp(left, right):
            return Imp(negative(left), negative(right))
        case All(body):
            return All(negative(body))
        case Ex(body):
            return neg(All(neg(negative(body))))
    raise TypeError(f"unknown formula: {formula!r}")


def shift_term(term: Term, amount: int = 1, cutoff: int = 0) -> Term:
    """Shift free indices at or above ``cutoff`` by ``amount``."""
    if amount < 0:
        raise ValueError("this reference implementation only shifts upward")
    match term:
        case Var(index):
            return Var(index + amount) if index >= cutoff else term
        case Const():
            return term
        case Fun(name, args):
            return Fun(name, tuple(shift_term(arg, amount, cutoff) for arg in args))
    raise TypeError(f"unknown term: {term!r}")


def subst_term(term: Term, substitution: Sequence[Term]) -> Term:
    """Simultaneous substitution for all free variables in a term."""
    match term:
        case Var(index):
            if index >= len(substitution):
                raise IndexError(
                    f"variable {index} outside substitution of size {len(substitution)}"
                )
            return substitution[index]
        case Const():
            return term
        case Fun(name, args):
            return Fun(name, tuple(subst_term(arg, substitution) for arg in args))
    raise TypeError(f"unknown term: {term!r}")


def lifted(substitution: Sequence[Term]) -> tuple[Term, ...]:
    """Lift a simultaneous substitution through one de Bruijn binder."""
    return (Var(0),) + tuple(shift_term(term) for term in substitution)


def subst_formula(formula: Formula, substitution: Sequence[Term]) -> Formula:
    match formula:
        case Eq(left, right):
            return Eq(subst_term(left, substitution), subst_term(right, substitution))
        case Bot():
            return BOT
        case And(left, right):
            return And(
                subst_formula(left, substitution),
                subst_formula(right, substitution),
            )
        case Or(left, right):
            return Or(
                subst_formula(left, substitution),
                subst_formula(right, substitution),
            )
        case Imp(left, right):
            return Imp(
                subst_formula(left, substitution),
                subst_formula(right, substitution),
            )
        case All(body):
            return All(subst_formula(body, lifted(substitution)))
        case Ex(body):
            return Ex(subst_formula(body, lifted(substitution)))
    raise TypeError(f"unknown formula: {formula!r}")


def is_qf(formula: Formula) -> bool:
    match formula:
        case Eq() | Bot():
            return True
        case And(left, right) | Or(left, right) | Imp(left, right):
            return is_qf(left) and is_qf(right)
        case All() | Ex():
            return False
    raise TypeError(f"unknown formula: {formula!r}")


def is_retained(formula: Formula) -> bool:
    """The first retained class from the report.

    Every quantifier-free formula is retained.  Beyond that base, the class is
    closed under conjunction, implication, and universal quantification.
    """
    if is_qf(formula):
        return True
    match formula:
        case And(left, right) | Imp(left, right):
            return is_retained(left) and is_retained(right)
        case All(body):
            return is_retained(body)
        case _:
            return False


TermFunction = Callable[[tuple[int, ...]], int]


def eval_term(
    term: Term,
    environment: Sequence[int],
    functions: Mapping[str, TermFunction],
) -> int:
    match term:
        case Var(index):
            return environment[index]
        case Const(value):
            return value
        case Fun(name, args):
            if name not in functions:
                raise KeyError(f"missing interpretation for function {name!r}")
            return functions[name](
                tuple(eval_term(arg, environment, functions) for arg in args)
            )
    raise TypeError(f"unknown term: {term!r}")


def eval_formula(
    formula: Formula,
    environment: Sequence[int],
    domain: Sequence[int],
    functions: Mapping[str, TermFunction],
) -> bool:
    """Classical finite-model evaluation, used only as a regression oracle."""
    match formula:
        case Eq(left, right):
            return eval_term(left, environment, functions) == eval_term(
                right, environment, functions
            )
        case Bot():
            return False
        case And(left, right):
            return eval_formula(left, environment, domain, functions) and eval_formula(
                right, environment, domain, functions
            )
        case Or(left, right):
            return eval_formula(left, environment, domain, functions) or eval_formula(
                right, environment, domain, functions
            )
        case Imp(left, right):
            return (not eval_formula(left, environment, domain, functions)) or eval_formula(
                right, environment, domain, functions
            )
        case All(body):
            return all(
                eval_formula(body, (value, *environment), domain, functions)
                for value in domain
            )
        case Ex(body):
            return any(
                eval_formula(body, (value, *environment), domain, functions)
                for value in domain
            )
    raise TypeError(f"unknown formula: {formula!r}")


def all_environments(domain: Sequence[int], arity: int) -> tuple[tuple[int, ...], ...]:
    if arity < 0:
        raise ValueError("arity must be nonnegative")
    return tuple(product(domain, repeat=arity))
