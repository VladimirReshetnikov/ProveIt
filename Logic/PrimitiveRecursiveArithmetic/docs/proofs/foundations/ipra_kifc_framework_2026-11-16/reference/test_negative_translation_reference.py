from __future__ import annotations

import random
import unittest

from reference.negative_translation_reference import (
    All,
    And,
    BOT,
    Const,
    Eq,
    Ex,
    Formula,
    Fun,
    Imp,
    Or,
    Term,
    Var,
    all_environments,
    eval_formula,
    is_qf,
    is_retained,
    negative,
    subst_formula,
)


FUNCTIONS = {
    "succ": lambda xs: xs[0] + 1,
    "add": lambda xs: xs[0] + xs[1],
    "mul": lambda xs: xs[0] * xs[1],
}


def random_term(rng: random.Random, arity: int, depth: int) -> Term:
    if depth <= 0 or rng.random() < 0.45:
        if arity and rng.random() < 0.65:
            return Var(rng.randrange(arity))
        return Const(rng.randrange(4))
    choice = rng.randrange(3)
    if choice == 0:
        return Fun("succ", (random_term(rng, arity, depth - 1),))
    if choice == 1:
        return Fun(
            "add",
            (
                random_term(rng, arity, depth - 1),
                random_term(rng, arity, depth - 1),
            ),
        )
    return Fun(
        "mul",
        (
            random_term(rng, arity, depth - 1),
            random_term(rng, arity, depth - 1),
        ),
    )


def random_formula(
    rng: random.Random,
    arity: int,
    depth: int,
    *,
    allow_quantifiers: bool = True,
) -> Formula:
    if depth <= 0 or rng.random() < 0.28:
        if rng.random() < 0.08:
            return BOT
        return Eq(
            random_term(rng, arity, 2),
            random_term(rng, arity, 2),
        )
    constructors = ["and", "or", "imp"]
    if allow_quantifiers:
        constructors += ["all", "ex"]
    tag = rng.choice(constructors)
    if tag == "all":
        return All(random_formula(rng, arity + 1, depth - 1))
    if tag == "ex":
        return Ex(random_formula(rng, arity + 1, depth - 1))
    left = random_formula(rng, arity, depth - 1, allow_quantifiers=allow_quantifiers)
    right = random_formula(rng, arity, depth - 1, allow_quantifiers=allow_quantifiers)
    if tag == "and":
        return And(left, right)
    if tag == "or":
        return Or(left, right)
    return Imp(left, right)


class NegativeTranslationSyntaxTests(unittest.TestCase):
    def test_substitution_commutes(self) -> None:
        rng = random.Random(20261116)
        for _ in range(250):
            formula = random_formula(rng, arity=3, depth=4)
            substitution = tuple(random_term(rng, arity=2, depth=3) for _ in range(3))
            self.assertEqual(
                negative(subst_formula(formula, substitution)),
                subst_formula(negative(formula), substitution),
            )

    def test_qf_is_preserved(self) -> None:
        rng = random.Random(8128)
        for _ in range(250):
            formula = random_formula(
                rng,
                arity=3,
                depth=5,
                allow_quantifiers=False,
            )
            self.assertTrue(is_qf(formula))
            self.assertTrue(is_qf(negative(formula)))

    def test_retained_classifier(self) -> None:
        atom = Eq(Var(0), Const(0))
        qf_disjunction = Or(atom, Imp(atom, BOT))
        retained = All(Imp(qf_disjunction, And(atom, atom)))
        nonretained = Ex(All(atom))
        self.assertTrue(is_retained(qf_disjunction))
        self.assertTrue(is_retained(retained))
        self.assertFalse(is_retained(nonretained))


class NegativeTranslationFiniteModelTests(unittest.TestCase):
    def test_classical_equivalence_on_random_finite_models(self) -> None:
        rng = random.Random(271828)
        domain = (0, 1, 2)
        for _ in range(120):
            formula = random_formula(rng, arity=2, depth=4)
            translated = negative(formula)
            for environment in all_environments(domain, 2):
                self.assertEqual(
                    eval_formula(formula, environment, domain, FUNCTIONS),
                    eval_formula(translated, environment, domain, FUNCTIONS),
                )

    def test_existential_translation_shape(self) -> None:
        atom = Eq(Var(0), Const(1))
        self.assertEqual(negative(Ex(atom)), Imp(All(Imp(atom, BOT)), BOT))

    def test_disjunction_translation_shape(self) -> None:
        left = Eq(Var(0), Const(0))
        right = Eq(Var(0), Const(1))
        self.assertEqual(
            negative(Or(left, right)),
            Imp(And(Imp(left, BOT), Imp(right, BOT)), BOT),
        )


if __name__ == "__main__":
    unittest.main()
