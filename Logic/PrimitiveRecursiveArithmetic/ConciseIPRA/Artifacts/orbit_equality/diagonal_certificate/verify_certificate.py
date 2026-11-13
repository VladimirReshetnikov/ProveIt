#!/usr/bin/env python3
"""Check finite equational derivations for the generic diagonal lemma.

This is an intentionally small, transparent, schematic equational kernel.
It is not a complete iPRA checker and does not evaluate numerical terms.
Its five fixed axiom schemes are stated in AXIOMS below. Induction is only
for a literal equation; the certificate cannot provide other axiom schemes.
"""

import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path


ARITIES = {"0": 0, "S": 1, "F": 2, "W": 2}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def variable_name(value):
    require(type(value) is str and re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", value),
            "invalid variable name")
    return value


def term(raw):
    require(type(raw) is list and len(raw) >= 1 and type(raw[0]) is str,
            "term must be a nonempty tagged array")
    symbol = raw[0]
    if symbol == "v":
        require(len(raw) == 2, "variable has wrong arity")
        return ("v", variable_name(raw[1]))
    require(symbol in ARITIES, "unknown function symbol")
    require(len(raw) == ARITIES[symbol] + 1, "function has wrong arity")
    return (symbol,) + tuple(term(child) for child in raw[1:])


def equation(raw):
    require(type(raw) is list and len(raw) == 2, "equation must have two endpoints")
    return (term(raw[0]), term(raw[1]))


def context(raw):
    require(type(raw) is list, "context must be an array")
    return tuple(equation(item) for item in raw)


def free_variables(t):
    if t[0] == "v":
        return {t[1]}
    answer = set()
    for child in t[1:]:
        answer.update(free_variables(child))
    return answer


def equation_variables(eq):
    return free_variables(eq[0]) | free_variables(eq[1])


def context_variables(gamma):
    answer = set()
    for eq in gamma:
        answer.update(equation_variables(eq))
    return answer


def substitution(raw):
    require(type(raw) is dict, "substitution must be an object")
    return {variable_name(name): term(value) for name, value in raw.items()}


def subst(t, mapping):
    # Terms have no binders. This is simultaneous substitution: an inserted
    # image is not recursively substituted again.
    if t[0] == "v":
        return mapping.get(t[1], t)
    return (t[0],) + tuple(subst(child, mapping) for child in t[1:])


def subst_equation(eq, mapping):
    return (subst(eq[0], mapping), subst(eq[1], mapping))


def v(name):
    return ("v", name)


ZERO = ("0",)


def s(t):
    return ("S", t)


def f(n, u):
    return ("F", n, u)


def w(t, n):
    return ("W", t, n)


ONE = s(ZERO)
n, t, u = v("n"), v("t"), v("u")
AXIOMS = {
    "W0": (w(ZERO, n), ZERO),
    "WS": (w(s(t), n), f(n, w(t, n))),
    "F10": (f(ONE, ZERO), ZERO),
    "FSS0": (f(s(s(n)), ZERO), ONE),
    "FS": (f(s(n), s(u)), s(f(n, u))),
}


@dataclass(frozen=True)
class Judgement:
    assumptions: tuple
    equation: tuple


EXTRA_FIELDS = {
    "axiom": {"name", "substitution"},
    "hypothesis": set(),
    "reflexivity": set(),
    "symmetry": {"premise"},
    "transitivity": {"first", "second"},
    "congruence": {"symbol", "premises"},
    "substitution": {"premise", "substitution"},
    "weakening": {"premise"},
    "induction": {"template", "variable", "eigenvariable", "target", "base", "step"},
}


def verify(document):
    require(type(document) is dict, "certificate must be an object")
    require(set(document) == {"format", "proof", "results"}, "unexpected certificate fields")
    require(document["format"] == "diagonal-equation-v1", "unknown certificate format")
    require(type(document["proof"]) is list, "proof must be an array")
    checked = []
    induction_count = 0

    for index, node in enumerate(document["proof"]):
        try:
            require(type(node) is dict, "proof node must be an object")
            rule = node.get("rule")
            require(type(rule) is str and rule in EXTRA_FIELDS, "unknown rule")
            require(set(node) == {"rule", "context", "equation"} | EXTRA_FIELDS[rule],
                    "unexpected rule fields")
            gamma = context(node["context"])
            eq = equation(node["equation"])

            def prior(ref):
                require(type(ref) is int and 0 <= ref < index,
                        "premise must reference an earlier proof node")
                return checked[ref]

            def in_same_context(ref):
                result = prior(ref)
                require(result.assumptions == gamma, "premise context differs")
                return result.equation

            if rule == "axiom":
                name = node["name"]
                require(type(name) is str and name in AXIOMS, "unknown axiom scheme")
                mapping = substitution(node["substitution"])
                require(set(mapping) == equation_variables(AXIOMS[name]),
                        "axiom must instantiate exactly its schematic variables")
                require(eq == subst_equation(AXIOMS[name], mapping), "wrong axiom instance")
            elif rule == "hypothesis":
                require(eq in gamma, "equation is not an assumption")
            elif rule == "reflexivity":
                require(eq[0] == eq[1], "nonreflexive equation")
            elif rule == "symmetry":
                premise = in_same_context(node["premise"])
                require(eq == (premise[1], premise[0]), "wrong symmetric equation")
            elif rule == "transitivity":
                first = in_same_context(node["first"])
                second = in_same_context(node["second"])
                require(first[1] == second[0] and eq == (first[0], second[1]),
                        "transitivity endpoints do not join")
            elif rule == "congruence":
                symbol = node["symbol"]
                refs = node["premises"]
                require(type(symbol) is str and symbol in ARITIES, "unknown congruence symbol")
                require(type(refs) is list and len(refs) == ARITIES[symbol],
                        "wrong number of congruence premises")
                premises = [in_same_context(ref) for ref in refs]
                expected = ((symbol,) + tuple(p[0] for p in premises),
                            (symbol,) + tuple(p[1] for p in premises))
                require(eq == expected, "wrong congruence conclusion")
            elif rule == "substitution":
                premise = prior(node["premise"])
                mapping = substitution(node["substitution"])
                require(gamma == tuple(subst_equation(p, mapping) for p in premise.assumptions),
                        "substitution did not transform its entire context")
                require(eq == subst_equation(premise.equation, mapping),
                        "wrong substituted equation")
            elif rule == "weakening":
                premise = prior(node["premise"])
                require(all(p in gamma for p in premise.assumptions),
                        "weakening discarded an assumption")
                require(eq == premise.equation, "weakening changed the equation")
            elif rule == "induction":
                template = equation(node["template"])
                variable = variable_name(node["variable"])
                eigen = variable_name(node["eigenvariable"])
                target = term(node["target"])
                forbidden = (context_variables(gamma)
                             | (equation_variables(template) - {variable})
                             | free_variables(target) | {variable})
                require(eigen not in forbidden, "induction eigenvariable is not fresh")
                require(variable not in context_variables(gamma),
                        "induction variable occurs in the fixed context")
                base = prior(node["base"])
                step = prior(node["step"])
                ih = subst_equation(template, {variable: v(eigen)})
                successor = subst_equation(template, {variable: s(v(eigen))})
                require(base.assumptions == gamma
                        and base.equation == subst_equation(template, {variable: ZERO}),
                        "induction base does not match")
                require(step.assumptions == gamma + (ih,) and step.equation == successor,
                        "induction step or its hypothesis does not match")
                require(eq == subst_equation(template, {variable: target}),
                        "induction conclusion does not match")
                induction_count += 1
            checked.append(Judgement(gamma, eq))
        except (TypeError, KeyError, ValueError) as error:
            raise ValueError(f"node {index}: {error}") from error

    results = document["results"]
    require(type(results) is dict and len(results) > 0, "results must name proof nodes")
    named = {}
    for name, ref in results.items():
        variable_name(name)
        require(type(ref) is int and 0 <= ref < len(checked), "invalid result reference")
        require(not checked[ref].assumptions, "a reported theorem still has assumptions")
        named[name] = checked[ref].equation
    return {"proof_nodes": len(checked), "induction_nodes": induction_count,
            "theorems": named}


def main():
    path = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name("certificate.json")
    try:
        result = verify(json.loads(path.read_text()))
    except (OSError, ValueError, TypeError, RecursionError) as error:
        print(f"REJECT: {error}", file=sys.stderr)
        return 1
    print(json.dumps({"status": "ACCEPT", **result}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
