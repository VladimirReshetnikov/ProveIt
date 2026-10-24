#!/usr/bin/env python3
"""Independent exact checks of the local artifact and finite certificate lemmas.

These checks supplement the paper proofs.  They do not prove a consistency
statement, compile a final polynomial, or execute a supposed ZFC refutation.
"""
import hashlib
import itertools
import json
import random
from copy import deepcopy
from math import prod
from pathlib import Path
from core import (parse, psos, pdegree, peval, rows, poly_product_factors,
                  poly_eval, budget_factor, flow_balance, finite_closure,
                  make_certificate, validate_certificate)

HERE = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def implication(a, b):
    return 2 * (a + b) * (a + b + 1) + 4 * b


def relation(a, b):
    return implication(a, b) + 1


def universal(a, b):
    return implication(a, b) + 2


def equality(a, b):
    return implication(a, b) + 3


def negation(a):
    return implication(a, 1)


def existential(a, b):
    return negation(universal(a, negation(b)))


def requirement(b, k, m):
    return universal(b, implication(m, negation(universal(
        b, implication(m, negation(relation(b, k)))))))


def closure(a, b, k, m):
    return universal(b, implication(relation(b, k), negation(universal(
        a, implication(m, negation(universal(a, implication(
            universal(k, implication(relation(k, a), relation(k, b))),
            requirement(b, k, m)))))))))


def bundle(a, b, c):
    return negation(implication(
        implication(relation(a, b), universal(c, relation(a, b))),
        universal(c, implication(closure(a, b, c, c),
                                 negation(requirement(b, c, c))))))


def head(name, a, b, c, d):
    i, a_, e, r, x = implication, universal, equality, relation, existential
    if name == "truth":
        return 0
    if name == "rho1":
        return x(a, e(a, b))
    if name == "rho2":
        return i(a_(a, i(b, c)), i(a_(a, b), a_(a, c)))
    if name == "rho3":
        return i(e(a, b), i(r(c, a), r(c, b)))
    if name == "rho4":
        return i(a_(a, a_(b, c)), a_(b, a_(a, c)))
    if name == "rho5":
        return i(e(c, a), i(r(c, b), r(a, b)))
    if name == "rho6":
        return i(x(a, a_(a, b)), b)
    if name == "growG":
        return i(e(c, a), i(e(c, b), a_(r(a, b), e(a, b))))
    if name == "rho8":
        return i(i(i(c, d), a), i(i(a, c), i(b, c)))
    if name == "bundle":
        return bundle(a, b, c)
    raise ValueError(name)


def check_local():
    obj = json.loads((HERE / "linear_budget_local.json").read_text())
    basis = json.loads((HERE / "horn_source_rows.json").read_text())
    by_name = {b["name"]: b for b in basis["branches"]}
    require(len(obj["witnesses"]) == obj["witness_count"] == 20, "witness list")
    require(len(set(obj["witnesses"])) == 20, "duplicate witness")
    expanded = 0
    cases = 0
    max_bits = 0
    degree_sum = 0
    for branch in obj["branches"]:
        name = branch["name"]
        old = by_name[name]
        require(branch["residuals"][:len(old["residuals"])] == old["residuals"],
                "an inherited row changed")
        sos = psos(parse(r) for r in branch["residuals"])
        require(sos == parse(branch["sum_of_squares"]), "literal SOS mismatch")
        degree = pdegree(sos)
        require(degree == branch["exact_degree"], "branch exact degree")
        degree_sum += degree
        expanded += 1
        allowed = set(obj["witnesses"] + obj["exposed_coordinates"])
        require(all(v in allowed for row in branch["residuals"]
                    for term in row for v in term["monomial"]), "undeclared variable")
        new_rows = branch["residuals"][len(old["residuals"]):]
        require(all(pdegree(parse(r)) <= 2 for r in new_rows), "new row degree")
        inputs = list(itertools.product(range(2), repeat=4))
        if name == "bundle":
            inputs = [(0, 1, 2, 1), (0, 2, 1, 0)]
        for a, b, c, d in inputs:
            env = {v: 0 for v in obj["witnesses"]}
            env.update(a=a, b=b, c=c, d=d)
            if name == "mp":
                env.update(p=a, q=implication(a, b), v=b)
                premises = (env["p"], env["q"])
            elif name == "gen":
                env.update(p=b, q=0, v=universal(a, b))
                premises = (env["p"],)
            else:
                env.update(p=0, q=0, v=head(name, a, b, c, d))
                premises = ()
            # A local zero is made without claiming it lies on a global refutation.
            env.update(M=7, T=3)
            env["S"] = env["M"] + env["v"]
            env["Sp"] = prod(env["M"] + p for p in premises)
            env["Tp"] = env["T"] * budget_factor(premises, env["v"])
            for wire in branch["wires"]:
                env[wire["name"]] = peval(wire["value"], env)
                require(env[wire["name"]] >= 0, "negative natural wire")
            require(all(peval(row, env) == 0 for row in branch["residuals"]),
                    f"failed exact local fixture {name}")
            max_bits = max(max_bits, max(v.bit_length() for v in env.values()))
            mutated = dict(env, Tp=env["Tp"] + 1)
            require(any(peval(row, mutated) != 0 for row in new_rows),
                    "budget mutation accepted in active branch")
            cases += 1
    require(degree_sum == obj["exact_degree"] == 52, "product degree")
    return {"exact_sos_expansions": expanded, "natural_branch_fixtures": cases,
            "fixture_budget_mutations_rejected": cases,
            "largest_fixture_integer_bits": max_bits,
            "local_witnesses": 20, "local_exact_degree": 52}


def check_finite_lemma():
    labels = range(3)
    possible_rules = [(premises, c) for c in labels for arity in range(3)
                      for premises in itertools.product(labels, repeat=arity)]
    checked = identities = 0
    for n in range(4):
        for rules in itertools.product(possible_rules, repeat=n):
            t = prod(budget_factor(p, c) for p, c in rules)
            m = t + 1
            conclusions = [c for p, c in rules]
            premises = [p for pp, c in rules for p in pp]
            cp = poly_product_factors(conclusions)
            qp = poly_product_factors([1] + premises)
            cp += [0] * max(0, len(qp) - len(cp))
            qp += [0] * max(0, len(cp) - len(qp))
            delta = [a - b for a, b in zip(cp, qp)]
            require(all(abs(coef) <= t < m for coef in delta), "coefficient bound")
            numeric = poly_eval(cp, m) == poly_eval(qp, m)
            symbolic = all(coef == 0 for coef in delta)
            balance = not flow_balance(rules)
            require(numeric == symbolic == balance, "injectivity or factor uniqueness")
            if numeric:
                require(1 in finite_closure(rules), "cyclic fake flow proof")
                identities += 1
            checked += 1
    return {"all_rule_lists_length_at_most": 3, "labels": [0, 1, 2],
            "rule_lists_checked": checked, "exact_flow_identities": identities}


def check_certificates():
    examples = [
        [((), 1)],
        [((2, 2), 1), ((), 2), ((), 2)],
        [((0,), 1), ((), 0)],
        [((2, 3), 1), ((0,), 2), ((), 0), ((0, 0), 3), ((), 0), ((), 0)],
    ]
    certs = [make_certificate(example) for example in examples]
    type_rejections = 0
    for cert in certs:
        require(validate_certificate(cert), "constructed proof rejected")
        require(not flow_balance([(tuple(p), c) for p, c in cert["rules"]]), "flow")
        bad = deepcopy(cert)
        bad["M"] += 1
        require(not validate_certificate(bad), "wrong endpoint base accepted")
        if len(cert["S"]) > 2:
            bad = deepcopy(cert)
            bad["S"][1] += 1
            require(not validate_certificate(bad), "mutated path accepted")
        for field in ("target", "M", "S", "T", "conclusion", "premise"):
            for constructor in (float, bool):
                bad = deepcopy(cert)
                if field in ("S", "T"):
                    bad[field][0] = constructor(bad[field][0])
                elif field == "conclusion":
                    bad["rules"][0][1] = constructor(bad["rules"][0][1])
                elif field == "premise":
                    if not bad["rules"][0][0]:
                        continue
                    bad["rules"][0][0][0] = constructor(bad["rules"][0][0][0])
                else:
                    bad[field] = constructor(bad[field])
                require(not validate_certificate(bad), "non-integer certificate accepted")
                type_rejections += 1
    # A finite source with no axiom and only cycles cannot derive the target.
    cyclic = [((1,), 1), ((2,), 1), ((1,), 2)]
    require(1 not in finite_closure(cyclic), "cycle fixture is not negative")
    require(bool(flow_balance(cyclic)), "cycle unexpectedly balanced")
    # Merely making M larger than every label is insufficient.  Both local
    # multiplicative steps are exact, but the budget endpoint detects the fake.
    fake_rules = [((10,), 3), ((), 7)]
    fake = {"target": 1, "M": 11, "S": [12, 18, 1], "T": [1, 14, 112],
            "rules": [[list(p), c] for p, c in fake_rules]}
    require(all(fake["S"][i+1] * (11+c) == fake["S"][i] * prod(11+p for p in pp)
                for i, (pp, c) in enumerate(fake_rules)), "fake lost local property")
    require(11 > max([1] + [c for p, c in fake_rules] +
                     [p for pp, c in fake_rules for p in pp]), "fake scale not large")
    require(1 not in finite_closure(fake_rules), "fake target is derivable")
    require(not validate_certificate(fake), "missing-budget fake not rejected")
    empty = {"target": 1, "M": 2, "S": [1], "T": [1], "rules": []}
    require(not validate_certificate(empty), "empty false refutation accepted")
    (HERE / "TOY_CERTIFICATES.json").write_text(json.dumps({
        "scope": "arbitrary finite Horn systems, never a ZFC refutation",
        "valid": certs, "negative_missing_budget": fake}, indent=2) + "\n")
    return {"toy_proof_trees": len(certs), "zero_label_is_actual_axiom": True,
            "repeated_premise_test": True, "cycle_test": True,
            "empty_target_one_trace_rejected": True,
            "non_integer_certificate_mutations_rejected": type_rejections,
            "fake_large_base_collision_rejected": True}


def check_normalized_quadratic_lift():
    rng = random.Random(10423)
    cases = 0
    for _ in range(2000):
        p, q, c, s, sp, t, tp, m = [rng.randrange(15) for _ in range(8)]
        w, u, up, v = p*q, m*s, m*sp, m*p*q
        rows_ = [w-p*q, u-m*s, up-m*sp, v-m*w,
                 sp+c*up-s-u*(p+q+v), tp-t*(1+p+q+w+c)]
        require(rows_[:4] == [0]*4, "normalization lift definitions")
        require(rows_[4] == sp*(1+m*c)-s*(1+m*p)*(1+m*q), "lift balance identity")
        require(rows_[5] == tp-t*((1+p)*(1+q)+c), "lift budget identity")
        cases += 1
    return {"normalized_lift_exact_identity_fixtures": cases,
            "normalized_lift_auxiliaries": 4, "normalized_lift_rows": 6}


def main():
    result = {"status": "PASS", "scope": "local exact checks and bounded regressions; paper theorem supplies general proof",
              "local": check_local(), "finite_lemma": check_finite_lemma(),
              "certificates": check_certificates(), "optional_lift": check_normalized_quadratic_lift()}
    result["artifact_sha256"] = {name: hashlib.sha256((HERE / name).read_bytes()).hexdigest()
        for name in ["horn_source_rows.json", "linear_budget_local.json", "LOCAL_METRICS.json"]}
    (HERE / "CHECKS.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
