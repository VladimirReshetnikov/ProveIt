#!/usr/bin/env python3
"""Independent finite controls and constructor metadata; never invokes Lean.

The universal arguments are in README.md. Exhaustive controls are not their
proof. All checks use explicit exceptions so python -O preserves them.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from hashlib import sha256
from itertools import combinations_with_replacement, product
import json
from math import gcd, lcm
from pathlib import Path
import re
import sys


HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent.parent
REPO = RESEARCH.parent.parent
DIRECT = RESEARCH / "con-zfc-diophantine-forms/68-joint-positivity/direct"
LEAN = RESEARCH / "Lean/DiophantineConsistency"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def mul_poly(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out)


def factor_poly(labels):
    out = (1,)
    for j in labels:
        out = mul_poly(out, (1, j))
    return out


def eval_poly(p, x):
    out = 0
    for c in reversed(p):
        out = c + x * out
    return out


def positive_labels(labels):
    return tuple(j for j in labels if j)


def carrier_controls():
    outputs = premises = coincidences = degree_exclusions = 0
    for m in range(1, 9):
        for t in range(1, 5):
            carrier = (m + 1) ** t
            by_value = {}
            for cs in combinations_with_replacement(range(m + 1), t):
                a = factor_poly(cs)
                require(max(a) < carrier, "output coefficient bound")
                value = eval_poly(a, carrier)
                require(value not in by_value, "distinct output multisets collide")
                by_value[value] = (positive_labels(cs), a)
                outputs += 1
            for ps in combinations_with_replacement(range(m + 1), 2 * t):
                c = factor_poly((1,) + ps)
                value = eval_poly(c, carrier)
                if len(c) - 1 > t:
                    require(value > (1 + m * carrier) ** t, "degree separation")
                    degree_exclusions += 1
                else:
                    require(max(c) < carrier, "bounded-degree premise coefficient bound")
                if value in by_value:
                    labels, a = by_value[value]
                    require(a == c, "evaluation equality failed polynomial identity")
                    require(labels == tuple(sorted((1,) + positive_labels(ps))),
                            "flow multiplicities differ")
                    coincidences += 1
                premises += 1
    signed = 0
    for radix in range(2, 7):
        for coefficients in product(range(1 - radix, radix), repeat=4):
            require((eval_poly(coefficients, radix) == 0) == (not any(coefficients)),
                    "strict signed-digit uniqueness")
            signed += 1
        require(eval_poly((0, radix, -1), radix) == 0,
                "non-strict-bound negative control")
    # Each is a spurious target1 balance, and an actual one-step accumulator
    # certificate for the unproductive rule (1,0)->M+2, if M is unrestricted.
    for carrier in range(1, 21):
        conclusion = carrier + 2
        require(1 + conclusion * carrier == (1 + carrier) ** 2,
                "small-carrier collision control")
        require(factor_poly((conclusion,)) != factor_poly((1, 1)),
                "negative control accidentally has polynomial balance")
    return dict(output_multisets=outputs, premise_multisets=premises,
                exact_balances=coincidences, degree_exclusions=degree_exclusions,
                signed_digit_cases=signed, small_carrier_negative_controls=20,
                nonstrict_digit_negative_controls=5)


def trace_fixture():
    # Derive1 using (2,3)->1 followed by the two axioms (0,0)->2,3.
    m, t = 4, 3
    carrier = (m + 1) ** t
    f = lambda j: 1 + j * carrier
    rules = [(2, 3, 1), (0, 0, 2), (0, 0, 3)]
    states = [f(1), f(2) * f(3), f(3), 1]
    scale = lcm(*range(1, t + 2)) * (max(states) + 1)
    moduli = [1 + (i + 1) * scale for i in range(t + 1)]
    require(all(gcd(a, b) == 1 for i, a in enumerate(moduli) for b in moduli[:i]),
            "CRT moduli not coprime")
    x, modulus = 0, 1
    for residue, nxt in zip(states, moduli):
        x += modulus * (((residue - x) * pow(modulus, -1, nxt)) % nxt)
        modulus *= nxt
    require([x % d for d in moduli] == states, "CRT trace mismatch")
    all_residuals = []
    for i, (p, q, c) in enumerate(rules):
        s, sn = states[i:i + 2]
        d = moduli[i]
        u, v = x // d, x // (d + scale)
        r, rn = d - s - 1, d + scale - sn - 1
        residuals = [d - ((i + 1) * scale + 1), x - s - d * u,
                     s + r + 1 - d, x - sn - (d + scale) * v,
                     sn + rn + 1 - (d + scale)]
        require(min(u, v, r, rn) >= 0 and not any(residuals), "beta residual fixture")
        require(sn * f(c) == s * f(p) * f(q), "accumulator update fixture")
        all_residuals.extend(residuals)
    # New carrier need not satisfy the old divisibility condition, nor make
    # all label weights pairwise coprime.
    require(carrier % 2 != 0 and gcd(f(1), f(3)) == 2,
            "fixture must distinguish the two carrier mechanisms")
    m0 = carrier - 1
    d = moduli[-1]
    endpoint = [d - ((t + 1) * scale + 1),
                x - (m0 + 2) - (scale + 1) * (x // (scale + 1)),
                m0 + ((scale + 1) - states[0] - 1) + 2 - scale,
                x - 1 - d * (x // d), (d - 2) + 2 - d]
    require(not any(endpoint), "endpoint residual fixture")
    # Endpoints alone exclude t=0. If m=0, all three labels are0 and each
    # update forces the state to be constant, contradicting these endpoints.
    for bound in range(1, 21):
        require(bound + 1 != 1, "degenerate endpoint exclusion")
    return dict(m=m, t=t, carrier=carrier, states=states, beta_x=x, beta_y=scale,
                beta_moduli=moduli, new_quadratic_residuals=all_residuals,
                endpoint_residuals=endpoint, gcd_weight1_weight3=2,
                old_common_multiple_condition=False)


def split_add(a, b):
    return 2 + a + b


def split_mul(a, b):
    return 6 + 2 * a + 2 * b


def rows_size(rows):
    terms = []
    for row in rows:
        s = 2
        for _ in row["monomial"]:
            s = split_mul(s, 2)
        terms.append(s)
    if not terms:
        return 2
    out = terms[0]
    for s in terms[1:]:
        out = split_add(out, s)
    return out


def read_quartic_rows():
    """Parse only the completely literal generated monomial grammar."""
    out = []
    for line in (DIRECT / "AffineProductEquation.lean").read_text().splitlines():
        found = re.fullmatch(r"  let r(\d+) : Expr \(Fin 4 ⊕ Fin 97\) := (.*)", line)
        if found is None:
            continue
        require(int(found[1]) == len(out), "nonsequential source residuals")
        rows = []
        for term in found[2].split(" + "):
            coefficient = re.search(r"\.constant \((-?\d+) : ℤ\)", term)
            require(coefficient is not None, "missing literal coefficient")
            variables = re.findall(r"\.var \(\.in([lr]) (\d+)\)", term)
            reconstructed = "(" + " * ".join(
                [f"(.constant ({coefficient[1]} : ℤ))"] +
                [f"(.var (.in{side} {index}))" for side, index in variables]) + ")"
            require(term == reconstructed, "unrecognized arithmetic syntax")
            rows.append(dict(coefficient=int(coefficient[1]), monomial=variables))
        require(all(len(row["monomial"]) <= 2 for row in rows), "source is not quadratic")
        out.append(rows)
    require(len(out) == 92, "expected92 literal source residuals")
    return out


@dataclass(frozen=True)
class RepSize:
    witnesses: int
    split_size: int

    def conjunction(self, other):
        return RepSize(self.witnesses + other.witnesses,
                       14 + 4 * self.split_size + 4 * other.split_size)


ATOM = RepSize(0, 6)  # Graph coordinate/constant: var-atom.


def predicate_compose(rep, graphs):
    rows = RepSize(0, 6)  # Rep.equality0 0.
    for graph in reversed(graphs):
        rows = graph.conjunction(rows)
    joined = rep.conjunction(rows)
    return RepSize(joined.witnesses + len(graphs), joined.split_size)


def graph_add(r, s):
    return RepSize(r.witnesses + s.witnesses + 2,
                   230 + 4 * r.split_size + 16 * s.split_size)


def graph_mul(r, s):
    return RepSize(r.witnesses + s.witnesses + 2,
                   358 + 4 * r.split_size + 16 * s.split_size)


def beta_size(index):
    denominator = graph_add(graph_mul(graph_add(index, ATOM), ATOM), ATOM)
    return predicate_compose(RepSize(2, 286), [ATOM, ATOM, denominator])


def forall_count(rep):
    m, s = rep.witnesses, rep.split_size
    return m * (4 * s + 11790) + 10 * s + 20674


def constructor_metadata():
    shared = json.loads((DIRECT / "affine_shared_step.json").read_text())
    hs = [rows_size(b["sum_of_squares"]) for b in shared["horn_source"]["branches"]]
    es = [rows_size(r) for r in shared["extra_residuals"]]
    shared_size = hs[0]
    for s in hs[1:]:
        shared_size = split_mul(shared_size, s)
    for s in es:
        shared_size = split_add(shared_size, split_mul(s, s))
    quartic_rows = read_quartic_rows()
    qs = [rows_size(rows) for rows in quartic_rows]
    quartic_size = split_mul(qs[0], qs[0])
    for s in qs[1:]:
        quartic_size = split_add(quartic_size, split_mul(s, s))
    current, nxt = beta_size(ATOM), beta_size(graph_add(ATOM, ATOM))
    body_old = predicate_compose(RepSize(23, shared_size + 4), [current, nxt, ATOM, ATOM])
    old_steps = forall_count(body_old)
    multiple = RepSize(1, 34)
    old_multiple = forall_count(multiple)
    old_endpoints = 3 + current.witnesses + current.witnesses
    old_closed = old_steps + old_multiple + old_endpoints + 5
    # Five new quadratic residuals, in README order. Each is squared and
    # appended to the original92-residual sum; equality-to0 contributes4.
    beta_residual_sizes = [30, 22, 14, 30, 18]
    new_size = quartic_size
    for s in beta_residual_sizes:
        new_size = split_add(new_size, split_mul(s, s))
    new_body = RepSize(104, new_size + 4)
    new_steps = forall_count(new_body)
    new_closed = new_steps + 111 + 5 + 5
    require((shared_size, quartic_size, new_body.split_size) ==
            (34389014, 107934, 108434), "literal-source metadata regression")
    require(old_multiple == 32940, "common-multiple count regression")
    require(old_closed == 140639095370 and new_closed == 47439839,
            "whole supplied-constructor count regression")
    return dict(source_rows=92, source_witnesses=97, source_degree_at_most=4,
                shared23_step_polynomial_split_size=shared_size,
                quartic97_step_polynomial_split_size=quartic_size,
                current_beta=current.__dict__, next_beta=nxt.__dict__,
                old_bounded_body=body_old.__dict__, old_step_block_witnesses=old_steps,
                removed_common_multiple_witnesses=old_multiple,
                old_endpoint_witnesses=old_endpoints, old_closed_rep_witnesses=old_closed,
                new_beta_quadratic_residual_split_sizes=beta_residual_sizes,
                new_bounded_body=new_body.__dict__, new_step_block_witnesses=new_steps,
                new_power_witnesses_by_literal_input_substitution=111,
                new_power_witnesses_if_using_three_input_compose=114,
                new_endpoint_witnesses=5, outer_witnesses=5,
                new_closed_rep_witnesses=new_closed,
                representation_witness_reduction=old_closed - new_closed,
                final_quartic_variable_count=None,
                final_ordinary_polynomial_materialized=False,
                newly_lean_checked=False)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    sources = [DIRECT / name for name in ["AffineProductEquation.lean",
               "SharedAffineProductEquation.lean", "affine_shared_step.json",
               "AFFINE_PRODUCT_CERTIFICATES.md", "COMMUTATIVE_CERTIFICATES.md"]]
    sources += [LEAN / name for name in ["Representation.lean", "RepresentationSize.lean",
                "ComposeRepresentation.lean", "ArithmeticRepresentation.lean",
                "RemainderRepresentation.lean", "PowerRepresentation.lean",
                "BoundedForallDepth.lean", "BoundedForallSize.lean", "PolynomialGraph.lean"]]
    receipt = dict(status="PASS", optimized=not __debug__, python=sys.version.split()[0],
                   provenance={str(p.relative_to(REPO)): sha256(p.read_bytes()).hexdigest()
                               for p in sources},
                   verifier_sha256=sha256(Path(__file__).read_bytes()).hexdigest(),
                   finite_controls=carrier_controls(), trace_fixture=trace_fixture(),
                   constructor_metadata=constructor_metadata(),
                   scope="ordinary mathematics and finite Python controls; no Lean builds or edits")
    encoded = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(encoded)
    else:
        print(encoded, end="")


if __name__ == "__main__":
    main()
