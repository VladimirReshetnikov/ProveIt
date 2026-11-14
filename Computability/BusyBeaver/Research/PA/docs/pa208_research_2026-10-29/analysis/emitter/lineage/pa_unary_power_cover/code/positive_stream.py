#!/usr/bin/env python3
"""Total positive theorem stream for the PA-calibrated raw axiom emitter.

This is a reference semidecision algorithm, not a Turing-machine table.
Every natural description denotes a theorem; failed MP and distribution
side conditions return the identity theorem. The target is code 0, the
open atom E(v0,v0), not a falsity constructor.
"""
from __future__ import annotations
import argparse
from functools import lru_cache
import json
from pathlib import Path

from frozen_positive_emitter import pair, unpair, R, A, I, emit, emit_polynomial, decode, encode, fields


def require(condition, message):
    if not condition:
        raise ValueError(message)


def nat(value):
    return type(value) is int and value >= 0


@lru_cache(maxsize=None)
def free_variables(tree):
    if tree[0] == "E":
        return frozenset(tree[1:])
    if tree[0] == "A":
        return free_variables(tree[2]) - {tree[1]}
    return free_variables(tree[1]) | free_variables(tree[2])


@lru_cache(maxsize=None)
def all_variables(tree):
    if tree[0] == "E":
        return frozenset(tree[1:])
    if tree[0] == "A":
        return all_variables(tree[2]) | {tree[1]}
    return all_variables(tree[1]) | all_variables(tree[2])


def rename_bound_body(tree, old, fresh):
    """Rename occurrences governed by an enclosing old-binder only."""
    if tree[0] == "E":
        return ("E", *(fresh if v == old else v for v in tree[1:]))
    if tree[0] == "A":
        if tree[1] == old:
            return tree
        return ("A", tree[1], rename_bound_body(tree[2], old, fresh))
    return ("I", rename_bound_body(tree[1], old, fresh),
            rename_bound_body(tree[2], old, fresh))


def substitute(tree, old, replacement):
    """Capture-avoiding replacement of free variable old by replacement."""
    if old == replacement or old not in free_variables(tree):
        return tree
    if tree[0] == "E":
        return ("E", *(replacement if v == old else v for v in tree[1:]))
    if tree[0] == "I":
        return ("I", substitute(tree[1], old, replacement),
                substitute(tree[2], old, replacement))
    binder, body = tree[1:]
    if binder == old:
        return tree
    if binder == replacement:
        fresh = 1 + max(all_variables(tree) | {old, replacement})
        body = rename_bound_body(body, binder, fresh)
        binder = fresh
    return ("A", binder, substitute(body, old, replacement))


def substitute_code(formula, old, replacement):
    return encode(substitute(decode(formula), old, replacement))


IDENTITY = I(0, 0)


def description(tag, a, b):
    require(nat(tag) and tag < 8 and nat(a) and nat(b), "invalid description fields")
    return 1 + 8 * pair(a, b) + tag


class TheoremStream:
    """Evaluate a finite dependency DAG, rather than all preceding integers."""
    def __init__(self):
        self.values = {0: IDENTITY}

    def value(self, index):
        require(nat(index), "description index must be a natural number")
        stack = [index]
        while stack:
            q = stack[-1]
            if q in self.values:
                stack.pop()
                continue
            payload, tag = divmod(q - 1, 8)
            a, b = unpair(payload)
            dependencies = (a, b) if tag == 6 else ((b,) if tag == 7 else ())
            missing = [d for d in dependencies if d not in self.values]
            if missing:
                require(all(d < q for d in missing), "nondecreasing description")
                stack.extend(missing)
                continue
            if tag == 0:
                out = I(a, I(b, a))
            elif tag == 1:
                c, d = unpair(b)
                out = I(I(a, I(c, d)), I(I(a, c), I(a, d)))
            elif tag == 2:
                out = I(I(I(a, b), a), a)
            elif tag == 3:
                formula, term = unpair(b)
                out = I(A(a, formula), substitute_code(formula, a, term))
            elif tag == 4:
                formula, conclusion = unpair(b)
                if a not in free_variables(decode(formula)):
                    out = I(A(a, I(formula, conclusion)), I(formula, A(a, conclusion)))
                else:
                    out = IDENTITY
            elif tag == 5:
                # The theorem stream executes the division-free program;
                # the independent certificate checker retains the constructor
                # reference emit() when verifying its nonlogical axiom lines.
                out = emit_polynomial(a)
            elif tag == 6:
                kind, antecedent, conclusion = fields(self.values[a])
                out = conclusion if kind == "I" and antecedent == self.values[b] else IDENTITY
            else:
                out = A(a, self.values[b])
            self.values[q] = out
            stack.pop()
        return self.values[index]


def check_certificate(commands):
    """Independent explicit proof checker; no extra nonlogical axioms allowed.

    Certificate arguments are formula codes or variable names as documented
    by their operation. MP and GEN use zero-based earlier-line indices.
    Every command also includes its claimed exact numerical conclusion.
    """
    require(type(commands) is list and bool(commands), "proof must be a nonempty list")
    lines = []
    for command in commands:
        require(type(command) is dict and set(command) == {"op", "args", "claim"},
                "invalid command fields")
        op, args, claim = command["op"], command["args"], command["claim"]
        arities = {"K": 2, "S": 3, "P": 2, "UI": 3, "QD": 3,
                   "AX": 1, "MP": 2, "GEN": 2}
        require(op in arities and type(args) is list and len(args) == arities[op],
                "invalid operation or arity")
        require(all(nat(v) for v in args) and nat(claim), "non-natural argument")
        if op == "K":
            a, b = args
            expected = I(a, I(b, a))
        elif op == "S":
            a, b, c = args
            expected = I(I(a, I(b, c)), I(I(a, b), I(a, c)))
        elif op == "P":
            a, b = args
            expected = I(I(I(a, b), a), a)
        elif op == "UI":
            v, f, t = args
            expected = I(A(v, f), substitute_code(f, v, t))
        elif op == "QD":
            v, f, g = args
            require(v not in free_variables(decode(f)), "distribution side condition")
            expected = I(A(v, I(f, g)), I(f, A(v, g)))
        elif op == "AX":
            expected = emit(args[0])
        elif op == "MP":
            i, j = args
            require(i < len(lines) and j < len(lines), "MP requires earlier lines")
            kind, a, b = fields(lines[i])
            require(kind == "I" and a == lines[j], "MP formulas do not match")
            expected = b
        else:
            i, v = args
            require(i < len(lines), "GEN requires an earlier line")
            expected = A(v, lines[i])
        require(expected == claim, "claimed conclusion mismatch")
        lines.append(expected)
    return lines


def compile_certificate(commands):
    lines = check_certificate(commands)
    indices = []
    for command in commands:
        op, args = command["op"], command["args"]
        if op == "K": q = description(0, *args)
        elif op == "S": q = description(1, args[0], pair(args[1], args[2]))
        elif op == "P": q = description(2, *args)
        elif op == "UI": q = description(3, args[0], pair(args[1], args[2]))
        elif op == "QD": q = description(4, args[0], pair(args[1], args[2]))
        elif op == "AX": q = description(5, args[0], 0)
        elif op == "MP": q = description(6, indices[args[0]], indices[args[1]])
        else: q = description(7, args[1], indices[args[0]])
        indices.append(q)
    stream = TheoremStream()
    for index, line in zip(indices, lines):
        require(stream.value(index) == line, "certificate/stream disagreement")
    return indices


def command(op, args, claim):
    return {"op": op, "args": list(args), "claim": claim}


def identity_certificate(a):
    b = I(a, a)
    first = I(a, I(b, a))
    second = I(a, I(a, a))
    third = I(first, I(second, b))
    return [command("K", (a, b), first), command("K", (a, a), second),
            command("S", (a, b, a), third), command("MP", (2, 0), I(second, b)),
            command("MP", (3, 1), b)]


def suite():
    certificates = {}
    for a in (0, 1, 2, 3, 7, 33):
        proof = identity_certificate(a)
        compile_certificate(proof)
        require(check_certificate(proof)[-1] == I(a, a), "wrong identity target")
        certificates[f"identity_{a}"] = proof
    # Capture is avoided: free v0 is substituted by v1 below a v1-binder.
    f = encode(("A", 1, ("E", 0, 1)))
    replacement = substitute_code(f, 0, 1)
    require(decode(replacement) == ("A", 2, ("E", 1, 2)), "capture avoidance")
    proof = [command("UI", (0, f, 1), I(A(0, f), replacement))]
    compile_certificate(proof)
    certificates["capture_avoiding_UI"] = proof
    # Derive vacuity from identity, generalization, and the single QD family.
    proof = identity_certificate(0)
    gen = A(1, I(0, 0))
    vacuity = I(0, A(1, 0))
    proof += [command("GEN", (4, 1), gen),
              command("QD", (1, 0, 0), I(gen, vacuity)),
              command("MP", (6, 5), vacuity)]
    compile_certificate(proof)
    require(check_certificate(proof)[-1] == vacuity, "wrong vacuity target")
    certificates["derived_vacuity"] = proof
    for n in (0, 1, 2, 27, 33, 128):
        proof = [command("AX", (n,), emit(n))]
        compile_certificate(proof)
        certificates[f"raw_axiom_{n}"] = proof
    # Substituting the source by the output label forces output-binder
    # alpha conversion inside a nonlogical instance.
    raw = emit(27)
    closed_source = A(0, raw)
    renamed = substitute_code(raw, 0, 27)
    require(27 in free_variables(decode(renamed)), "source was not re-instantiated")
    proof = [command("AX", (27,), raw), command("GEN", (0, 0), closed_source),
             command("UI", (0, raw, 27), I(closed_source, renamed)),
             command("MP", (2, 1), renamed)]
    compile_certificate(proof)
    certificates["raw_axiom_reinstantiation"] = proof
    peirce = [command("P", (0, 1), I(I(I(0, 1), 0), 0))]
    compile_certificate(peirce)
    certificates["Peirce"] = peirce
    # Check finite semantics of logical instances on arbitrary structures,
    # not on alleged finite models of the full nonlogical schema.
    from itertools import product
    from frozen_positive_emitter import evaluate
    semantic_checks = 0
    for name, proof in certificates.items():
        if name.startswith("raw_axiom_"):
            continue
        formula = decode(proof[-1]["claim"])
        names = sorted(free_variables(formula))
        for size in (1, 2):
            for relation in range(1 << (size * size)):
                for values in product(range(size), repeat=len(names)):
                    require(evaluate(formula, size, relation, dict(zip(names, values))),
                            "logical certificate has a finite countermodel")
                    semantic_checks += 1
    controls = []
    wrong = json.loads(json.dumps(certificates["identity_0"]))
    wrong[-1]["claim"] = 0
    controls.append(("wrong target", wrong))
    controls.append(("free variable distribution", [command("QD", (0, 0, 1), 0)]))
    controls.append(("forward proof reference", [command("MP", (1, 0), 0)]))
    controls.append(("Boolean as natural", [command("AX", (True,), emit(1))]))
    controls.append(("unauthorized axiom", [{"op": "ASSUME", "args": [0], "claim": 0}]))
    controls.append(("empty certificate", []))
    wrong_capture = [command("UI", (0, f, 1), I(A(0, f), encode(("A", 1, ("E", 1, 1)))))]
    controls.append(("capturing substitution", wrong_capture))
    for name, proof in controls:
        try:
            check_certificate(proof)
        except ValueError:
            pass
        else:
            raise ValueError(f"invalid control accepted: {name}")
    stream = TheoremStream()
    require(stream.value(description(6, 0, 0)) == IDENTITY, "MP default")
    require(stream.value(description(4, 0, pair(0, 0))) == IDENTITY, "QD default")
    prefix_count = 4096
    prefix = [stream.value(q) for q in range(prefix_count)]
    require(all(nat(n) for n in prefix), "stream prefix not total")
    for q in range(256):
        require(TheoremStream().value(q) == prefix[q], "DAG/prefix discrepancy")
    receipt = {
        "status": "passed", "formula_tags": 3, "description_tags": 8,
        "target_code": 0, "target_formula": "E(v0,v0)",
        "default_code": IDENTITY, "logical_certificate_semantics": semantic_checks,
        "certificates": len(certificates), "rejected_controls": [name for name, _ in controls],
        "prefix_descriptions": prefix_count, "prefix_target_occurrences": prefix.count(0),
        "prefix_max_formula_bits": max(n.bit_length() for n in prefix),
        "scope": "Local syntax, logic certificates, compiler and finite prefixes only; no consistency proof by testing.",
    }
    return receipt, certificates


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--certificates", type=Path)
    parser.add_argument("--search", action="store_true")
    parser.add_argument("--limit", type=int)
    args = parser.parse_args()
    if args.search:
        require(args.limit is None or args.limit >= 0, "negative search limit")
        stream, q = TheoremStream(), 0
        while args.limit is None or q < args.limit:
            if stream.value(q) == 0:
                print(json.dumps({"status": "target_found", "description": q}))
                return
            q += 1
        print(json.dumps({"status": "unknown", "descriptions_checked": q}))
        return
    receipt, certificates = suite()
    output = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(output)
    if args.certificates:
        args.certificates.write_text(json.dumps(certificates, indent=2, sort_keys=True) + "\n")
    print(output, end="")


if __name__ == "__main__":
    main()
