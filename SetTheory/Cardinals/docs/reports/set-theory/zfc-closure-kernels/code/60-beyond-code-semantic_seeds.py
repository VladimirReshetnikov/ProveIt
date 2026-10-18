#!/usr/bin/env python3
"""Sufficient certificates for ZFC-valid Code254 startup formula data.

This recognizes a deliberately small family.  It is NOT a theorem oracle,
a native-C254 derivation checker, a binary-frame checker, or a proof-assistant
certificate.  Its new certificates are justified in foundations_audit.md:
raw Extensionality and denials of finite membership cycles.  Those formulas
may be used by the relative-consistency seed theorem even when no native
C254 proof is supplied.

The codec is Mira-Cult's / Jeff Ketchersid's / ProveIt's original base-four,
dual-Cantor codec: Imp=0, Rel=1, All=2, Eq=3; truth=0, falsity=1.
The legacy certificate constructors and stream convention are reproduced
from ProveIt's safe_seed254.py at a2bf288dead95b653919b86608e3f2cca47552f7.
New recognition and audit code: this research delivery, 17 October 2026.

Usage:
    python semantic_seeds.py --audit
    python semantic_seeds.py --formula 19364
    python semantic_seeds.py --state 0 19364 0 0 0 0 0 0 0
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from math import isqrt
from pathlib import Path


def natural(x: int) -> int:
    if type(x) is not int or x < 0:
        raise ValueError("natural number required")
    return x


def pair(a: int, b: int) -> int:
    natural(a)
    natural(b)
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    natural(n)
    d = (isqrt(8 * n + 1) - 1) // 2
    b = n - d * (d + 1) // 2
    return d - b, b


def imp(a: int, b: int) -> int:
    return 4 * pair(a, b)


def rel(a: int, b: int) -> int:
    return 4 * pair(a, b) + 1


def all_(a: int, b: int) -> int:
    return 4 * pair(a, b) + 2


def eq(a: int, b: int) -> int:
    return 4 * pair(a, b) + 3


def neg(a: int) -> int:
    return imp(a, 1)


def and_(a: int, b: int) -> int:
    return neg(imp(a, neg(b)))


def iff(a: int, b: int) -> int:
    return and_(imp(a, b), imp(b, a))


def cycle_code(labels: list[int] | tuple[int, ...]) -> int:
    """Curried denial of v0 in v1 in ... in v0, for the supplied labels."""
    if not labels:
        raise ValueError("membership cycle must have positive length")
    for x in labels:
        natural(x)
    out = 1
    for i in range(len(labels) - 1, -1, -1):
        out = imp(rel(labels[i], labels[(i + 1) % len(labels)]), out)
    return out


def extensionality_code(a: int, b: int, c: int) -> int:
    """(forall c (c in a iff c in b)) -> a=b, universally valid in ZFC."""
    for x in (a, b, c):
        natural(x)
    if c in (a, b):
        raise ValueError("Extensionality's bound label must be fresh")
    return imp(all_(c, iff(rel(c, a), rel(c, b))), eq(a, b))


def code(cert: tuple | list) -> int:
    """Check the certificate's schema/arity and reconstruct its exact code."""
    if not isinstance(cert, (tuple, list)) or not cert:
        raise ValueError("nonempty certificate required")
    tag, *args = cert
    arities = {"truth": 0, "all": 2, "identity": 1, "weaken": 2,
               "exfalso": 1, "eqRefl": 1, "foundationCycle": 1,
               "extensionality": 3}
    if tag not in arities or len(args) != arities[tag]:
        raise ValueError("unknown certificate tag or wrong arity")
    if tag == "truth":
        return 0
    if tag == "foundationCycle":
        if not isinstance(args[0], (tuple, list)):
            raise ValueError("cycle labels must be a finite list")
        return cycle_code(args[0])
    if tag == "extensionality":
        return extensionality_code(*args)
    a = natural(args[0])
    if tag == "all":
        return all_(a, code(args[1]))
    if tag == "identity":
        return imp(a, a)
    if tag == "weaken":
        return imp(a, code(args[1]))
    if tag == "exfalso":
        return imp(1, a)
    if tag == "eqRefl":
        return eq(a, a)
    raise AssertionError("unhandled checked tag")


def legacy_formula(n: int, fuel: int = 256) -> tuple | None:
    """Exact accepted-family comparator for ProveIt's six seed constructors."""
    natural(n)
    if n == 0:
        return ("truth",)
    if fuel <= 0:
        return None
    a, b = unpair(n // 4)
    tag = n % 4
    if tag == 3 and a == b:
        return ("eqRefl", a)
    if tag == 2:
        inner = legacy_formula(b, fuel - 1)
        return ("all", a, inner) if inner is not None else None
    if tag == 0:
        if a == b:
            return ("identity", a)
        if a == 1:
            return ("exfalso", b)
        inner = legacy_formula(b, fuel - 1)
        return ("weaken", a, inner) if inner is not None else None
    return None


def parse_cycle(n: int, fuel: int) -> tuple | None:
    edges: list[tuple[int, int]] = []
    while n != 1:
        if fuel <= 0 or n == 0 or n % 4 != 0:
            return None
        left, n = unpair(n // 4)
        if left % 4 != 1:
            return None
        edges.append(unpair(left // 4))
        fuel -= 1
    if not edges:
        return None
    if all(edges[i][1] == edges[(i + 1) % len(edges)][0]
           for i in range(len(edges))):
        return ("foundationCycle", [a for a, _ in edges])
    return None


def parse_extensionality(n: int) -> tuple | None:
    if n == 0 or n % 4 != 0:
        return None
    left, right = unpair(n // 4)
    if left % 4 != 2 or right % 4 != 3:
        return None
    c, body = unpair(left // 4)
    a, b = unpair(right // 4)
    if c in (a, b):
        return None
    if body == iff(rel(c, a), rel(c, b)):
        return ("extensionality", a, b, c)
    return None


def formula(n: int, fuel: int = 256) -> tuple | None:
    """Return a sufficient ZFC-validity certificate, never a semantic guess."""
    natural(n)
    if n == 0:
        return ("truth",)
    if fuel <= 0:
        return None
    a, b = unpair(n // 4)
    tag = n % 4
    result = None
    if tag == 3 and a == b:
        result = ("eqRefl", a)
    elif tag == 2:
        inner = formula(b, fuel - 1)
        if inner is not None:
            result = ("all", a, inner)
    elif tag == 0:
        if a == b:
            result = ("identity", a)
        elif a == 1:
            result = ("exfalso", b)
        else:
            inner = formula(b, fuel - 1)
            if inner is not None:
                result = ("weaken", a, inner)
    if result is None:
        result = parse_cycle(n, fuel)
    if result is None:
        result = parse_extensionality(n)
    if result is not None and code(result) != n:
        raise AssertionError("certificate/code disagreement")
    return result


def stack_code(certs: list) -> int:
    n = 0
    for cert in reversed(certs):
        n = pair(code(cert), n)
    return n


def stack(n: int, fuel: int = 256, recognizer=formula) -> list | None:
    """Check every exposed entry of the finite code plus its infinite 0 tail."""
    natural(n)
    original, certs = n, []
    while n:
        if len(certs) >= fuel:
            return None
        head, tail = unpair(n)
        cert = recognizer(head, fuel)
        if cert is None:
            return None
        if tail >= n:
            raise AssertionError("positive stream-tail descent failed")
        certs.append(cert)
        n = tail
    if stack_code(certs) != original:
        raise AssertionError("stream reconstruction failed")
    return certs


def state(logical: list[int]) -> dict | None:
    """Formula admission only. Register order N,T,W,A,D,H,X,Y,L."""
    if len(logical) != 9:
        raise ValueError("exactly nine logical registers required")
    for n in logical:
        natural(n)
    top, cache, cells = formula(logical[1]), formula(logical[5]), stack(logical[2])
    if top is None or cache is None or cells is None:
        return None
    return {"top": top, "cache": cache, "stack": cells,
            "scope": "ZFC-valid formula data only; complete binary frame remains required"}


def eval_code(n: int, env: tuple[int, ...], mem: tuple[tuple[bool, ...], ...]) -> bool:
    """Independent finite semantics for diagnostics; F is normalized to false."""
    if n == 0:
        return True
    if n == 1:
        return False
    a, b = unpair(n // 4)
    if n % 4 == 0:
        return not eval_code(a, env, mem) or eval_code(b, env, mem)
    if n % 4 == 1:
        return mem[env[a]][env[b]]
    if n % 4 == 3:
        return env[a] == env[b]
    return all(eval_code(b, env[:a] + (x,) + env[a + 1:], mem)
               for x in range(len(mem)))


def acyclic(mem: tuple[tuple[bool, ...], ...]) -> bool:
    reach = [list(row) for row in mem]
    for k in range(len(mem)):
        for i in range(len(mem)):
            for j in range(len(mem)):
                reach[i][j] |= reach[i][k] and reach[k][j]
    return not any(reach[i][i] for i in range(len(mem)))


def fingerprint(n: int) -> dict:
    return {"bit_length": n.bit_length(), "sha256_unsigned_big_endian":
            hashlib.sha256(n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")).hexdigest()}


def audit(limit: int = 65536) -> dict:
    legacy_f = new_f = legacy_s = new_s = 0
    added: list[int] = []
    for n in range(limit):
        old, new = legacy_formula(n), formula(n)
        if old is not None:
            legacy_f += 1
            assert code(old) == n and new is not None
        if new is not None:
            new_f += 1
            assert code(new) == n
            if old is None:
                added.append(n)
        old_stack, new_stack = stack(n, recognizer=legacy_formula), stack(n)
        if old_stack is not None:
            legacy_s += 1
            assert new_stack is not None
        if new_stack is not None:
            new_s += 1
            assert stack_code(new_stack) == n

    # A practical, small newly admitted formula; its stack value is different.
    two_cycle = cycle_code([0, 1])
    assert two_cycle == 19364
    assert legacy_formula(two_cycle) is None
    assert code(formula(two_cycle)) == two_cycle
    assert formula(1) is None and formula(5) is None and formula(9) is None
    assert stack(1) is None and stack(60) is None
    assert state([0, two_cycle, 0, 0, 0, 0, 0, 0, 0]) is not None
    assert stack(pair(two_cycle, 0)) is not None

    templates = 0
    for length in range(1, 5):
        for labels in itertools.product(range(4), repeat=length):
            n = cycle_code(labels)
            assert code(formula(n, 512)) == n
            templates += 1
    for a, b, c in itertools.product(range(4), repeat=3):
        if c not in (a, b):
            n = extensionality_code(a, b, c)
            assert code(formula(n, 512)) == n
            assert code(formula(all_(a, all_(b, n)), 512)) == all_(a, all_(b, n))
            templates += 1

    # All small well-founded relations, including nonextensional ones for cycles.
    cycle_semantic_cases = extensionality_semantic_cases = 0
    graphs = ext_graphs = 0
    cycle_templates = [cycle_code(labels) for length in range(1, 4)
                       for labels in itertools.product(range(3), repeat=length)]
    ext = extensionality_code(0, 1, 2)
    for size in range(1, 4):
        for bits in range(1 << (size * size)):
            mem = tuple(tuple(bool(bits & (1 << (i * size + j)))
                              for j in range(size)) for i in range(size))
            if not acyclic(mem):
                continue
            graphs += 1
            columns = [tuple(mem[i][j] for i in range(size)) for j in range(size)]
            is_extensional = len(set(columns)) == size
            ext_graphs += is_extensional
            for env in itertools.product(range(size), repeat=3):
                for n in cycle_templates:
                    assert eval_code(n, env, mem)
                    cycle_semantic_cases += 1
                if is_extensional:
                    assert eval_code(ext, env, mem)
                    extensionality_semantic_cases += 1

    # The recognizer must reject malformed certificate shapes/freshness premises.
    rejected_bad_certificates = 0
    for bad in [("foundationCycle", []), ("foundationCycle", [-1]),
                ("extensionality", 0, 1, 1), ("extensionality", 0, 1, 0),
                ("all", 0), ("truth", 0), ("unknown",), ("eqRefl", True)]:
        try:
            code(bad)
        except ValueError:
            rejected_bad_certificates += 1
        else:
            raise AssertionError("bad certificate accepted")

    result = {"status": "PASS", "scope": "finite codec and semantic diagnostics; ordinary mathematical soundness proof is separate",
              "tested_codes_each": limit,
              "legacy_formula_codes": legacy_f, "semantic_formula_codes": new_f,
              "added_formula_codes": added,
              "legacy_stack_codes": legacy_s, "semantic_stack_codes": new_s,
              "cycle_and_extensionality_template_cases": templates,
              "acyclic_graphs_sizes_1_to_3": graphs,
              "extensional_acyclic_graphs_sizes_1_to_3": ext_graphs,
              "foundation_cycle_semantic_cases": cycle_semantic_cases,
              "extensionality_semantic_cases": extensionality_semantic_cases,
              "malformed_certificates_rejected": rejected_bad_certificates,
              "two_cycle_code": two_cycle,
              "two_cycle_certificate": formula(two_cycle),
              "two_cycle_singleton_stack_code": pair(two_cycle, 0),
              "extensionality_0_1_2": fingerprint(ext),
              "extensionality_certificate": formula(ext),
              "ordinary_soundness_proof": "foundations_audit.md",
              "binary_simulation_checked": False,
              "new_machine_constructed": False,
              "lean_or_coq_proof_supplied": False}
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--audit", action="store_true")
    group.add_argument("--formula", type=int)
    group.add_argument("--state", type=int, nargs=9)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.audit:
        result = audit()
    elif args.formula is not None:
        result = {"formula": args.formula, "certificate": formula(args.formula)}
    else:
        result = {"logical_registers": args.state, "certificate": state(args.state)}
    encoded = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end="")


if __name__ == "__main__":
    main()
