"""Fixed eight-production EPSC proof search, with no external theory data.

All conclusions are globally valid open theorems: free slots are parameters.
The mathematical algorithm ranges over arbitrary natural numbers. Python's
resource limits are not part of its halting semantics; failures are never
accepted as refutations. This is a reference program, not a binary TM table.
"""
from __future__ import annotations

from functools import lru_cache
from typing import Optional

import debruijn_kernel as k


def conjunction(a: int, b: int) -> int:
    return k.neg(k.imp(a, k.neg(b)))


def disjunction(a: int, b: int) -> int:
    return k.imp(k.neg(a), b)


def subset(i: int, j: int) -> int:
    return k.all_(k.imp(k.rel(0, i + 1), k.rel(0, j + 1)))


def empty(i: int) -> int:
    return k.all_(k.neg(k.rel(0, i + 1)))


@lru_cache(None)
def hull_matrix(rho: int) -> int:
    # rho has input x in slot0, output y in slot1, parameters in slots>=2.
    # Both hull copies are under [x,y,v,parameters].
    return k.edit(rho, 2, 0)


@lru_cache(None)
def bound_matrix(rho: int) -> int:
    # Reuse exactly the kernel's edit operation. The maps are
    # x0->2, y1->0, parameter i>=2 -> i+1, under [y,b,x,parameters].
    return k.edit(k.subst0(hull_matrix(rho), 1), 1, 0)


@lru_cache(None)
def bound(rho: int) -> int:
    return raw_bound(bound_matrix(rho))


@lru_cache(None)
def raw_bound(beta: int) -> int:
    # beta is arbitrary in the environment [y,b,x,parameters]. In particular,
    # it may depend on b. No free-variable condition is being assumed.
    return k.all_(k.ex(k.all_(k.imp(beta, subset(0, 1)))))


@lru_cache(None)
def hull(rho: int) -> int:
    """Curried EPSC hull with the common universal y factored out."""
    return hull_from_matrix(hull_matrix(rho))


@lru_cache(None)
def hull_from_matrix(body: int) -> int:
    # Here the matrix environment is [x,y,v,parameters].
    active = disjunction(empty(0), k.rel(0, 2))
    step = k.all_(k.imp(active, k.imp(body, k.rel(1, 2))))
    # Outside x, the environment is [y,v,parameters]. Its existential x
    # restores the identical matrix environment used by the step clause.
    support = k.imp(k.rel(0, 1), k.ex(body))
    return k.ex(k.all_(conjunction(step, support)))


@lru_cache(None)
def protected_matrix(beta: int) -> int:
    # Desired map into the body of a new universal b under [x,y,v,params]:
    # beta's y0->2, b1->0, x2->1, and i>=3->i+1.
    # Two inserted unused slots, then remove old y and substitute slot2.
    return k.all_(k.subst0(k.edit(k.edit(beta, 3, 0), 3, 0), 2))


@lru_cache(None)
def protected_hull(beta: int) -> int:
    return hull_from_matrix(protected_matrix(beta))


def unall(a: int):
    return (a - 3) // 3 if a > 0 and a % 3 == 0 else None


def unimp(a: int):
    return k.unpair((a - 2) // 3) if a > 0 and a % 3 == 2 else None


def unex(a: int):
    outer = unimp(a)
    if outer is None or outer[1] != 0:
        return None
    universal_body = unall(outer[0])
    if universal_body is None:
        return None
    inner = unimp(universal_body)
    return inner[0] if inner is not None and inner[1] == 0 else None


@lru_cache(None)
def extract_bound(a: int):
    """Match the literal fixed boundedness skeleton; return beta or None.

    Zero is a valid beta and must not be confused with failure. This parser
    does not re-emit a separate candidate antecedent or scan variable labels.
    """
    x_body = unall(a)
    if x_body is None:
        return None
    b_body = unex(x_body)
    if b_body is None:
        return None
    y_body = unall(b_body)
    if y_body is None:
        return None
    arrow = unimp(y_body)
    return arrow[0] if arrow is not None and arrow[1] == subset(0, 1) else None


def epsc_axiom(rho: int) -> int:
    return k.imp(bound(rho), hull(rho))


def guarded_matrix(rho: int) -> int:
    # Keep the bound's parameters OPEN. Insert the two matrix roles before
    # those parameters. Closing them before this insertion is unsound.
    theta = k.lift(k.lift(bound(rho)))
    return conjunction(theta, rho)


def proof_close(rho: int, p: int) -> int:
    return 8 * k.pair(rho, p) + 7


def proof_protected_close(p: int) -> int:
    return 8 * p + 7


def rule_checker(*, logic_only: bool = False, presentation: str = "protected"):
    """Return check(n), with None invalid and 0 a genuine refutation.

    Each presentation has exactly eight productions. Shared reference code
    records a purity bit even in primary mode; only logic_only inspects it
    at a closure application. A compact primary compiler may erase the bit.
    """
    if presentation not in ("protected", "rule", "axiom"):
        raise ValueError("presentation must be protected, rule, or axiom")

    @lru_cache(None)
    def checked(n: int) -> Optional[tuple[int, bool]]:
        if type(n) is not int or n < 0:
            raise ValueError("proof codes must be natural numbers")
        payload, tag = divmod(n, 8)
        if tag <= 4:
            a, b = k.unpair(payload)
            if tag == 0:
                return k.K(a, b), True
            if tag == 1:
                b, c = k.unpair(b)
                return k.S(a, b, c), True
            if tag == 2:
                return k.C(a, b), True
            if tag == 3:
                return k.UI(a, b), True
            return k.UD(a, b), True
        if tag == 5:
            p = checked(payload)
            return None if p is None else (k.all_(p[0]), p[1])
        if tag == 6:
            pi, qi = k.unpair(payload)
            p, q = checked(pi), checked(qi)
            if p is None or q is None or q[0] == 0 or q[0] % 3 != 2:
                return None
            a, b = k.unpair((q[0] - 2) // 3)
            return (b, p[1] and q[1]) if a == p[0] else None
        if presentation == "axiom":
            # A fair comparator: open axioms have the same global theorem
            # invariant, so they need no runtime parameter-closure scan.
            return epsc_axiom(payload), False
        if presentation == "protected":
            p = checked(payload)
            if p is None or (logic_only and not p[1]):
                return None
            beta = extract_bound(p[0])
            return None if beta is None else (protected_hull(beta), False)
        rho, pi = k.unpair(payload)
        p = checked(pi)
        if p is None or p[0] != bound(rho) or (logic_only and not p[1]):
            return None
        return hull(rho), False

    def check(n: int) -> Optional[int]:
        p = checked(n)
        return None if p is None else p[0]
    check.with_purity = checked
    return check


def search_refutation():
    check = rule_checker()
    n = 0
    while True:
        if check(n) == 0:
            return n
        n += 1


def check_dag(rows, *, logic_only=False, presentation="protected"):
    """Same eight rules, with prior-line references for practical certificates.

    Natural formula arguments are JSON strings containing lowercase hex;
    prior-line and instantiation indices are JSON nonnegative integers.
    No supplied conclusion and no assumption/extra axiom is accepted.
    """
    if presentation not in ("protected", "rule", "axiom"):
        raise ValueError("unknown presentation")
    conclusions = []
    pure = []

    def natural(v):
        if type(v) is not int or v < 0:
            raise ValueError("expected a natural number")
        return v

    def formula(v):
        if not isinstance(v, str) or not v or any(c not in "0123456789abcdef" for c in v):
            raise ValueError("expected a lowercase hexadecimal formula code")
        return int(v, 16)

    def ref(v):
        v = natural(v)
        if v >= len(conclusions):
            raise ValueError("proof reference is not strictly earlier")
        return v

    for row in rows:
        if not isinstance(row, list) or not row:
            raise ValueError("proof row must be a nonempty array")
        tag, args = row[0], row[1:]
        arities = {"K": 2, "S": 3, "C": 2, "UI": 2, "UD": 2,
                   "GEN": 1, "MP": 2}
        if presentation == "axiom":
            arities["AX"] = 1
        else:
            arities["CLOSE"] = 1 if presentation == "protected" else 2
        if tag not in arities or len(args) != arities[tag]:
            raise ValueError("unknown production or wrong number of fields")
        is_pure = True
        if tag in ("K", "S", "C", "UD"):
            result = getattr(k, tag)(*(formula(a) for a in args))
        elif tag == "UI":
            result = k.UI(formula(args[0]), natural(args[1]))
        elif tag == "GEN":
            p = ref(args[0])
            result, is_pure = k.all_(conclusions[p]), pure[p]
        elif tag == "MP":
            p, q = map(ref, args)
            arrow = conclusions[q]
            if arrow == 0 or arrow % 3 != 2:
                raise ValueError("MP second premise is not an implication")
            a, result = k.unpair((arrow - 2) // 3)
            if a != conclusions[p]:
                raise ValueError("MP antecedent does not match")
            is_pure = pure[p] and pure[q]
        elif tag == "AX":
            result, is_pure = epsc_axiom(formula(args[0])), False
        elif presentation == "protected":
            p = ref(args[0])
            beta = extract_bound(conclusions[p])
            if beta is None:
                raise ValueError("closure premise lacks the exact bound skeleton")
            if logic_only and not pure[p]:
                raise ValueError("closure premise is not a pure logical proof")
            result, is_pure = protected_hull(beta), False
        else:
            rho, p = formula(args[0]), ref(args[1])
            if conclusions[p] != bound(rho):
                raise ValueError("closure premise is not the required bound theorem")
            if logic_only and not pure[p]:
                raise ValueError("closure premise is not a pure logical proof")
            result, is_pure = hull(rho), False
        conclusions.append(result)
        pure.append(is_pure)
    return conclusions


if __name__ == "__main__":
    import argparse
    import json
    from pathlib import Path
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    data = json.loads(args.certificate.read_text())
    result = check_dag(data["proof"], presentation=data.get("presentation", "protected"))
    if not result:
        raise SystemExit("Invalid: empty certificate")
    print(json.dumps({"accepted": True, "lines": len(result),
                      "refutation": result[-1] == 0,
                      "conclusion_bit_length": result[-1].bit_length()}))
