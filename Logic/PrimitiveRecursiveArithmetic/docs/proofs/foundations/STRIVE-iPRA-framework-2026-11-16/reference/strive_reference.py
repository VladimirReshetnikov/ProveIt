"""Executable reference model for STRIVE-iPRA.

This module is semantic evidence, not an iPRA proof checker.  It implements the
same primitive-recursive recurrences used in the report:

* heterogeneous mixed-radix packing;
* Boolean evaluation of a fixed bounded formula;
* positive and negative strategy-code bounds;
* canonical least signed strategy synthesis;
* a recursive checker for arbitrary supplied codes;
* finite monotone demand closure.

The formula is a finite JSON-compatible syntax tree.  There is deliberately no
universal object-language evaluator claim: in Lean, each fixed tree is meant to
be specialized to concrete PR symbols and Prf PRAAx derivations.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import reduce
from operator import mul
from typing import Any, Callable, Iterable, Mapping, Sequence

JSON = dict[str, Any]
Env = dict[str, int]


class StriveError(ValueError):
    """Raised for malformed formulas, terms, or certificate codes."""


def _nat(value: Any, *, what: str = "value") -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise StriveError(f"{what} must be an integer, got {value!r}")
    if value < 0:
        raise StriveError(f"{what} must be nonnegative, got {value}")
    return value


def product(values: Iterable[int]) -> int:
    result = 1
    for value in values:
        result *= _nat(value, what="radix")
    return result


def mixed_pack(digits: Sequence[int], radices: Sequence[int]) -> int:
    """Pack digits in little-endian heterogeneous mixed radix.

    The represented number is
        d_0 + B_0(d_1 + B_1(d_2 + ...)).
    Every radix must be positive and every digit strictly below its radix.
    The empty table has the unique code 0 and total bound 1.
    """

    if len(digits) != len(radices):
        raise StriveError("digits and radices must have the same length")
    code = 0
    place = 1
    for index, (digit, radix) in enumerate(zip(digits, radices, strict=True)):
        radix = _nat(radix, what=f"radix[{index}]")
        digit = _nat(digit, what=f"digit[{index}]")
        if radix == 0:
            raise StriveError(f"radix[{index}] must be positive")
        if digit >= radix:
            raise StriveError(
                f"digit[{index}]={digit} is not below radix {radix}"
            )
        code += place * digit
        place *= radix
    return code


def mixed_unpack(code: int, radices: Sequence[int]) -> list[int]:
    """Decode a little-endian mixed-radix code."""

    code = _nat(code, what="code")
    total = 1
    normalized: list[int] = []
    for index, radix in enumerate(radices):
        radix = _nat(radix, what=f"radix[{index}]")
        if radix == 0:
            raise StriveError(f"radix[{index}] must be positive")
        normalized.append(radix)
        total *= radix
    if code >= total:
        raise StriveError(f"code {code} is not below mixed-radix bound {total}")
    digits: list[int] = []
    rest = code
    for radix in normalized:
        digits.append(rest % radix)
        rest //= radix
    if rest != 0:  # Defensive; the bound check should make this impossible.
        raise StriveError("internal mixed-radix decoding error")
    return digits


def mixed_digit(code: int, radices: Sequence[int], index: int) -> int:
    """Return one digit without materializing the full table."""

    index = _nat(index, what="index")
    if index >= len(radices):
        raise StriveError("digit index outside the radix table")
    return mixed_unpack(code, radices)[index]


def _term(term: Any, env: Mapping[str, int]) -> int:
    """Evaluate the small arithmetic term language used by examples."""

    if isinstance(term, int) and not isinstance(term, bool):
        return _nat(term, what="numeral")
    if not isinstance(term, dict) or len(term) != 1:
        raise StriveError(f"malformed arithmetic term: {term!r}")
    op, arg = next(iter(term.items()))
    if op == "var":
        if not isinstance(arg, str) or arg not in env:
            raise StriveError(f"unbound variable {arg!r}")
        return _nat(env[arg], what=f"variable {arg}")
    if op == "succ":
        return _term(arg, env) + 1
    if op in {"add", "mul", "monus", "mod", "quot", "min", "max"}:
        if not isinstance(arg, list) or len(arg) != 2:
            raise StriveError(f"{op} expects two arguments")
        left = _term(arg[0], env)
        right = _term(arg[1], env)
        if op == "add":
            return left + right
        if op == "mul":
            return left * right
        if op == "monus":
            return max(0, left - right)
        if op == "mod":
            return 0 if right == 0 else left % right
        if op == "quot":
            return 0 if right == 0 else left // right
        if op == "min":
            return min(left, right)
        return max(left, right)
    raise StriveError(f"unknown arithmetic operation {op!r}")


def _pred(predicate: Any, env: Mapping[str, int]) -> bool:
    """Evaluate a decidable primitive-recursive predicate expression."""

    if isinstance(predicate, bool):
        return predicate
    if not isinstance(predicate, dict) or len(predicate) != 1:
        raise StriveError(f"malformed predicate: {predicate!r}")
    op, arg = next(iter(predicate.items()))
    if op in {"eq", "ne", "lt", "le"}:
        if not isinstance(arg, list) or len(arg) != 2:
            raise StriveError(f"{op} expects two arithmetic terms")
        left = _term(arg[0], env)
        right = _term(arg[1], env)
        if op == "eq":
            return left == right
        if op == "ne":
            return left != right
        if op == "lt":
            return left < right
        return left <= right
    if op == "divides":
        if not isinstance(arg, list) or len(arg) != 2:
            raise StriveError("divides expects divisor and dividend")
        divisor = _term(arg[0], env)
        dividend = _term(arg[1], env)
        return divisor != 0 and dividend % divisor == 0
    if op == "not":
        return not _pred(arg, env)
    if op in {"and", "or"}:
        if not isinstance(arg, list):
            raise StriveError(f"{op} expects a list")
        values = [_pred(item, env) for item in arg]
        return all(values) if op == "and" else any(values)
    raise StriveError(f"unknown predicate operation {op!r}")


def formula_kind(formula: JSON) -> str:
    if not isinstance(formula, dict):
        raise StriveError("a formula must be an object")
    kind = formula.get("kind")
    if kind not in {"atom", "and", "or", "exists", "forall"}:
        raise StriveError(f"unknown formula kind {kind!r}")
    return kind


def _children(formula: JSON) -> tuple[JSON, JSON]:
    left = formula.get("left")
    right = formula.get("right")
    if not isinstance(left, dict) or not isinstance(right, dict):
        raise StriveError("binary formula requires left and right subformulas")
    return left, right


def _quantifier_data(formula: JSON, env: Mapping[str, int]) -> tuple[str, int, JSON]:
    var = formula.get("var")
    body = formula.get("body")
    if not isinstance(var, str) or not var:
        raise StriveError("bounded quantifier requires a nonempty variable name")
    if not isinstance(body, dict):
        raise StriveError("bounded quantifier requires a body")
    bound = _term(formula.get("bound"), env)
    return var, bound, body


def extend(env: Mapping[str, int], var: str, value: int) -> Env:
    result = dict(env)
    result[var] = _nat(value, what=f"value of {var}")
    return result


def evaluate(formula: JSON, env: Mapping[str, int] | None = None) -> bool:
    """Evaluate a fixed bounded formula."""

    env = {} if env is None else env
    kind = formula_kind(formula)
    if kind == "atom":
        return _pred(formula.get("predicate"), env)
    if kind == "and":
        left, right = _children(formula)
        return evaluate(left, env) and evaluate(right, env)
    if kind == "or":
        left, right = _children(formula)
        return evaluate(left, env) or evaluate(right, env)
    var, bound, body = _quantifier_data(formula, env)
    values = (evaluate(body, extend(env, var, i)) for i in range(bound))
    return any(values) if kind == "exists" else all(values)


def certificate_bound(
    formula: JSON, env: Mapping[str, int] | None, side: bool
) -> int:
    """Bound the signed strategy-code space.

    A zero bound means that the requested side has no syntactically shaped
    certificate at this input (for example, a positive certificate for an empty
    existential).  A successful checker always implies a positive bound.
    """

    env = {} if env is None else env
    kind = formula_kind(formula)
    if kind == "atom":
        return 1
    if kind in {"and", "or"}:
        left, right = _children(formula)
        b_left = certificate_bound(left, env, side)
        b_right = certificate_bound(right, env, side)
        if (kind == "and" and side) or (kind == "or" and not side):
            return b_left * b_right
        return b_left + b_right
    var, bound, body = _quantifier_data(formula, env)
    child_bounds = [
        certificate_bound(body, extend(env, var, i), side) for i in range(bound)
    ]
    if (kind == "exists" and side) or (kind == "forall" and not side):
        return sum(child_bounds)
    return product(child_bounds)


def _select_disjoint(code: int, bounds: Sequence[int]) -> tuple[int, int] | None:
    """Decode a disjoint-sum code, skipping empty summands."""

    if code < 0:
        return None
    offset = 0
    for index, bound in enumerate(bounds):
        bound = _nat(bound, what=f"bound[{index}]")
        if offset <= code < offset + bound:
            return index, code - offset
        offset += bound
    return None


def canonical_strategy(
    formula: JSON, env: Mapping[str, int] | None = None
) -> tuple[bool, int]:
    """Return the truth value and its canonical least signed strategy code."""

    env = {} if env is None else env
    kind = formula_kind(formula)
    if kind == "atom":
        return evaluate(formula, env), 0

    if kind in {"and", "or"}:
        left, right = _children(formula)
        side_left, code_left = canonical_strategy(left, env)
        side_right, code_right = canonical_strategy(right, env)
        if kind == "and":
            side = side_left and side_right
            if side:
                radices = [
                    certificate_bound(left, env, True),
                    certificate_bound(right, env, True),
                ]
                return True, mixed_pack([code_left, code_right], radices)
            if not side_left:  # least failing branch
                return False, code_left
            offset = certificate_bound(left, env, False)
            return False, offset + code_right
        side = side_left or side_right
        if side:
            if side_left:  # least winning branch
                return True, code_left
            offset = certificate_bound(left, env, True)
            return True, offset + code_right
        radices = [
            certificate_bound(left, env, False),
            certificate_bound(right, env, False),
        ]
        return False, mixed_pack([code_left, code_right], radices)

    var, bound, body = _quantifier_data(formula, env)
    children = [canonical_strategy(body, extend(env, var, i)) for i in range(bound)]
    if kind == "exists":
        for i, (child_side, child_code) in enumerate(children):
            if child_side:
                offset = sum(
                    certificate_bound(body, extend(env, var, j), True)
                    for j in range(i)
                )
                return True, offset + child_code
        radices = [
            certificate_bound(body, extend(env, var, i), False)
            for i in range(bound)
        ]
        return False, mixed_pack([code for _, code in children], radices)

    # Universal quantifier.
    for i, (child_side, child_code) in enumerate(children):
        if not child_side:
            offset = sum(
                certificate_bound(body, extend(env, var, j), False)
                for j in range(i)
            )
            return False, offset + child_code
    radices = [
        certificate_bound(body, extend(env, var, i), True) for i in range(bound)
    ]
    return True, mixed_pack([code for _, code in children], radices)


def check_strategy(
    formula: JSON,
    env: Mapping[str, int] | None,
    side: bool,
    code: int,
) -> bool:
    """Check an arbitrary signed strategy code without trusting its producer."""

    env = {} if env is None else env
    if isinstance(code, bool) or not isinstance(code, int) or code < 0:
        return False
    total_bound = certificate_bound(formula, env, side)
    if code >= total_bound:
        return False
    kind = formula_kind(formula)
    if kind == "atom":
        return code == 0 and evaluate(formula, env) is side

    if kind in {"and", "or"}:
        left, right = _children(formula)
        product_case = (kind == "and" and side) or (kind == "or" and not side)
        if product_case:
            radices = [
                certificate_bound(left, env, side),
                certificate_bound(right, env, side),
            ]
            if any(radix == 0 for radix in radices):
                return False
            left_code, right_code = mixed_unpack(code, radices)
            return check_strategy(left, env, side, left_code) and check_strategy(
                right, env, side, right_code
            )
        bounds = [
            certificate_bound(left, env, side),
            certificate_bound(right, env, side),
        ]
        selected = _select_disjoint(code, bounds)
        if selected is None:
            return False
        index, child_code = selected
        child = left if index == 0 else right
        return check_strategy(child, env, side, child_code)

    var, bound, body = _quantifier_data(formula, env)
    disjoint_case = (kind == "exists" and side) or (kind == "forall" and not side)
    child_envs = [extend(env, var, i) for i in range(bound)]
    child_bounds = [certificate_bound(body, child_env, side) for child_env in child_envs]
    if disjoint_case:
        selected = _select_disjoint(code, child_bounds)
        if selected is None:
            return False
        index, child_code = selected
        return check_strategy(body, child_envs[index], side, child_code)
    if any(radix == 0 for radix in child_bounds):
        return False
    child_codes = mixed_unpack(code, child_bounds)
    return all(
        check_strategy(body, child_env, side, child_code)
        for child_env, child_code in zip(child_envs, child_codes, strict=True)
    )


def decode_strategy(
    formula: JSON,
    env: Mapping[str, int] | None,
    side: bool,
    code: int,
) -> JSON:
    """Decode a valid code into a human-readable certificate tree."""

    env = {} if env is None else env
    if not check_strategy(formula, env, side, code):
        return {"valid": False, "side": side, "code": code}
    kind = formula_kind(formula)
    base: JSON = {"valid": True, "kind": kind, "side": side, "code": code}
    if kind == "atom":
        base["label"] = formula.get("label", "atom")
        return base
    if kind in {"and", "or"}:
        left, right = _children(formula)
        product_case = (kind == "and" and side) or (kind == "or" and not side)
        if product_case:
            radices = [
                certificate_bound(left, env, side),
                certificate_bound(right, env, side),
            ]
            child_codes = mixed_unpack(code, radices)
            base["children"] = [
                decode_strategy(left, env, side, child_codes[0]),
                decode_strategy(right, env, side, child_codes[1]),
            ]
            return base
        bounds = [
            certificate_bound(left, env, side),
            certificate_bound(right, env, side),
        ]
        selected = _select_disjoint(code, bounds)
        assert selected is not None
        index, child_code = selected
        base["choice"] = index
        base["child"] = decode_strategy(
            left if index == 0 else right, env, side, child_code
        )
        return base
    var, bound, body = _quantifier_data(formula, env)
    child_envs = [extend(env, var, i) for i in range(bound)]
    child_bounds = [certificate_bound(body, child_env, side) for child_env in child_envs]
    disjoint_case = (kind == "exists" and side) or (kind == "forall" and not side)
    if disjoint_case:
        selected = _select_disjoint(code, child_bounds)
        assert selected is not None
        index, child_code = selected
        base["choice"] = index
        base["child"] = decode_strategy(body, child_envs[index], side, child_code)
        return base
    child_codes = mixed_unpack(code, child_bounds)
    base["table"] = [
        {
            "index": i,
            "certificate": decode_strategy(body, child_env, side, child_code),
        }
        for i, (child_env, child_code) in enumerate(
            zip(child_envs, child_codes, strict=True)
        )
    ]
    return base


@dataclass(frozen=True)
class DemandClosureResult:
    value: tuple[int, ...]
    trace: tuple[tuple[int, ...], ...]
    capacity_budget: int


def least_demand_closure(
    initial: Sequence[int],
    capacities: Sequence[int],
    transfer: Callable[[tuple[int, ...]], Sequence[int]],
) -> DemandClosureResult:
    """Iterate d <- d join F(d) on a finite product of chains.

    Soundness requires `transfer` to be monotone.  The executable function
    checks only range and inflation; the report proves termination under the
    monotonicity contract.  From an initial point d, at most
    sum_i(cap_i - d_i) strict increases are possible.
    """

    if len(initial) != len(capacities):
        raise StriveError("initial vector and capacities must have equal length")
    caps = tuple(_nat(c, what=f"capacity[{i}]") for i, c in enumerate(capacities))
    current = tuple(_nat(v, what=f"initial[{i}]") for i, v in enumerate(initial))
    if any(v > cap for v, cap in zip(current, caps, strict=True)):
        raise StriveError("initial demand exceeds a coordinate capacity")
    budget = sum(cap - value for value, cap in zip(current, caps, strict=True))
    trace: list[tuple[int, ...]] = [current]
    for _ in range(budget + 1):
        proposed_raw = tuple(transfer(current))
        if len(proposed_raw) != len(current):
            raise StriveError("transfer changed the dimension")
        proposed = tuple(
            min(cap, _nat(value, what=f"transfer[{i}]"))
            for i, (value, cap) in enumerate(zip(proposed_raw, caps, strict=True))
        )
        nxt = tuple(max(old, new) for old, new in zip(current, proposed, strict=True))
        if nxt == current:
            return DemandClosureResult(current, tuple(trace), budget)
        if sum(nxt) <= sum(current):
            raise StriveError("strict closure step did not increase the rank")
        current = nxt
        trace.append(current)
    raise StriveError(
        "closure did not stabilize within the finite-chain rank budget; "
        "the transfer may violate the stated contract"
    )


def formula_summary(formula: JSON, env: Mapping[str, int] | None = None) -> JSON:
    """Return a compact, serializable audit record for one formula instance."""

    env = {} if env is None else dict(env)
    side, code = canonical_strategy(formula, env)
    result: JSON = {
        "environment": env,
        "value": side,
        "positive_bound": certificate_bound(formula, env, True),
        "negative_bound": certificate_bound(formula, env, False),
        "canonical_code": code,
        "canonical_check": check_strategy(formula, env, side, code),
        "certificate": decode_strategy(formula, env, side, code),
    }
    return result
