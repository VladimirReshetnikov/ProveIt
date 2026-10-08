"""Component pushforward -> square-free product -> Frobenius expansion.

A plan is the exact tuple format of ProveIt's fastunknot.algebra:
(left-disc mask, right-disc mask, output-circle mask, fixed dots) for each
connected genus-zero component; None means a positive-genus zero map.
"""
from __future__ import annotations
from dataclasses import dataclass
from .subset import noop, pack, subset_product, support, validate, Check

Plan = tuple[tuple[int, int, int, int], ...] | None


def evaluate_reference(plan, f: int, g: int = 0) -> int:
    """The monomial evaluator from upstream algebra.py (minor renaming only)."""
    result = 1
    for left, right, boundary, extra in plan:
        dots = (f & left).bit_count() + (g & right).bit_count() + extra
        if dots >= 2:
            return 0
        if not boundary:
            if dots != 1:
                return 0
            continue
        if dots:
            choices = (boundary,)
        else:
            choices = [boundary ^ (1 << k) for k in support(boundary)]
        nxt = 0
        for monomial in support(result):
            for choice in choices:
                nxt ^= 1 << (monomial | choice)
        result = nxt
    return result


def contract_reference(plan: Plan, f: int, g: int = 1, *, check: Check = noop) -> int:
    """Upstream-style double monomial loop, deliberately without caches."""
    if plan is None or not f or not g:
        return 0
    result = 0
    for tf in support(f):
        check()
        for tg in support(g):
            result ^= evaluate_reference(plan, tf, tg)
    return result


@dataclass(frozen=True)
class CompiledPlan:
    components: tuple[tuple[int, int, int, int], ...]
    left_owner: tuple[int, ...]
    right_owner: tuple[int, ...]
    output_variables: int
    open_components: tuple[tuple[int, int, int], ...]
    required_ones: int
    required_zeros: int
    annihilated: bool

    @classmethod
    def from_plan(cls, plan: Plan) -> "CompiledPlan":
        if plan is None:
            return cls((), (), (), 0, (), 0, 0, True)
        parts = tuple(tuple(p) for p in plan)
        unions = [0, 0, 0]
        for p in parts:
            if len(p) != 4 or any(type(v) is not int or v < 0 for v in p):
                raise ValueError("plan entries must be four nonnegative integers")
            for i in range(3):
                if unions[i] & p[i]:
                    raise ValueError("component masks must be disjoint")
                unions[i] |= p[i]
        for mask in unions:
            if mask != (1 << mask.bit_length()) - 1:
                raise ValueError("variable indices must be contiguous from zero")
        owners = [[0]*unions[i].bit_length() for i in range(2)]
        required_ones = required_zeros = 0
        open_components = []
        annihilated = False
        for j, (left, right, boundary, extra) in enumerate(parts):
            for side, mask in enumerate((left, right)):
                for v in support(mask):
                    owners[side][v] = 1 << j
            if extra >= 2:
                annihilated = True
            if not boundary:
                if extra == 0:
                    required_ones |= 1 << j
                elif extra == 1:
                    required_zeros |= 1 << j
            else:
                if extra == 1:
                    required_zeros |= 1 << j
                open_components.append((j, boundary, extra))
        return cls(parts, tuple(owners[0]), tuple(owners[1]), unions[2].bit_length(),
                   tuple(open_components), required_ones, required_zeros, annihilated)

    @property
    def variables(self) -> int:
        return len(self.components)

    def linearized_rank(self) -> int:
        """Rank of (F tensor G) -> output as an F2-linear map.

        Each surviving open component contributes rank two precisely when it
        has at least one input circle and no fixed dot. Other components
        contribute rank one, except an undotted closed component with no
        inputs, which annihilates the map.
        """
        if self.annihilated:
            return 0
        exponent = 0
        for left, right, boundary, extra in self.components:
            inputs = bool(left or right)
            if not boundary and not extra and not inputs:
                return 0
            if boundary and not extra and inputs:
                exponent += 1
        return 1 << exponent

    def project(self, f: int, side: int, *, check: Check = noop) -> int:
        if side not in (0, 1):
            raise ValueError("side must be 0 or 1")
        owner = self.left_owner if side == 0 else self.right_owner
        validate(f, len(owner))
        if not f or f == 1:
            return f
        out = bytearray(((1 << self.variables)+7)//8)
        for count, monomial in enumerate(support(f)):
            if not count & 255:
                check()
            occupied = 0
            while monomial:
                low = monomial & -monomial
                comp = owner[low.bit_length()-1]
                if occupied & comp:
                    break
                occupied |= comp
                monomial ^= low
            else:
                out[occupied >> 3] ^= 1 << (occupied & 7)
        return int.from_bytes(out, "little")

    def lift(self, h: int, *, check: Check = noop) -> int:
        validate(h, self.variables)
        if self.annihilated or not h:
            return 0
        out = bytearray(((1 << self.output_variables)+7)//8)
        for occupied in support(h):
            check()
            if occupied & self.required_ones != self.required_ones:
                continue
            if occupied & self.required_zeros:
                continue
            terms = [0]
            for j, boundary, extra in self.open_components:
                if extra or (occupied >> j) & 1:
                    choices = (boundary,)
                else:
                    choices = tuple(boundary ^ (1 << k) for k in support(boundary))
                terms = [t | choice for t in terms for choice in choices]
            for s in terms:
                out[s >> 3] ^= 1 << (s & 7)
        return int.from_bytes(out, "little")

    def apply(self, f: int, g: int = 1, *, method: str = "auto", check: Check = noop,
              dense_limit: int = 18) -> int:
        if type(dense_limit) is not int or dense_limit < 0:
            raise ValueError("dense_limit must be a nonnegative integer")
        if type(f) is not int or f < 0 or type(g) is not int or g < 0:
            raise ValueError("polynomials must be nonnegative integers")
        if method not in {"auto", "sparse", "fast", "reference"}:
            raise ValueError("unknown method")
        if self.annihilated:
            return 0
        validate(f, len(self.left_owner)); validate(g, len(self.right_owner))
        if not f or not g:
            return 0
        if method == "reference" or (method == "auto" and f.bit_count()*g.bit_count() <= 16):
            return contract_reference(self.components, f, g, check=check)
        if max(self.variables, self.output_variables) > dense_limit:
            raise MemoryError("component coefficient array exceeds configured variable limit")
        a = self.project(f, 0, check=check)
        if not a:
            return 0
        b = self.project(g, 1, check=check)
        if not b:
            return 0
        product = subset_product(a, b, self.variables, method=method, check=check,
                                 dense_limit=dense_limit)
        return self.lift(product, check=check)


def contract(plan: Plan | CompiledPlan, f: int, g: int = 1, *, method: str = "auto",
             check: Check = noop, dense_limit: int = 18) -> int:
    cp = plan if isinstance(plan, CompiledPlan) else CompiledPlan.from_plan(plan)
    return cp.apply(f, g, method=method, check=check, dense_limit=dense_limit)

