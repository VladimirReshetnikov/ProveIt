"""Exact component-compressed F2 dotted-cobordism composition.

Bit convention: bit number S is the coefficient of the square-free monomial S.
A component is (left_mask, right_mask, output_mask, extra_dots), optionally
followed by the choices field of fastunknot.planar.component.

This is a numerical kernel, NOT a stand-alone unknot recognizer.
SPDX-License-Identifier: MIT-0
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Iterable, Sequence

Check = Callable[[], None]
_BYTE_BITS = tuple(tuple(j for j in range(8) if b & (1 << j)) for b in range(256))


class KernelLimit(RuntimeError):
    """A dense-domain allocation would exceed the caller's explicit budget."""


def _noop() -> None:
    pass


def support(value: int):
    """Iterate support without repeatedly shifting a potentially long integer."""
    raw = value.to_bytes((value.bit_length() + 7) // 8, "little")
    for i, b in enumerate(raw):
        for j in _BYTE_BITS[b]:
            yield 8 * i + j


def pack(coefficients: Sequence[int]) -> int:
    out = bytearray((len(coefficients) + 7) // 8)
    for i, bit in enumerate(coefficients):
        if bit:
            out[i >> 3] |= 1 << (i & 7)
    return int.from_bytes(out, "little")


def subset_convolution(f: Sequence[int], g: Sequence[int], k: int,
                       check: Check = _noop) -> bytearray:
    """Disjoint subset convolution over F2, by ranked zeta/Mobius transforms.

    Ranks are packed into separated binary lanes. Ordinary integer multiplication
    is safe: a product coefficient is at most k+1, and lane base > k+1. Selecting
    the low bit of each lane therefore implements exact carryless multiplication.
    No floating point or probabilistic arithmetic is used.
    """
    if type(k) is not int or k < 0:
        raise ValueError("k must be a nonnegative integer")
    n = 1 << k
    if len(f) != n or len(g) != n:
        raise ValueError("coefficient arrays must have length 2**k")
    if any(x not in (0, 1) for x in f) or any(x not in (0, 1) for x in g):
        raise ValueError("coefficients must be bits")
    lane = (k + 1).bit_length()
    ranks = [s.bit_count() for s in range(n)]
    a = [int(f[s]) << (lane * ranks[s]) for s in range(n)]
    b = [int(g[s]) << (lane * ranks[s]) for s in range(n)]
    for bit in range(k):
        check()
        step = 1 << bit
        for start in range(0, n, step * 2):
            if not start & 1023:
                check()
            for s in range(start + step, start + step * 2):
                a[s] ^= a[s - step]
                b[s] ^= b[s - step]
    parity_lanes = sum(1 << (lane * rank) for rank in range(k + 1))
    h = []
    for s in range(n):
        if not s & 1023:
            check()
        h.append((a[s] * b[s]) & parity_lanes)
    # Mobius equals zeta in characteristic two.
    for bit in range(k):
        check()
        step = 1 << bit
        for start in range(0, n, step * 2):
            if not start & 1023:
                check()
            for s in range(start + step, start + step * 2):
                h[s] ^= h[s - step]
    return bytearray((h[s] >> (lane * ranks[s])) & 1 for s in range(n))


@dataclass(frozen=True)
class Dimensions:
    left: int
    right: int
    output: int
    components: int

    @property
    def domain_entries(self) -> int:
        return sum(1 << v for v in (self.left, self.right, self.output, self.components))


def normalize(components: Iterable[Sequence[int]]) -> tuple[tuple[int, int, int, int], ...]:
    answer = []
    for row in components:
        if len(row) not in (4, 5):
            raise ValueError("a component must have four fields, or five with choices")
        values = tuple(row[:4])
        if any(type(v) is not int or v < 0 for v in values):
            raise ValueError("component masks and extra dots must be nonnegative integers")
        if len(row) == 5:
            boundary = values[2]
            expected = tuple(boundary ^ (1 << b) for b in range(boundary.bit_length())
                             if boundary & (1 << b))
            if tuple(row[4]) != expected:
                raise ValueError("choices do not agree with the output mask")
        answer.append(values)
    result = tuple(answer)
    for side in range(3):
        used = 0
        for row in result:
            if used & row[side]:
                raise ValueError("component masks must be disjoint on each side")
            used |= row[side]
        if used != (1 << used.bit_length()) - 1:
            raise ValueError("circle indices must be contiguous from zero")
    return result


def dimensions(components: Sequence[Sequence[int]]) -> Dimensions:
    masks = [0, 0, 0]
    for row in components:
        for side in range(3):
            masks[side] |= row[side]
    return Dimensions(*(m.bit_length() for m in masks), len(components))


def _projection_table(components: Sequence[Sequence[int]], side: int, r: int,
                      check: Check) -> list[int]:
    owners = [0] * r
    for j, row in enumerate(components):
        mask = row[side]
        while mask:
            low = mask & -mask
            owners[low.bit_length() - 1] = 1 << j
            mask ^= low
    table = [0] * (1 << r)
    for mask in range(1, 1 << r):
        if not mask & 1023:
            check()
        low = mask & -mask
        old = table[mask ^ low]
        bit = owners[low.bit_length() - 1]
        table[mask] = -1 if old < 0 or old & bit else old | bit
    return table


class ComponentPlan:
    """Reusable quotient and reconstruction tables for one genus-zero plan.

    The default allocation cap counts table entries, not bytes. Projection and
    output tables use Python integers and may have a sizeable constant factor.
    The cap is checked BEFORE allocation. A caller can fall back on KernelLimit.
    """
    def __init__(self, components: Iterable[Sequence[int]], *,
                 max_entries: int = 1 << 18, check: Check = _noop):
        if type(max_entries) is not int or max_entries < 0:
            raise ValueError("max_entries must be a nonnegative integer")
        self.components = normalize(components)
        self.dim = dimensions(self.components)
        self.check = check
        self.zero = any(row[3] >= 2 for row in self.components)
        if self.dim.domain_entries > max_entries:
            raise KernelLimit(f"{self.dim.domain_entries} domain entries exceed {max_entries}")
        d = self.dim
        self.left_table = _projection_table(self.components, 0, d.left, check)
        self.right_table = _projection_table(self.components, 1, d.right, check)
        extra_mask = sum(1 << j for j, row in enumerate(self.components) if row[3] == 1)
        # Each output monomial comes from at most one component-dot monomial.
        self.output_table = [-1] * (1 << d.output)
        if not self.zero:
            for out in range(1 << d.output):
                if not out & 1023:
                    check()
                required = 0
                for j, (_, _, boundary, _) in enumerate(self.components):
                    missing = (boundary & ~out).bit_count()
                    if not boundary or missing == 0:
                        required |= 1 << j   # a closed sphere requires one dot
                    elif missing != 1:
                        break
                else:
                    if required & extra_mask == extra_mask:
                        self.output_table[out] = required ^ extra_mask

    def _project(self, f: int, table: list[int]) -> bytearray:
        result = bytearray(1 << self.dim.components)
        for i, mask in enumerate(support(f)):
            if not i & 1023:
                self.check()
            image = table[mask]
            if image >= 0:
                result[image] ^= 1
        return result

    def compose(self, f: int, g: int) -> int:
        d = self.dim
        if type(f) is not int or type(g) is not int or f < 0 or g < 0:
            raise ValueError("morphisms must be nonnegative integers")
        if f.bit_length() > 1 << d.left or g.bit_length() > 1 << d.right:
            raise ValueError("morphism has a monomial outside its input basis")
        self.check()
        if not f or not g or self.zero:
            return 0
        a = self._project(f, self.left_table)
        b = self._project(g, self.right_table)
        if not any(a) or not any(b):
            return 0
        h = subset_convolution(a, b, d.components, self.check)
        out = bytearray((len(self.output_table) + 7) // 8)
        for target, source in enumerate(self.output_table):
            if not target & 1023:
                self.check()
            if source >= 0 and h[source]:
                out[target >> 3] |= 1 << (target & 7)
        return int.from_bytes(out, "little")


class ComponentAlgebra:
    """Opt-in per-scanner adapter for the existing fastunknot.planar.Planar.

    Delegates all geometry and transfer work unchanged. Only composition of
    sufficiently dense operands is dispatched to ComponentPlan. No global
    monkey-patching; each scanner/race worker owns its adapter and stage cache.
    The thresholds are a transparent policy, not a proved speed prediction.
    """
    def __init__(self, original, *, max_entries: int = 1 << 18,
                 min_pairs: int = 256, check: Check = _noop):
        if type(min_pairs) is not int or min_pairs < 0:
            raise ValueError("min_pairs must be a nonnegative integer")
        if type(max_entries) is not int or max_entries < 0:
            raise ValueError("max_entries must be a nonnegative integer")
        self.original = original
        self.max_entries = max_entries
        self.min_pairs = min_pairs
        self.check = check
        self.kernels: dict[tuple[int, int, int], ComponentPlan | None] = {}
        self.kernel_stats = {"compressed_calls": 0, "baseline_calls": 0,
                             "compiled_plans": 0, "allocation_fallbacks": 0}

    def __getattr__(self, name):
        return getattr(self.original, name)

    def stage(self, *args, **kwargs):
        self.kernels.clear()
        return self.original.stage(*args, **kwargs)

    def compose(self, a: int, b: int, c: int, f: int, g: int) -> int:
        pairs = f.bit_count() * g.bit_count()
        if pairs < self.min_pairs:
            self.kernel_stats["baseline_calls"] += 1
            return self.original.compose(a, b, c, f, g)
        key = (a, b, c)
        if key not in self.kernels:
            old_plan = self.original.compose_plan(a, b, c)
            if old_plan is None:
                return 0
            components, _ = old_plan
            dim = dimensions(components)
            # Include a rough ranked-transform cost; deliberately conservative.
            work = dim.domain_entries + max(1, dim.components) * (1 << dim.components)
            if pairs < work:
                self.kernel_stats["baseline_calls"] += 1
                return self.original.compose(a, b, c, f, g)
            try:
                self.kernels[key] = ComponentPlan(components, max_entries=self.max_entries,
                                                  check=self.check)
                self.kernel_stats["compiled_plans"] += 1
            except KernelLimit:
                self.kernels[key] = None
                self.kernel_stats["allocation_fallbacks"] += 1
        kernel = self.kernels[key]
        if kernel is None:
            self.kernel_stats["baseline_calls"] += 1
            return self.original.compose(a, b, c, f, g)
        self.kernel_stats["compressed_calls"] += 1
        return kernel.compose(f, g)
