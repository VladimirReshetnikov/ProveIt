"""Exact dense cobordism composition by ranked subset convolution over F_2.

This standalone module preserves fastunknot's bit convention: coefficient of
the squarefree monomial indexed by mask is bit ``mask`` of a Python integer.
It does not mutate the existing implementation.  The optional AdaptivePlanar
adapter subclasses its Planar algebra and preserves its public interface.

The dense kernel is an application of Bjorklund--Husfeldt--Kaski--Koivisto,
"Fourier meets Mobius: fast subset convolution", STOC 2007.  No claim of a new
subset-convolution algorithm or a general quasipolynomial knot recognizer is
made here.
"""
from __future__ import annotations


def _check_bits(value: int, variables: int) -> None:
    if type(variables) is not int or variables < 0:
        raise ValueError("variable counts must be nonnegative integers")
    if type(value) is not int or value < 0 or value.bit_length() > (1 << variables):
        raise ValueError("morphism coefficients do not fit the given basis")


def _unpack(value: int, variables: int) -> list[int]:
    """Linear bit cost; avoid a sequence of whole-bigint shifts/XORs."""
    _check_bits(value, variables)
    count = 1 << variables
    raw = value.to_bytes((count + 7) // 8, "little")
    return [(raw[mask >> 3] >> (mask & 7)) & 1 for mask in range(count)]


def _pack(values) -> int:
    raw = bytearray((len(values) + 7) // 8)
    for mask, coefficient in enumerate(values):
        if coefficient:
            raw[mask >> 3] |= 1 << (mask & 7)
    return int.from_bytes(raw, "little")


def _coefficient_masks(value: int, variables: int) -> list[int]:
    """Enumerate set coefficient positions by small bytes, not large integers."""
    count = 1 << variables
    raw = value.to_bytes((count + 7) // 8, "little")
    masks = []
    for index, byte in enumerate(raw):
        while byte:
            low = byte & -byte
            masks.append((index << 3) + low.bit_length() - 1)
            byte ^= low
    return masks


def _carryless_product(left: int, right: int, rank_mask: int) -> int:
    """Multiply F_2[t] polynomials and retain ranks at most r.

    Both operands have O(r) bits, unlike a full morphism's 2**r bits.
    """
    if left.bit_count() > right.bit_count():
        left, right = right, left
    result = 0
    while left:
        low = left & -left
        result ^= right << (low.bit_length() - 1)
        left ^= low
    return result & rank_mask


def _zeta_in_place(values: list[int], variables: int) -> None:
    """In characteristic two, this is also the Mobius inverse."""
    count = 1 << variables
    step = 1
    while step < count:
        for start in range(0, count, step << 1):
            for offset in range(step):
                high = start + step + offset
                values[high] ^= values[start + offset]
        step <<= 1


def _homogeneous_degree(values):
    degree = -1
    for mask, coefficient in enumerate(values):
        if coefficient:
            current = mask.bit_count()
            if degree < 0:
                degree = current
            elif degree != current:
                return None
    return degree


def _squarefree_arrays(left: list[int], right: list[int], variables: int) -> list[int]:
    """Disjoint subset convolution; O(r^2 2^r) F_2 operations.

    Rank-polynomial coefficients are packed into O(r)-bit integers.  Ordinary
    unranked zeta multiplication would produce OR-convolution and be wrong:
    e.g. it would assign x*x=x instead of x*x=0.
    """
    count = 1 << variables
    left_degree, right_degree = _homogeneous_degree(left), _homogeneous_degree(right)
    if left_degree == -1 or right_degree == -1:
        return [0] * count
    if left_degree is not None and right_degree is not None:
        total_degree = left_degree + right_degree
        if total_degree > variables:
            return [0] * count
        # OR-convolution, restricted to the only possible disjoint-union rank.
        lf, rg = left.copy(), right.copy()
        _zeta_in_place(lf, variables)
        _zeta_in_place(rg, variables)
        for mask in range(count):
            lf[mask] &= rg[mask]
        _zeta_in_place(lf, variables)
        return [coefficient if mask.bit_count() == total_degree else 0
                for mask, coefficient in enumerate(lf)]
    lf = [coefficient << mask.bit_count() for mask, coefficient in enumerate(left)]
    rg = [coefficient << mask.bit_count() for mask, coefficient in enumerate(right)]
    _zeta_in_place(lf, variables)
    _zeta_in_place(rg, variables)
    rank_mask = (1 << (variables + 1)) - 1
    for mask in range(count):
        lf[mask] = _carryless_product(lf[mask], rg[mask], rank_mask)
    _zeta_in_place(lf, variables)
    return [(lf[mask] >> mask.bit_count()) & 1 for mask in range(count)]


def squarefree_product(left: int, right: int, variables: int) -> int:
    """Multiply in F_2[x_1,...,x_r]/(x_1^2,...,x_r^2)."""
    return _pack(_squarefree_arrays(_unpack(left, variables),
                                    _unpack(right, variables), variables))


def _owner_map(components, side: int, variables: int) -> list[int]:
    owner = [-1] * variables
    for component_id, component in enumerate(components):
        mask = component[side]
        if type(mask) is not int or mask < 0 or mask.bit_length() > variables:
            raise ValueError("plan mask does not fit its basis")
        while mask:
            low = mask & -mask
            index = low.bit_length() - 1
            if owner[index] != -1:
                raise ValueError("plan component masks must be disjoint")
            owner[index] = component_id
            mask ^= low
    if any(index == -1 for index in owner):
        raise ValueError("plan component masks must cover every basis variable")
    return owner


def _contraction_table(owner: list[int]) -> list[int]:
    table = [0] * (1 << len(owner))
    for mask in range(1, len(table)):
        low = mask & -mask
        previous = table[mask ^ low]
        target = 1 << owner[low.bit_length() - 1]
        table[mask] = -1 if previous < 0 or previous & target else previous | target
    return table


class FastCompositionPlan:
    """Compiled exact factorization of a genus-zero gluing plan.

    ``components`` is None (positive genus, hence zero over F_2) or a sequence
    of (left_mask, right_mask, boundary_mask, extra_dots[, choices]) tuples.
    Each side's masks must partition its specified basis.  Closed components
    (boundary_mask=0) and any nonnegative number of extra dots are supported.
    The optional fifth entry is ignored: output choices are reconstructed.

    Precomputation and one apply use
    O(poly(kL+kR+kO+r)*(2^kL+2^kR+2^kO+2^r)) bit operations.
    In actual arc-matching composition, r<=min(kL,kR)<=frontier/2.
    A completely general list of components need not satisfy that inequality.
    """

    def __init__(self, components, left_vars: int, right_vars: int, output_vars: int):
        for variables in (left_vars, right_vars, output_vars):
            _check_bits(0, variables)
        self.left_vars, self.right_vars, self.output_vars = left_vars, right_vars, output_vars
        self.zero = components is None
        self.components = None if components is None else tuple(tuple(c[:4]) for c in components)
        self.variables = 0 if self.zero else len(self.components)
        if self.zero:
            return
        if any(len(c) != 4 for c in self.components):
            raise ValueError("each component needs four fields")
        for component in self.components:
            if type(component[3]) is not int or component[3] < 0:
                raise ValueError("extra dot counts must be nonnegative integers")
        left_owner = _owner_map(self.components, 0, left_vars)
        right_owner = _owner_map(self.components, 1, right_vars)
        _owner_map(self.components, 2, output_vars)
        if any(c[3] >= 2 for c in self.components):
            self.zero = True
            return
        self.left_table = _contraction_table(left_owner)
        self.right_table = _contraction_table(right_owner)
        self.output_table = []
        for output_mask in range(1 << output_vars):
            required = 0
            for index, (_, _, boundary, extra) in enumerate(self.components):
                if boundary:
                    missing = (boundary & ~output_mask).bit_count()
                    if missing > 1:
                        required = -1
                        break
                    final_dot = int(missing == 0)
                else:
                    final_dot = 1  # counit(1)=0 and counit(x)=1
                if final_dot < extra:
                    required = -1
                    break
                if final_dot - extra:
                    required |= 1 << index
            self.output_table.append(required)

    def _contract(self, value: int, variables: int, table: list[int]) -> list[int]:
        count = 1 << variables
        raw = value.to_bytes((count + 7) // 8, "little")
        contracted = [0] * (1 << self.variables)
        for mask, target in enumerate(table):
            if target >= 0 and ((raw[mask >> 3] >> (mask & 7)) & 1):
                contracted[target] ^= 1
        return contracted

    def apply(self, left: int, right: int) -> int:
        _check_bits(left, self.left_vars)
        _check_bits(right, self.right_vars)
        if self.zero or not left or not right:
            return 0
        lf = self._contract(left, self.left_vars, self.left_table)
        rg = self._contract(right, self.right_vars, self.right_table)
        product = _squarefree_arrays(lf, rg, self.variables)
        return _pack([0 if source < 0 else product[source] for source in self.output_table])


def compose_plan_fast(components, left: int, right: int,
                      left_vars: int, right_vars: int, output_vars: int) -> int:
    """Convenience entry point; reuse FastCompositionPlan for repeated calls."""
    return FastCompositionPlan(components, left_vars, right_vars, output_vars).apply(left, right)


def _sparse_compose(components, left: int, right: int,
                    left_vars: int, right_vars: int, output_vars: int) -> int:
    """Accumulate individual output bits; never XOR full morphisms per pair.

    For boundary sizes b_j a monomial pair produces at most
    D=product(max(1,b_j)) output monomials.  The adapter uses this certified
    bound to keep its sparse path within the dense asymptotic budget.
    """
    ls = _coefficient_masks(left, left_vars)
    rs = _coefficient_masks(right, right_vars)
    raw = bytearray(((1 << output_vars) + 7) // 8)
    prepared = []
    for lm, rm, boundary, extra, *_ in components:
        choices = []
        remaining = boundary
        while remaining:
            low = remaining & -remaining
            choices.append(boundary ^ low)
            remaining ^= low
        prepared.append((lm, rm, boundary, extra, tuple(choices)))
    for lm in ls:
        for rm in rs:
            terms = [0]
            for left_mask, right_mask, boundary, extra, choices in prepared:
                dots = (lm & left_mask).bit_count() + (rm & right_mask).bit_count() + extra
                if dots > 1 or (not boundary and dots != 1):
                    terms = []
                    break
                if dots:
                    terms = [term | boundary for term in terms]
                else:
                    terms = [term | choice for term in terms for choice in choices]
            for monomial in terms:
                raw[monomial >> 3] ^= 1 << (monomial & 7)
    return int.from_bytes(raw, "little")


try:
    from fastunknot.planar import Planar
except ImportError:
    Planar = None


if Planar is not None:
    class AdaptivePlanar(Planar):
        """Drop-in adapter; sparse plans use byte-array monomial accumulation.

        The switch compares a rigorous upper bound for sparse work to dense
        work, up to polynomial factors.  Both selected paths satisfy the
        advertised exponential bound in a bit-cost model.  The multiplicative
        dense_factor tunes a constant only.  ``force_dense`` is for verification.
        """

        def __init__(self, *, shape_cache=True, force_dense=False, dense_factor=2):
            if not isinstance(dense_factor, (int, float)) or not 0 < dense_factor < float("inf"):
                raise ValueError("dense_factor must be a positive finite constant")
            self.force_dense = force_dense
            self.dense_factor = dense_factor
            self.fast_plans = {}
            self.transfer_mask_memos = {}
            self.dense_calls = 0
            self.sparse_calls = 0
            self.dense_transfer_calls = 0
            self.sparse_transfer_calls = 0
            super().__init__(shape_cache=shape_cache)

        def stage(self, points, slots):
            super().stage(points, slots)
            self.fast_plans = {}
            self.transfer_mask_memos = {}

        def compose(self, a, b, c, f, g):
            if not f or not g:
                return 0
            if f == 1 and a == b:
                return g
            if g == 1 and b == c:
                return f
            if a == b == c and f == g:
                return f & 1
            raw = self.compose_plan(a, b, c)
            if raw is None:
                return 0
            components, _ = raw
            k_left = self.basis(a, b)[1]
            k_right = self.basis(b, c)[1]
            k_out = self.basis(a, c)[1]
            variables = len(components)
            estimate = ((k_left + 1) * (1 << k_left) + (k_right + 1) * (1 << k_right)
                        + (k_out + 1) * (variables + 1) * (1 << k_out)
                        + (variables + 1) ** 2 * (1 << variables))
            expansion_bound = 1
            for comp in components:
                expansion_bound *= max(1, comp[2].bit_count())
            sparse_bound = f.bit_count() * g.bit_count() * (
                variables + 1 + (k_out + 1) * expansion_bound)
            if not self.force_dense and sparse_bound <= self.dense_factor * estimate:
                self.sparse_calls += 1
                return _sparse_compose(components, f, g, k_left, k_right, k_out)
            self.dense_calls += 1
            key = (a, b, c)
            compiled = self.fast_plans.get(key)
            if compiled is None:
                compiled = self.fast_plans[key] = FastCompositionPlan(
                    components, k_left, k_right, k_out)
            return compiled.apply(f, g)

        def transfer(self, a, b, f, i_src, i_tgt):
            """Exact crossing transfer with linear-size packed input/output.

            The inherited path remains useful for at most 32 input monomials;
            that fixed cap also gives its whole-bigint operations a safe
            O(poly(m)*2^m) bound.  Larger supports use byte accumulation.
            """
            if not f:
                return ()
            if not self.force_dense and f.bit_count() <= 32:
                self.sparse_transfer_calls += 1
                return super().transfer(a, b, f, i_src, i_tgt)
            self.dense_transfer_calls += 1
            plans, touched_mask, renumber, _ = self.transfer_plan(a, b, i_src, i_tgt)
            if not plans:
                return ()
            key = (a, b, i_src, i_tgt)
            memo = self.transfer_mask_memos.setdefault(key, {})
            k_left = self.basis(a, b)[1]
            new_a = self.glue(a, i_src)[0]
            new_b = self.glue(b, i_tgt)[0]
            k_out = self.basis(new_a, new_b)[1]
            size = ((1 << k_out) + 7) // 8
            buffers = [bytearray(size) for _ in plans]
            for monomial in _coefficient_masks(f, k_left):
                core = monomial & touched_mask
                values = memo.get(core)
                if values is None:
                    local_values = []
                    for _, _, components in plans:
                        terms = [0]
                        for left, _, boundary, extra, choices in components:
                            dots = (core & left).bit_count() + extra
                            if dots > 1 or (not boundary and dots != 1):
                                terms = []
                                break
                            if dots:
                                terms = [term | boundary for term in terms]
                            else:
                                terms = [term | choice for term in terms for choice in choices]
                        local_values.append(tuple(terms))
                    values = memo[core] = tuple(local_values)
                rest = monomial ^ core
                shift = 0
                while rest:
                    low = rest & -rest
                    shift |= renumber[low]
                    rest ^= low
                for buffer, local_terms in zip(buffers, values):
                    for term in local_terms:
                        output_mask = term | shift
                        buffer[output_mask >> 3] ^= 1 << (output_mask & 7)
            result = []
            for plan, buffer in zip(plans, buffers):
                value = int.from_bytes(buffer, "little")
                if value:
                    result.append((plan[0], plan[1], value))
            return tuple(result)

