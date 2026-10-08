"""Exact radical transfer for the characteristic-two Khovanov arc category.

SPDX-License-Identifier: MIT-0
No floating-point calculations. Objects have an interned boundary matching and
an unnormalised homological degree. Quantum gradings are intentionally forgotten,
as in the audited reference scanner. Resource limits are never knot verdicts.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import defaultdict
from pathlib import Path
import sys
from typing import Callable

VENDOR = Path(__file__).resolve().parents[1] / 'vendor'
if str(VENDOR) not in sys.path:
    sys.path.insert(0, str(VENDOR))
from reference_planar import ReferencePlanar, matchings


def bits(x: int):
    while x:
        low = x & -x
        yield low.bit_length() - 1
        x ^= low


def derivative(f: int) -> int:
    """Sum of formal derivatives on F2[x_1,...,x_c]/(x_i^2)."""
    out = 0
    for mask in bits(f):
        for i in bits(mask):
            out ^= 1 << (mask ^ (1 << i))
    return out


class ArcAlgebra(ReferencePlanar):
    """Repository composition excerpt with scalar shortcuts and counters."""
    def __init__(self, check: Callable[[], None] = lambda: None):
        super().__init__()
        self.check = check
        self.calls = 0
        self.nontrivial_calls = 0

    def compose(self, a: int, b: int, c: int, f: int, g: int) -> int:
        self.calls += 1
        self.check()
        if not f or not g:
            return 0
        if a == b and f == 1:
            return g
        if b == c and g == 1:
            return f
        if a == b == c and f == g:
            return f & 1
        self.nontrivial_calls += 1
        return super().compose(a, b, c, f, g)

    def weights(self, a: int, b: int, f: int) -> set[int]:
        k, c = len(self.pairs[a]), self.basis(a, b)[1]
        return {k - c + 2*s.bit_count() for s in bits(f)}


@dataclass(frozen=True)
class Obj:
    matching: int
    degree: int


@dataclass
class Mat:
    """Column-sparse matrix; entries are packed dotted-monomial polynomials."""
    src: tuple[Obj, ...]
    dst: tuple[Obj, ...]
    cols: list[dict[int, int]]

    def __post_init__(self):
        if len(self.cols) != len(self.src):
            raise ValueError('wrong number of columns')
        for col in self.cols:
            if any(type(i) is not int or i < 0 or i >= len(self.dst)
                   or type(v) is not int or v <= 0 for i, v in col.items()):
                raise ValueError('invalid matrix entry')

    @property
    def nnz(self) -> int:
        return sum(map(len, self.cols))

    def is_zero(self) -> bool:
        return not any(self.cols)

    def copy(self) -> Mat:
        return Mat(self.src, self.dst, [dict(c) for c in self.cols])


def zero(src, dst) -> Mat:
    return Mat(tuple(src), tuple(dst), [{} for _ in src])


def identity(objects) -> Mat:
    objects = tuple(objects)
    return Mat(objects, objects, [{i: 1} for i in range(len(objects))])


def add(a: Mat, b: Mat) -> Mat:
    if a.src != b.src or a.dst != b.dst:
        raise ValueError('incompatible matrix addition')
    out = a.copy()
    for j, col in enumerate(b.cols):
        for i, v in col.items():
            w = out.cols[j].get(i, 0) ^ v
            if w:
                out.cols[j][i] = w
            else:
                out.cols[j].pop(i, None)
    return out


def mul(a: Mat, b: Mat, alg: ArcAlgebra) -> Mat:
    """a after b. The scalar fast path also works for scalar h,i,p."""
    if a.src != b.dst:
        raise ValueError('incompatible matrix multiplication')
    out = zero(b.src, a.dst)
    for j, col in enumerate(b.cols):
        source = b.src[j].matching
        acc = out.cols[j]
        for mid, f in col.items():
            middle = b.dst[mid].matching
            for i, g in a.cols[mid].items():
                if f == 1 and source == middle:
                    term = g
                elif g == 1 and middle == a.dst[i].matching:
                    term = f
                else:
                    term = alg.compose(source, middle, a.dst[i].matching, f, g)
                if term:
                    value = acc.get(i, 0) ^ term
                    if value:
                        acc[i] = value
                    else:
                        acc.pop(i, None)
        alg.check()
    return out


def residue(d: Mat) -> Mat:
    return Mat(d.src, d.dst, [
        {i: 1 for i, v in col.items()
         if v & 1 and d.src[j].matching == d.dst[i].matching}
        for j, col in enumerate(d.cols)])


def validate_complex(d: Mat, alg: ArcAlgebra, square: bool = True) -> int:
    if d.src != d.dst:
        raise ValueError('differential is not an endomorphism')
    endpoints = None
    k = 0
    for o in d.src:
        pairs = alg.pairs[o.matching]
        here = frozenset(x for pair in pairs for x in pair)
        if endpoints is None:
            endpoints = here
            k = len(pairs)
        if here != endpoints or len(pairs)*2 != len(here):
            raise ValueError('objects do not share a matching boundary')
    for j, col in enumerate(d.cols):
        for i, f in col.items():
            if d.dst[i].degree != d.src[j].degree+1:
                raise ValueError('differential must have homological degree +1')
            c = alg.basis(d.src[j].matching, d.dst[i].matching)[1]
            if f.bit_length() > (1 << c):
                raise ValueError('morphism exceeds its basis')
    if square and not mul(d, d, alg).is_zero():
        raise ValueError('d squared is nonzero')
    return k


def rank_binary(columns: list[int]) -> int:
    pivots = {}
    for value in columns:
        while value:
            top = value.bit_length()-1
            if top not in pivots:
                pivots[top] = value
                break
            value ^= pivots[top]
    return len(pivots)


def image_kernel(columns: list[int]):
    """Independent images, their preimages, and a basis for the kernel."""
    pivots = {}
    image, lift, kernel = [], [], []
    for j, value in enumerate(columns):
        preimage = 1 << j
        while value:
            top = value.bit_length()-1
            if top not in pivots:
                pivots[top] = (value, preimage)
                image.append(value)
                lift.append(preimage)
                break
            a, b = pivots[top]
            value ^= a
            preimage ^= b
        if not value:
            kernel.append(preimage)
    return image, lift, kernel


def complement(initial: list[int], candidates: list[int]) -> list[int]:
    pivots = {}
    selected = []
    for is_candidate, value0 in [(False, x) for x in initial] + [(True, x) for x in candidates]:
        value = value0
        while value:
            top = value.bit_length()-1
            if top not in pivots:
                pivots[top] = value
                if is_candidate:
                    selected.append(value0)
                break
            value ^= pivots[top]
    return selected


def inverse_binary(columns: list[int]) -> list[int]:
    """Inverse rows of an invertible binary matrix supplied as columns."""
    n = len(columns)
    rows = [sum(((col >> r) & 1) << c for c, col in enumerate(columns)) | (1 << (n+r))
            for r in range(n)]
    for c in range(n):
        pivot = next((r for r in range(c, n) if rows[r] >> c & 1), None)
        if pivot is None:
            raise ArithmeticError('singular change of basis')
        rows[c], rows[pivot] = rows[pivot], rows[c]
        for r in range(n):
            if r != c and rows[r] >> c & 1:
                rows[r] ^= rows[c]
    return [row >> n for row in rows]


def grouped_residue(d: Mat):
    groups = defaultdict(list)
    for j, o in enumerate(d.src):
        groups[(o.matching, o.degree)].append(j)
    maps = {}
    for key, ids in groups.items():
        target_ids = groups.get((key[0], key[1]+1), [])
        index = {j: i for i, j in enumerate(target_ids)}
        maps[key] = [sum(1 << index[i] for i, v in d.cols[j].items()
                         if i in index and v & 1) for j in ids]
    return dict(groups), maps


def survivor_profile(d: Mat) -> dict:
    """Exact minimal object multiplicities, not a knot verdict.

    Requires a valid differential. A separate validation function is provided
    so production callers need not pay for d^2 on each diagnostic invocation.
    """
    groups, maps = grouped_residue(d)
    ranks = {key: rank_binary(cols) for key, cols in maps.items()}
    profile = {}
    for key, ids in groups.items():
        mu = len(ids)-ranks[key]-ranks.get((key[0], key[1]-1), 0)
        if mu < 0:
            raise ArithmeticError('negative residue homology dimension')
        if mu:
            profile[key] = mu
    return profile


@dataclass
class Contraction:
    d0: Mat
    i: Mat
    p: Mat
    h: Mat
    profile: dict


def scalar_contraction(d: Mat) -> Contraction:
    """Split d0 using only binary linear algebra, no cobordism products."""
    d0 = residue(d)
    groups, maps = grouped_residue(d0)
    data = {key: image_kernel(cols) for key, cols in maps.items()}
    local = {}
    survivors = []
    profile = {}
    for key in sorted(groups):
        previous = (key[0], key[1]-1)
        boundary = data.get(previous, ([], [], []))[0]
        _, lift, kernel = data[key]
        homology = complement(boundary, kernel)
        basis = boundary+homology+lift
        if len(basis) != len(groups[key]):
            raise ArithmeticError('residue is not a complex or splitting failed')
        inv = inverse_binary(basis)
        offset = len(survivors)
        survivors.extend([Obj(*key)]*len(homology))
        if homology:
            profile[key] = len(homology)
        local[key] = (boundary, homology, inv, offset)
    survivors = tuple(survivors)
    i, p, h = zero(survivors, d.src), zero(d.src, survivors), zero(d.src, d.src)
    for key, ids in groups.items():
        boundary, homology, inv, offset = local[key]
        for t, vector in enumerate(homology):
            i.cols[offset+t] = {ids[r]: 1 for r in bits(vector)}
            for r in bits(inv[len(boundary)+t]):
                p.cols[ids[r]][offset+t] = 1
        prev_ids = groups.get((key[0], key[1]-1), [])
        prev_lifts = data.get((key[0], key[1]-1), ([], [], []))[1]
        for t in range(len(boundary)):
            for r in bits(inv[t]):
                col = h.cols[ids[r]]
                for s in bits(prev_lifts[t]):
                    idx = prev_ids[s]
                    if idx in col:
                        del col[idx]
                    else:
                        col[idx] = 1
    return Contraction(d0, i, p, h, profile)


def series_apply(h: Mat, delta: Mat, v: Mat, ell: int, alg: ArcAlgebra) -> tuple[Mat, int]:
    """Apply sum_{r=0}^{ell-1}(h delta)^r without forming h delta."""
    total, term, depth = v.copy(), v, 0
    for r in range(1, ell):
        term = mul(h, mul(delta, term, alg), alg)
        if term.is_zero():
            break
        total = add(total, term)
        depth = r
    return total, depth


@dataclass
class Transfer:
    original: Mat
    d: Mat
    i: Mat
    p: Mat | None
    h: Mat | None
    profile: dict
    radical_index_bound: int
    series_depth: int


def transfer(d: Mat, alg: ArcAlgebra, *, certificate: bool = False,
             validate: bool = True, survivor_limit: int | None = None) -> Transfer:
    """Finite homological perturbation, with an optional full contraction.

    Raises MemoryError before transfer products if the predicted survivor count
    exceeds a requested ceiling. Optional input validation may multiply first.
    This is a resource outcome, never a verdict.
    """
    if survivor_limit is not None and (type(survivor_limit) is not int or survivor_limit < 0):
        raise ValueError('survivor_limit must be nonnegative')
    k = validate_complex(d, alg, square=validate)
    predicted = survivor_profile(d)
    if survivor_limit is not None and sum(predicted.values()) > survivor_limit:
        raise MemoryError('certified minimal survivor count exceeds limit')
    s = scalar_contraction(d)
    delta = add(d, s.d0)
    ell = max(1, 2*k)
    i, depth = series_apply(s.h, delta, s.i, ell, alg)
    new_d = mul(s.p, mul(delta, i, alg), alg)
    if not residue(new_d).is_zero():
        raise ArithmeticError('transferred differential is not radical')
    p = h = None
    if certificate:
        h, _ = series_apply(s.h, delta, s.h, ell, alg)
        p, term = s.p.copy(), s.p
        for _ in range(1, ell):
            term = mul(mul(term, delta, alg), s.h, alg)
            if term.is_zero():
                break
            p = add(p, term)
    return Transfer(d, new_d, i, p, h, s.profile, ell, depth)


def check_contraction(t: Transfer, alg: ArcAlgebra) -> dict[str, bool]:
    if t.p is None or t.h is None:
        raise ValueError('full certificate was not requested')
    d, D, i, p, h = t.original, t.d, t.i, t.p, t.h
    checks = {
        'd_squared': mul(d, d, alg).is_zero(),
        'D_squared': mul(D, D, alg).is_zero(),
        'i_chain_map': mul(d, i, alg) == mul(i, D, alg),
        'p_chain_map': mul(p, d, alg) == mul(D, p, alg),
        'pi_identity': mul(p, i, alg) == identity(D.src),
        'homotopy': add(identity(d.src), mul(i, p, alg)) == add(mul(d, h, alg), mul(h, d, alg)),
        'h_squared': mul(h, h, alg).is_zero(),
        'hi_zero': mul(h, i, alg).is_zero(),
        'ph_zero': mul(p, h, alg).is_zero(),
        'minimal': residue(D).is_zero(),
    }
    if not all(checks.values()):
        raise ArithmeticError(f'invalid contraction: {checks}')
    return checks


def pivot_reduce(d: Mat, alg: ArcAlgebra) -> Mat:
    """Independent scalar-unit cancellation baseline; min-fill pivot rule."""
    objects = d.src
    out = {j: dict(col) for j, col in enumerate(d.cols)}
    active = set(range(len(objects)))
    while True:
        inc = defaultdict(set)
        for j in active:
            for i in out[j]:
                inc[i].add(j)
        candidates = (( (len(out[b])-1)*(len(inc[c])-1), b, c)
                      for b in active for c, f in out[b].items()
                      if objects[b].matching == objects[c].matching and f & 1)
        best = min(candidates, default=None)
        if best is None:
            break
        _, b, c = best
        m = objects[b].matching
        inverse = out[b][c]  # scalar End(m) unit, NOT a block-matrix unit
        for a in list(inc[c]-{b}):
            half = alg.compose(objects[a].matching, m, m, out[a][c], inverse)
            for f, gamma in list(out[b].items()):
                if f == c:
                    continue
                term = alg.compose(objects[a].matching, m, objects[f].matching, half, gamma)
                if term:
                    val = out[a].get(f, 0)^term
                    if val:
                        out[a][f] = val
                    else:
                        out[a].pop(f, None)
        active.remove(b); active.remove(c)
        for j in active:
            out[j].pop(b, None); out[j].pop(c, None)
        out.pop(b); out.pop(c)
        alg.check()
    ids = sorted(active)
    index = {j: i for i, j in enumerate(ids)}
    obs = tuple(objects[j] for j in ids)
    return Mat(obs, obs, [{index[i]: v for i, v in out[j].items()} for j in ids])


def marked_dot(f: Mat, alg: ArcAlgebra, point: int) -> Mat:
    """Multiply every entry by the central dot at a fixed boundary point."""
    out=zero(f.src,f.dst)
    for j,col in enumerate(f.cols):
        for i,value in col.items():
            owner,_=alg.basis(f.src[j].matching,f.dst[i].matching)
            if point not in owner: raise ValueError('marked point is not on the common boundary')
            mark=1<<owner[point]; image=0
            for mask in bits(value):
                if not mask&mark: image ^= 1<<(mask|mark)
            if image: out.cols[j][i]=image
    return out


def dot_derivative(f: Mat) -> Mat:
    out=zero(f.src,f.dst)
    for j,col in enumerate(f.cols):
        for i,value in col.items():
            image=derivative(value)
            if image: out.cols[j][i]=image
    return out


def transfer_marked(d: Mat, alg: ArcAlgebra, point: int, *, validate: bool = True) -> Transfer:
    """Certified two-pass transfer through ker(dot_derivative).

    This proof-oriented variant uses full encodings and a full intermediate
    contraction. It is not claimed to save time or memory in this implementation.
    A reduced-basis implementation can exploit the factor-two Hom dimension.
    """
    k=validate_complex(d,alg,square=validate)
    if not k or (d.src and point not in alg.partner[d.src[0].matching]):
        raise ValueError('marked transfer needs a nonempty marked boundary')
    e=dot_derivative(d)
    dB=add(d,marked_dot(e,alg,point))
    base=transfer(dB,alg,certificate=True,validate=validate)
    def zmul(a,b): return marked_dot(mul(a,b,alg),alg,point)
    ei=mul(e,base.i,alg); eh=mul(e,base.h,alg)
    D=add(base.d,zmul(base.p,ei))
    I=add(base.i,zmul(base.h,ei))
    P=add(base.p,zmul(base.p,eh))
    H=add(base.h,zmul(base.h,eh))
    return Transfer(d,D,I,P,H,base.profile,max(1,2*k),base.series_depth)
