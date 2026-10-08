"""Certified rank primitives for D = direct_sum(A_nu tensor I) + U V over F_2.

The certificate establishes a chain-complex calculation, NOT association with a
knot diagram. Only a separate trusted diagram-to-complex construction may turn
rank_two into an unknot verdict.
"""
from __future__ import annotations
from dataclasses import dataclass
from . import gf2
from .automata import Register, product_register


@dataclass(frozen=True)
class TemplateBlock:
    differential: tuple[int, ...]
    degrees: tuple[int, ...]
    register: Register

    @property
    def size(self) -> int:
        return len(self.degrees)

    def to_dict(self) -> dict:
        return {'differential': list(self.differential), 'degrees': list(self.degrees),
                'register': self.register.to_dict()}


@dataclass(frozen=True)
class PortComplex:
    blocks: tuple[TemplateBlock, ...]
    port_degrees: tuple[int, ...]

    def __post_init__(self):
        r = len(self.port_degrees)
        if any(type(h) is not int for h in self.port_degrees):
            raise ValueError('port degrees must be integers')
        for block in self.blocks:
            d = block.size
            if any(type(h) is not int for h in block.degrees):
                raise ValueError('template degrees must be integers')
            if len(block.differential) != d:
                raise ValueError('template is not square')
            gf2.check_rows(block.differential, d)
            if block.register.output_count != 2*d*r:
                raise ValueError('register must output d*r U entries, then d*r V entries')
            for target, row in enumerate(block.differential):
                for source in gf2.bits(row):
                    if block.degrees[target] != block.degrees[source]+1:
                        raise ValueError('base differential is not homogeneous of degree one')
            if any(gf2.mul(block.differential, block.differential)):
                raise ValueError('base differential does not square to zero')

    @property
    def ports(self) -> int:
        return len(self.port_degrees)

    @property
    def dimension(self) -> int:
        return sum(block.size << block.register.length for block in self.blocks)

    def to_dict(self) -> dict:
        return {'format': 'portkh-1', 'port_degrees': list(self.port_degrees),
                'blocks': [block.to_dict() for block in self.blocks]}

    @classmethod
    def from_dict(cls, obj: dict) -> 'PortComplex':
        if not isinstance(obj, dict):
            raise ValueError('JSON object required')
        if obj.get('format') != 'portkh-1':
            raise ValueError('unsupported presentation format')
        return cls(tuple(TemplateBlock(tuple(b['differential']), tuple(b['degrees']),
                                       Register.from_dict(b['register'])) for b in obj['blocks']),
                   tuple(obj['port_degrees']))


def _fields(value: int, d: int, r: int) -> tuple[list[int], list[int]]:
    mask = (1 << r)-1
    u = [(value >> (t*r)) & mask for t in range(d)]
    vcols = [(value >> ((d+t)*r)) & mask for t in range(d)]
    return u, vcols


def _act(matrix: list[int] | tuple[int, ...], coeff: list[list[int]]) -> list[list[int]]:
    """Template action on d arrays of B rows, with r port bits per row."""
    b = len(coeff[0]) if coeff else 0
    result = []
    for row in matrix:
        acc = [0]*b
        for j in gf2.bits(row):
            acc = [a ^ c for a, c in zip(acc, coeff[j])]
        result.append(acc)
    return result


def _pair(vcoeff: list[list[int]], w: list[int], ucoeff: list[list[int]], r: int) -> list[int]:
    total = [0]*r
    for vv, uu in zip(vcoeff, ucoeff):
        part = gf2.mul(gf2.transpose(vv, r), gf2.mul(w, uu))
        total = gf2.add(total, part)
    return total


def analyze(complex_: PortComplex) -> dict:
    """Validate degree and D^2=0, then compute exact total homology dimension.

    No array in this function is indexed by all 2^m register words.
    """
    r = complex_.ports
    records = []
    vu = [0]*r
    vhu = [0]*r
    base_rank = 0
    for block_index, block in enumerate(complex_.blocks):
        a, d, reg = block.differential, block.size, block.register
        h, q = gf2.generalized_inverse(a, d)
        base_rank += q << reg.length
        reach = reg.reachable()
        evaluations = reach['evaluation_rows']
        values = [_fields(f, d, r) for f in evaluations]
        for uu, vv in values:
            for t in range(d):
                for j in gf2.bits(uu[t]):
                    if block.degrees[t] != complex_.port_degrees[j]+1:
                        raise ValueError(f'U has wrong degree in block {block_index}')
                for j in gf2.bits(vv[t]):
                    if block.degrees[t] != complex_.port_degrees[j]:
                        raise ValueError(f'V has wrong degree in block {block_index}')
        # Extract small coefficient matrices without ever constructing an output Gram matrix.
        mask = (1 << r)-1
        uc = [[(f >> (t*r)) & mask for f in reg.outputs] for t in range(d)]
        vc = [[(f >> ((d+t)*r)) & mask for f in reg.outputs] for t in range(d)]
        w = reg.state_gram()
        vu = gf2.add(vu, _pair(vc, w, uc, r))
        vhu = gf2.add(vhu, _pair(vc, w, _act(h, uc), r))
        records.append({'block': block, 'h': h, 'rank': q, 'reach': reach, 'values': values})

    # D^2 = [A U + U(VU), U] [V ; V A]. Actual row/column span bases suffice.
    left_square_rows, right_square_cols = [], []
    u0_rows, v0_cols = [], []
    for rec in records:
        block, h = rec['block'], rec['h']
        a, d = block.differential, block.size
        ah, ha = gf2.mul(a, h), gf2.mul(h, a)
        at, hat = gf2.transpose(a, d), gf2.transpose(ha, d)
        for uu, vv in rec['values']:
            au = gf2.mul(a, uu)
            um = gf2.mul(uu, vu)
            va = gf2.mul(at, vv)
            left_square_rows.extend((x ^ y) | (u << r) for x, y, u in zip(au, um, uu))
            right_square_cols.extend(v | (v_a << r) for v, v_a in zip(vv, va))
            u0_rows.extend(gf2.add(uu, gf2.mul(ah, uu)))
            v0_cols.extend(gf2.add(vv, gf2.mul(hat, vv)))
    left_basis = gf2.independent(left_square_rows)
    right_basis = gf2.independent(right_square_cols)
    if any((l & rr).bit_count() & 1 for l in left_basis for rr in right_basis):
        raise ValueError('coupled differential does not square to zero')

    middle = gf2.add(gf2.identity(r), vhu)
    core, aa, bb = gf2.border_core(u0_rows, v0_cols, middle, r)
    core_rank = gf2.rank(core)
    differential_rank = base_rank + core_rank-r
    n = complex_.dimension
    beta0 = n-2*base_rank
    beta = n-2*differential_rank
    if not 0 <= beta <= n or not 0 <= differential_rank <= n//2:
        raise ArithmeticError('invalid homology dimension after verified square-zero test')
    if abs(beta-beta0) > 2*r:
        raise ArithmeticError('rank-perturbation inequality violated')
    return {
        'format': 'portkh-certificate-1',
        'dimension': n, 'ports': r, 'base_differential_rank': base_rank,
        'base_homology_dimension': beta0, 'differential_rank': differential_rank,
        'homology_dimension': beta, 'rank_two': beta == 2,
        'topological_verdict': None,
        'rank_two_obstruction_from_budget': beta0 > 2*r+2,
        'base_dimension_safe_cap': min(beta0, 2*r+3),
        'left_quotient_rank': aa, 'right_quotient_rank': bb,
        'core_shape': [aa+r, bb+r], 'core_rank': core_rank,
        'core_rows': core, 'middle_rows': middle,
        'square_zero_left_rank': len(left_basis),
        'square_zero_right_rank': len(right_basis),
        'register_summaries': [
            {'length': rec['block'].register.length,
             'template_size': rec['block'].size,
             'template_rank': rec['rank'],
             'maximum_width': max(rec['block'].register.widths),
             'reachable_dimensions': rec['reach']['reachable_dimensions'],
             'candidate_rows': rec['reach']['candidate_rows'],
             'evaluation_rank': len(rec['reach']['evaluation_rows']),
             'evaluation_witnesses': rec['reach']['witnesses']}
            for rec in records],
        'scope': 'Exact binary chain-complex rank; no diagram-to-complex provenance is inferred.'
    }


def expand(complex_: PortComplex, *, max_dimension: int = 4096) -> tuple[list[int], list[int]]:
    """Audit oracle only: materialize small presentations. Refuses oversized input."""
    n, r = complex_.dimension, complex_.ports
    if n > max_dimension:
        raise ValueError(f'expansion of dimension {n} exceeds audit cap {max_dimension}')
    a = [0]*n
    u = [0]*n
    vcols = [0]*n
    degrees = [0]*n
    offset = 0
    for block in complex_.blocks:
        d, m = block.size, block.register.length
        copies = 1 << m
        for x in range(copies):
            word = tuple((x >> j) & 1 for j in range(m))
            uu, vv = _fields(block.register.evaluate(word), d, r)
            for t in range(d):
                idx = offset+t*copies+x
                degrees[idx] = block.degrees[t]
                u[idx], vcols[idx] = uu[t], vv[t]
                a[idx] = sum(1 << (offset+s*copies+x) for s in gf2.bits(block.differential[t]))
        offset += d*copies
    v = gf2.transpose(vcols, r)
    return gf2.add(a, gf2.mul(u, v)), degrees


def coupled_pair(length: int, kind: str = 'singular') -> PortComplex:
    """Two-term demonstrations with 2^(length+1) virtual generators.

    singular: I + 1 e_{11..1}^T has nullity one; homology dimension two.
    invertible: I + 1 1^T is invertible when length>=1; homology zero.
    large_homology: base zero, update 1 1^T; homology 2^(length+1)-2.
    """
    if kind not in ('singular', 'invertible', 'large_homology'):
        raise ValueError('unknown example kind')
    # d=2, r=1: U target B is output bit 1; V source A is bit 2.
    if kind == 'singular':
        reg = product_register([[3]*length, [2]*length], [2, 4], 4, length=length)
    else:
        reg = product_register([[3]*length], [2|4], 4, length=length)
    a = (0, 0) if kind == 'large_homology' else (0, 1)
    return PortComplex((TemplateBlock(a, (0, 1), reg),), (0,))


def connected_singular_pair(length: int) -> PortComplex:
    """I + 1 (e_0 + e_1 + e_2)^T: connected support, rank 2^m-1.

    The Boolean words represent 0,1,2 in least-significant-bit-first order.
    The virtual support graph is connected for length >= 2. No knot-diagram
    provenance is asserted for this abstract chain complex.
    """
    if type(length) is not int or length < 2:
        raise ValueError('connected example requires length >= 2')
    terms = [[3]*length]
    for x in (0, 1, 2):
        terms.append([2 if x >> j & 1 else 1 for j in range(length)])
    reg = product_register(terms, [2, 4, 4, 4], 4, length=length)
    return PortComplex((TemplateBlock((0, 1), (0, 1), reg),), (0,))
