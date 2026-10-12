"""Transport complete scalar commutants through one verified static split.

If C is a direct sum of children, each child endomorphism extends by zero.
Consequently restrictions of S^-1 R S, for a complete parent basis R, span
the entire child commutant. This is valid only before any differential or
object mutation. FittingScan keeps these spaces within one _compress call.
Canonicalization preserves the fresh nullspace solver's candidate sequence.
"""
from .barcode_scan import _apply
from .scalar_split import _columns, _inverse, _scalar_blocks


def canonical_binary_span(vectors, *, check=lambda: None):
    """Reduced basis with increasing least-bit pivots, as in binary_nullspace."""
    pivots = {}
    for vector in vectors:
        check()
        while vector:
            pivot = (vector & -vector).bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = vector
                break
            vector ^= pivots[pivot]
    ordered = sorted(pivots, reverse=True)
    for offset, pivot in enumerate(ordered):
        check()
        for lower in ordered[offset + 1:]:
            if pivots[lower] >> pivot & 1:
                pivots[lower] ^= pivots[pivot]
    return [pivots[pivot] for pivot in reversed(ordered)]


def corner_endomorphism_space(parent_space, witness, scan, group, *,
                              check=lambda: None, preserve_grading=True):
    """Internal restriction of a trusted complete parent space to one child.

The positive split has already checked every transformed cross term. The
witness blocks name indices in the resulting view; parent_space blocks may
instead use its source's indices. Both have exactly the same block order.
No incomplete candidate list or cross-stage cached basis is accepted here.
"""
    check()
    parent_blocks, parent_variables, parent_basis, _ = parent_space
    blocks = _scalar_blocks(scan, group, check=check, preserve_grading=preserve_grading)
    variables = {(i, j): index for index, (i, j) in enumerate(
        (i, j) for block in blocks for i in block for j in block)}
    locations = {v: (block_index, index)
                 for block_index, block in enumerate(witness['blocks'])
                 for index, v in enumerate(block)}
    changes = witness['basis_columns']
    active = {}
    for block in blocks:
        indices = {locations[v][0] for v in block}
        if len(indices) != 1:
            raise ArithmeticError('child scalar types do not refine the parent types')
        parent_index = indices.pop()
        active.setdefault(parent_index, []).append(block)
    inverses = {index: _inverse(changes[index]) for index in active}
    vectors = []
    for vector in parent_basis:
        check()
        matrices = _columns(parent_blocks, parent_variables, vector)
        restricted = 0
        for index, child_blocks in active.items():
            check()
            for block in child_blocks:
                for source in block:
                    check()
                    old = _apply(matrices[index], changes[index][locations[source][1]])
                    column = _apply(inverses[index], old)
                    for target in block:
                        if column >> locations[target][1] & 1:
                            restricted |= 1 << variables[target, source]
        vectors.append(restricted)
    basis = canonical_binary_span(vectors, check=check)
    identity = sum(1 << variables[v, v] for v in group)
    if not basis or canonical_binary_span(basis + [identity], check=check) != basis:
        raise ArithmeticError('transported commutant lost the child identity')
    check()
    # No differential equations were constructed for this child.
    return blocks, variables, basis, 0
