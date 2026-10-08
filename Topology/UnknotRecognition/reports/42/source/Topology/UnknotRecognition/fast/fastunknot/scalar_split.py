"""Certified scalar Fitting decompositions of small scan components.

By default the searched endomorphisms mix only objects with identical matching,
homological degree, and recovered quantum shift, using F2 scalar coefficients.
An explicit preserve_grading=False option retains the archive's ungraded search.  They therefore act by
honest invertible changes of basis in the existing cobordism category.  The
commutation equations are solved separately for every morphism coefficient.

A bounded deterministic collection of endomorphisms is inspected.  When a
stable kernel and stable image are both nonzero, their bases split the entire
component, including all attachments.  The commutator and every transformed
cross-block entry are checked before acceptance.  Failure to find a split
retains the exact original component; completeness is not claimed.
"""
from __future__ import annotations

from random import Random
from time import monotonic

from .barcode_scan import BarcodeScan, _apply, _binary_basis
from .component_scan import components
from .ordering import best_scan_order, repeated_stages, validate_order
from .window_scan import validate_seconds
from .geometry import ScanLimit
from .recovered_grading import recover_shifts


_UNCOMPUTED = object()


def binary_nullspace(equations, variables, check=None):
    """A basis of solutions of homogeneous binary equations, packed by row."""
    pivots = {}
    for index, row in enumerate(equations):
        if check is not None and not index & 255:
            check()
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    basis = []
    ordered = sorted(pivots)
    for free in range(variables):
        if free in pivots:
            continue
        vector = 1 << free
        for pivot in ordered:
            if (pivots[pivot] & vector).bit_count() & 1:
                vector ^= 1 << pivot
        basis.append(vector)
    return basis


def _canonical_binary_span(vectors, check=None):
    """The unique reduced binary basis with least-significant-bit pivots.

    This is exactly the basis order used by ``binary_nullspace``.  Reducing
    inherited generators to this form preserves the bounded splitter's
    deterministic candidate sequence, not just its search space.
    """
    pivots = {}
    for index, vector in enumerate(vectors):
        if check is not None and not index & 255:
            check()
        while vector:
            low = vector & -vector
            if low not in pivots:
                pivots[low] = vector
                break
            vector ^= pivots[low]
    ordered = sorted(pivots)
    for index in range(len(ordered) - 1, -1, -1):
        if check is not None and not index & 255:
            check()
        pivot = ordered[index]
        value = pivots[pivot]
        for other in ordered[:index]:
            if pivots[other] & pivot:
                pivots[other] ^= value
    return [pivots[pivot] for pivot in ordered]


def _inverse(columns):
    """Inverse of a square binary matrix, represented by columns."""
    pivots = {}
    for index, column in enumerate(columns):
        coefficient = 1 << index
        while column:
            pivot = column.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = column, coefficient
                break
            value, change = pivots[pivot]
            column ^= value
            coefficient ^= change
        else:
            raise ArithmeticError("the Fitting basis is singular")
    inverse = []
    for index in range(len(columns)):
        vector, coefficient = 1 << index, 0
        while vector:
            pivot = vector.bit_length() - 1
            value, change = pivots[pivot]
            vector ^= value
            coefficient ^= change
        inverse.append(coefficient)
    if any(_apply(inverse, column) != 1 << i for i, column in enumerate(columns)):
        raise ArithmeticError("the computed Fitting inverse failed verification")
    return inverse


def _inherited_endomorphism_spaces(data, group, changes, children, check=None,
                                  *, method='auto'):
    """Transport a complete commutant basis and return its child corners.

    ``children`` uses local indices in the changed version of ``group``; each
    child must be a whole differential-graph component.  Colors are inherited
    from the parent blocks.  If A is the parent's full scalar commutant and S
    is the accepted change of basis, the result for child i is precisely
    e_i (S^-1 A S) e_i = End(child_i), by extension by zero.  No new commutation
    equations or quantum-shift recovery are needed.  Corner compression is
    linear; it need not be an algebra homomorphism on A.

    For large algebras, a packed linear map acts on every parent basis vector;
    its columns are restricted conjugates of matrix units, built as outer
    products.  For small algebras, directly conjugating their few matrices
    avoids constructing that larger map.  Both methods return the same basis.
    Returned bases agree exactly with a fresh ``scalar_endomorphism_space``
    solve, including its basis ordering.  The equation-count field is zero.
    """
    if method not in ('auto', 'direct', 'matrix_units'):
        raise ValueError('unknown corner transport method')
    blocks, variables, basis, _ = data
    local = {v: index for index, v in enumerate(group)}
    local_blocks = [[local[v] for v in block] for block in blocks]
    location = {v: (index, position)
                for index, block in enumerate(local_blocks)
                for position, v in enumerate(block)}
    plans = []
    pieces = [[] for _ in blocks]
    total_variables = 0
    for child in children:
        partitions = {}
        for v in child:
            partitions.setdefault(location[v][0], []).append(v)
        child_blocks = list(partitions.values())
        child_variables = {(i, j): index for index, (i, j) in enumerate(
            (i, j) for block in child_blocks for i in block for j in block)}
        offset = 0
        for block_index, child_block in partitions.items():
            positions = [location[v][1] for v in child_block]
            pieces[block_index].append((positions, total_variables + offset))
            offset += len(positions) ** 2
        plans.append((child_blocks, child_variables, total_variables))
        total_variables += len(child_variables)
    if not plans:
        return []
    if method == 'auto':
        method = 'direct' if len(basis) <= max(map(len, blocks)) else 'matrix_units'
    if method == 'direct':
        inverses = [_inverse(change) for change in changes]
        images = []
        for vector in basis:
            if check is not None:
                check()
            packed = 0
            matrices = _columns(blocks, variables, vector)
            for block_index, (matrix, change, inverse) in enumerate(
                    zip(matrices, changes, inverses)):
                conjugate = [_apply(inverse, _apply(matrix, column)) for column in change]
                for positions, offset in pieces[block_index]:
                    width = len(positions)
                    for source, position in enumerate(positions):
                        column = conjugate[position]
                        for target, old_target in enumerate(positions):
                            if column >> old_target & 1:
                                packed ^= 1 << (offset + target * width + source)
            images.append(packed)
        return [(child_blocks, child_variables,
                 _canonical_binary_span(((v >> offset) & ((1 << len(child_variables)) - 1)
                                         for v in images), check), 0)
                for child_blocks, child_variables, offset in plans]
    transport = [0] * len(variables)
    used = 0
    for vector in basis:
        used |= vector
    for block_index, (block, change) in enumerate(zip(blocks, changes)):
        if check is not None:
            check()
        inverse = _inverse(change)
        rows = [sum(((column >> row) & 1) << col
                    for col, column in enumerate(change)) for row in range(len(block))]
        for positions, offset in pieces[block_index]:
            width = len(positions)
            left = [sum(((column >> position) & 1) << row
                        for row, position in enumerate(positions)) for column in inverse]
            right = [sum(((row >> position) & 1) << col
                         for col, position in enumerate(positions)) for row in rows]
            for i, target in enumerate(block):
                if check is not None:
                    check()
                for j, source in enumerate(block):
                    index = variables[target, source]
                    if not (used >> index) & 1 or not right[j]:
                        continue
                    column = left[i]
                    while column:
                        low = column & -column
                        transport[index] ^= right[j] << (offset + (low.bit_length() - 1) * width)
                        column ^= low
    images = []
    for index, vector in enumerate(basis):
        if check is not None and not index & 255:
            check()
        images.append(_apply(transport, vector))
    result = []
    for child_blocks, child_variables, offset in plans:
        mask = (1 << len(child_variables)) - 1
        child_basis = _canonical_binary_span(((v >> offset) & mask for v in images), check)
        result.append((child_blocks, child_variables, child_basis, 0))
    return result


def scalar_endomorphism_space(scan, group, *, max_variables=1024, check=None,
                              preserve_grading=True):
    """Return blocks, variable indices, nullspace, and equation count; or None.

    A matrix variable Q_(i,j) exists exactly when i,j have the same degree and
    matching, and (by default) recovered quantum shift. A return value None denotes a configured size skip, not a proof
    that no endomorphism or decomposition exists.
    """
    shifts = recover_shifts(scan, group, check=check or (lambda: None)) if preserve_grading else {}
    partitions = {}
    for v in group:
        partitions.setdefault((scan.deg[v], scan.mid[v], shifts.get(v)), []).append(v)
    blocks = list(partitions.values())
    variable_count = sum(len(block) ** 2 for block in blocks)
    if max_variables is not None and variable_count > max_variables:
        return None
    if not blocks or max(map(len, blocks)) == 1:
        variables = {(v, v): index for index, v in enumerate(group)}
        return blocks, variables, [(1 << len(group)) - 1], 0
                                              # a connected graph has only scalar diagonals
    variables = {(i, j): index for index, (i, j) in enumerate(
        (i, j) for block in blocks for i in block for j in block)}
    containing = {v: block for block in blocks for v in block}
    equations = {}
    for a in group:
        if check is not None:
            check()
        for b, value in scan.out[a].items():
            while value:
                bit = value & -value
                value ^= bit
                for target in containing[b]:
                    key = a, target, bit
                    equations[key] = equations.get(key, 0) ^ (1 << variables[target, b])
                for source in containing[a]:
                    key = source, b, bit
                    equations[key] = equations.get(key, 0) ^ (1 << variables[a, source])
    nonzero = [row for row in equations.values() if row]
    basis = binary_nullspace(nonzero, variable_count, check)
    return blocks, variables, basis, len(nonzero)


def _columns(blocks, variables, vector):
    return [[sum(((vector >> variables[i, j]) & 1) << row
                 for row, i in enumerate(block)) for j in block] for block in blocks]


def _commutes(scan, group, blocks, columns):
    """Independent coefficientwise verification of Q d = d Q."""
    actions = {}
    for block, matrix in zip(blocks, columns):
        for source, column in zip(block, matrix):
            actions[source] = [target for index, target in enumerate(block) if column >> index & 1]
    for source in group:
        left, right = {}, {}
        for old_target, value in scan.out[source].items():
            for target in actions[old_target]:
                left[target] = left.get(target, 0) ^ value
        for old_source in actions[source]:
            for target, value in scan.out[old_source].items():
                right[target] = right.get(target, 0) ^ value
        if {v: f for v, f in left.items() if f} != {v: f for v, f in right.items() if f}:
            return False
    return True


def _fitting_bases(blocks, columns):
    exponent = 1
    while exponent < max(map(len, blocks)):
        exponent *= 2
    changes, kernel_dimensions, image_dimension = [], [], 0
    for block, matrix in zip(blocks, columns):
        power = list(matrix)
        step = 1
        while step < exponent:
            power = [_apply(power, column) for column in power]
            step *= 2
        rows = [sum(((column >> row) & 1) << col for col, column in enumerate(power))
                for row in range(len(block))]
        kernel = binary_nullspace(rows, len(block))
        image = _binary_basis(power)
        if len(kernel) + len(image) != len(block):
            raise ArithmeticError("the selected power has not stabilized")
        change = kernel + image
        _inverse(change)                       # independently checks a direct-sum basis
        changes.append(change)
        kernel_dimensions.append(len(kernel))
        image_dimension += len(image)
    return changes, kernel_dimensions, image_dimension, exponent


def _change_basis(scan, group, blocks, changes, kernel_dimensions):
    """Transform every morphism, and require zero maps across the split."""
    location = {v: (block_index, index) for block_index, block in enumerate(blocks)
                for index, v in enumerate(block)}
    local = {v: i for i, v in enumerate(group)}
    inverses = [_inverse(change) for change in changes]
    out = [{} for _ in group]
    side = [0] * len(group)
    for block_index, block in enumerate(blocks):
        for new_index, source in enumerate(block):
            side[local[source]] = int(new_index >= kernel_dimensions[block_index])
            original_image = {}
            coefficients = changes[block_index][new_index]
            for old_index, old_source in enumerate(block):
                if not coefficients >> old_index & 1:
                    continue
                for old_target, value in scan.out[old_source].items():
                    original_image[old_target] = original_image.get(old_target, 0) ^ value
            row = out[local[source]]
            for old_target, value in original_image.items():
                if not value:
                    continue
                target_block, old_index = location[old_target]
                coefficients = inverses[target_block][old_index]
                for new_target_index, target in enumerate(blocks[target_block]):
                    if coefficients >> new_target_index & 1:
                        target = local[target]
                        row[target] = row.get(target, 0) ^ value
            out[local[source]] = {v: f for v, f in row.items() if f}
    for source, row in enumerate(out):
        for target in row:
            if side[source] != side[target]:
                raise ArithmeticError("nonzero morphism across the proposed Fitting split")
    return out, side


def _monogenic_child_spaces(witness, children, check=None):
    """Inherit saturated polynomial algebras by transporting one generator.

    The caller has certified End(parent)=F2[Q] using minimal-degree equality.
    Every component selector belongs to this commutative algebra.  Hence its
    corner is generated by the restricted Q, including its corner identity.
    A primary restricted minimal polynomial certifies a scalar local leaf;
    otherwise the powers give the complete child commutant basis.
    """
    from .primary_split import primary_projector
    local_blocks = witness['blocks']
    columns = witness['primary']['candidate_columns']
    conjugates = []
    for matrix, change in zip(columns, witness['basis_columns']):
        if check is not None:
            check()
        inverse = _inverse(change)
        conjugates.append([_apply(inverse, _apply(matrix, column)) for column in change])
    location = {v: (index, position)
                for index, block in enumerate(local_blocks)
                for position, v in enumerate(block)}
    result = []
    for child in children:
        partitions = {}
        for v in child:
            partitions.setdefault(location[v][0], []).append(v)
        blocks, restricted = list(partitions.values()), []
        for block_index, block in partitions.items():
            positions = [location[v][1] for v in block]
            matrix = conjugates[block_index]
            restricted.append([sum(((matrix[source] >> target) & 1) << row
                                   for row, target in enumerate(positions)) for source in positions])
        _, evidence = primary_projector(restricted, check=check)
        dimension = evidence['minimal_degree']
        if evidence['berlekamp_dimension'] == 1:
            local = {v: index for index, v in enumerate(child)}
            certificate = dict(blocks=[[local[v] for v in block] for block in blocks],
                generator_columns=restricted, commutant_dimension=dimension, **evidence)
            result.append((None, certificate))
            continue
        variables = {(i, j): index for index, (i, j) in enumerate(
            (i, j) for block in blocks for i in block for j in block)}
        powers = []
        current = [[1 << col for col in range(len(block))] for block in blocks]
        for _ in range(dimension):
            if check is not None:
                check()
            packed = 0
            for block, matrix in zip(blocks, current):
                for col, source in enumerate(block):
                    for row, target in enumerate(block):
                        if matrix[col] >> row & 1:
                            packed ^= 1 << variables[target, source]
            powers.append(packed)
            current = [[_apply(matrix, column) for column in power]
                       for matrix, power in zip(restricted, current)]
        basis = _canonical_binary_span(powers, check)
        if len(basis) != dimension:
            raise ArithmeticError('saturated child powers are linearly dependent')
        result.append(((blocks, variables, basis, 0), None))
    return result


def find_scalar_split(scan, group, *, max_variables=1024, basis_trials=64,
                      combination_trials=16, check=None, preserve_grading=True,
                      primary=False, certify_local=False, endomorphism_data=_UNCOMPUTED):
    """Return transformed rows and a verifiable witness, or no split.

    The search is deterministic: the first basis_trials basis vectors, then a
    fixed-seed collection of binary linear combinations. Every returned split
    is exact, regardless of whether this bounded search finds all splits.

    ``endomorphism_data`` is an internal complete commutant basis in the same
    format as ``scalar_endomorphism_space``.  Recursive corner inheritance
    supplies it to avoid reconstructing the child's commutation equations.
    The optional ``primary`` search is inherited from the earlier projectors
    research package; it is off by default and uses polynomial idempotents.
    With ``certify_local``, a negative primary test is conclusive when its
    polynomial algebra already has the full commutant dimension.  This proves
    absence of scalar direct summands, not absence of general cobordism-valued
    projectors.  The evidence is returned in ``metrics['local_certificate']``.
    """
    if type(primary) is not bool:
        raise ValueError('primary must be a boolean')
    if type(certify_local) is not bool:
        raise ValueError('certify_local must be a boolean')
    data = endomorphism_data
    if data is _UNCOMPUTED:
        data = scalar_endomorphism_space(scan, group, max_variables=max_variables, check=check,
                                        preserve_grading=preserve_grading)
    metrics = dict(variables=0, equations=0, dimension=0, candidates=0, skipped_variables=0,
                   primary_candidates=0, primary_splits=0, primary_max_minimal_degree=0,
                   local_certificates=0, local_certificate=None)
    if data is None:
        metrics['skipped_variables'] = 1
        return None, None, metrics
    blocks, variables, basis, equations = data
    metrics.update(variables=len(variables), equations=equations, dimension=len(basis))
    if len(basis) <= 1 or not variables:
        return None, None, metrics
    candidates = list(basis[:basis_trials])
    rng = Random(7243)
    for _ in range(combination_trials):
        vector = 0
        for item in basis:
            if rng.randrange(2):
                vector ^= item
        candidates.append(vector)
    seen = set()
    for vector in candidates:
        if not vector or vector in seen:
            continue
        seen.add(vector)
        if check is not None:
            check()
        metrics['candidates'] += 1
        columns = _columns(blocks, variables, vector)
        changes, kernels, image_dimension, exponent = _fitting_bases(blocks, columns)
        primary_witness = None
        if image_dimension in (0, len(group)):
            if (not primary or image_dimension == 0
                    or all(matrix == [1 << i for i in range(len(matrix))] for matrix in columns)):
                continue
            from .primary_split import primary_projector
            original_columns = columns
            metrics['primary_candidates'] += 1
            columns, primary_witness = primary_projector(columns, check=check)
            metrics['primary_max_minimal_degree'] = max(
                metrics['primary_max_minimal_degree'], primary_witness['minimal_degree'])
            if columns is None:
                if certify_local and primary_witness['minimal_degree'] == len(basis):
                    if primary_witness['berlekamp_dimension'] != 1:
                        raise ArithmeticError('a negative primary test has multiple idempotents')
                    if not _commutes(scan, group, blocks, original_columns):
                        raise ArithmeticError('the proposed local generator does not commute with d')
                    local = {v: i for i, v in enumerate(group)}
                    metrics['local_certificates'] = 1
                    metrics['local_certificate'] = dict(
                        blocks=[[local[v] for v in block] for block in blocks],
                        generator_columns=original_columns,
                        commutant_dimension=len(basis), **primary_witness)
                    return None, None, metrics
                continue
            changes, kernels, image_dimension, exponent = _fitting_bases(blocks, columns)
            if image_dimension in (0, len(group)):
                raise ArithmeticError('a nontrivial primary projector failed to split')
            primary_witness['candidate_columns'] = original_columns
            metrics['primary_splits'] += 1
        if not _commutes(scan, group, blocks, columns):
            raise ArithmeticError("the computed scalar endomorphism does not commute with d")
        out, sides = _change_basis(scan, group, blocks, changes, kernels)
        local = {v: i for i, v in enumerate(group)}
        witness = dict(
            blocks=[[local[v] for v in block] for block in blocks],
            endomorphism_columns=columns, basis_columns=changes,
            kernel_dimensions=kernels, stable_exponent=exponent,
            image_dimension=image_dimension, sides=sides,
        )
        if primary_witness is not None:
            witness['primary'] = primary_witness
        return out, witness, metrics
    return None, None, metrics


def verify_scalar_local_certificate(scan, group, evidence, *, preserve_grading=True,
                                    check=None):
    """Independently recompute the space and check a conclusive scalar no-split.

    Verification deliberately solves the commutation equations again; the
    production shortcut uses the already computed or inherited complete space.
    Equality of the minimal degree and commutant dimension establishes that
    the displayed generator spans the whole algebra by its powers.
    """
    from .primary_split import minimal_polynomial, berlekamp_basis
    data = scalar_endomorphism_space(scan, group, max_variables=None, check=check,
                                     preserve_grading=preserve_grading)
    blocks, _, basis, _ = data
    local = {v: i for i, v in enumerate(group)}
    if evidence['blocks'] != [[local[v] for v in block] for block in blocks]:
        raise ArithmeticError('local certificate has incorrect scalar blocks')
    columns = evidence['generator_columns']
    if (len(columns) != len(blocks)
            or any(len(matrix) != len(block) for matrix, block in zip(columns, blocks))):
        raise ArithmeticError('local certificate has incorrect matrix sizes')
    if not _commutes(scan, group, blocks, columns):
        raise ArithmeticError('local certificate generator does not commute with d')
    modulus = minimal_polynomial(columns, check=check)
    dimension = len(basis)
    if (evidence['commutant_dimension'] != dimension
            or evidence['minimal_polynomial'] != modulus
            or evidence['minimal_degree'] != dimension
            or modulus.bit_length() - 1 != dimension):
        raise ArithmeticError('local certificate does not generate the full commutant')
    if evidence['berlekamp_dimension'] != 1 or len(berlekamp_basis(modulus, check=check)) != 1:
        raise ArithmeticError('local certificate algebra has a nontrivial idempotent')
    return True


class _View:
    def __init__(self, scan, group, out=None):
        local = {v: i for i, v in enumerate(group)}
        self.mid = [scan.mid[v] for v in group]
        self.deg = [scan.deg[v] for v in group]
        self.out = out if out is not None else [
            {local[w]: value for w, value in scan.out[v].items()} for v in group]
        self.inc = [set() for _ in group]
        for v, row in enumerate(self.out):
            for w in row:
                self.inc[w].add(v)
        self.algebra = scan.algebra
        self.points = scan.points


def _scalar_key(scan, group, preserve_grading=True):
    """Complete scalar-quiver data, ignoring actual matching names and a shift."""
    shifts = recover_shifts(scan, group) if preserve_grading else {}
    names = {}
    first = min(scan.deg[v] for v in group)
    local = {v: i for i, v in enumerate(group)}
    return tuple((names.setdefault(scan.mid[v], len(names)), scan.deg[v] - first, shifts.get(v),
                  tuple(sorted((local[w], value) for w, value in scan.out[v].items())))
                 for v in group)


class FittingScan(BarcodeScan):
    """Optional bounded scalar splitting, then interval and literal sharing."""

    def __init__(self, *args, fitting_max_objects=48, fitting_max_variables=1024,
                 fitting_max_splits=16, fitting_basis_trials=64,
                 fitting_combination_trials=16, fitting_cache_entries=4096,
                 record_witnesses=False, preserve_grading=True,
                 fitting_reuse_endomorphisms=True, fitting_primary=False,
                 fitting_certify_local=False, fitting_monogenic_corners=False, **kwargs):
        super().__init__(*args, **kwargs)
        for name, value in [('fitting_max_objects', fitting_max_objects),
                            ('fitting_max_variables', fitting_max_variables),
                            ('fitting_max_splits', fitting_max_splits),
                            ('fitting_basis_trials', fitting_basis_trials),
                            ('fitting_combination_trials', fitting_combination_trials),
                            ('fitting_cache_entries', fitting_cache_entries)]:
            if type(value) is not int or value < 0:
                raise ValueError(name + ' must be a nonnegative integer')
            setattr(self, name, value)
        if type(preserve_grading) is not bool:
            raise ValueError("preserve_grading must be a boolean")
        if type(fitting_reuse_endomorphisms) is not bool:
            raise ValueError("fitting_reuse_endomorphisms must be a boolean")
        if type(fitting_primary) is not bool:
            raise ValueError('fitting_primary must be a boolean')
        if type(fitting_certify_local) is not bool:
            raise ValueError('fitting_certify_local must be a boolean')
        if type(fitting_monogenic_corners) is not bool:
            raise ValueError('fitting_monogenic_corners must be a boolean')
        self.preserve_grading = preserve_grading
        self.fitting_reuse_endomorphisms = fitting_reuse_endomorphisms
        self.fitting_primary = fitting_primary
        self.fitting_certify_local = fitting_certify_local
        self.fitting_monogenic_corners = fitting_monogenic_corners
        self.record_witnesses = record_witnesses
        self.fitting_witnesses = []
        self.fitting_local_certificates = []
        self.scalar_cache = {}
        self.stats.update(fitting_examined=0, fitting_splits=0, fitting_candidates=0,
                          fitting_skipped_size=0, fitting_skipped_variables=0,
                          fitting_skipped_split_budget=0, fitting_max_variables=0,
                          fitting_max_endomorphism_dimension=0, fitting_cache_hits=0,
                          fitting_cache_misses=0, fitting_skipped_scalar_only=0,
                          fitting_endomorphism_computations=0, fitting_equations_built=0,
                          fitting_inherited_spaces_built=0, fitting_inherited_spaces_used=0,
                          fitting_inheritance_maps=0, fitting_inheritance_variables=0,
                          fitting_inheritance_generators=0, fitting_primary_candidates=0,
                          fitting_primary_splits=0, fitting_primary_max_minimal_degree=0,
                          fitting_local_certificates=0, fitting_monogenic_corners=0)

    def _record_local_certificate(self, source, group, evidence):
        if not self.record_witnesses:
            return
        certificate = dict(evidence)
        local = {v: i for i, v in enumerate(group)}
        certificate.update(stage=len(self.stage_history) + 1,
            rows=[{local[w]: value for w, value in source.out[v].items()} for v in group],
            degrees=[source.deg[v] for v in group],
            matchings=[source.algebra.pairs[source.mid[v]] for v in group],
            frontier_points=sorted(source.points),
            preserves_quantum_grading=self.preserve_grading)
        self.fitting_local_certificates.append(certificate)

    def _compress(self, ancestry, groups=None):
        # Work with views of the current indices until an accepted split really
        # requires new arrays. Ineligible and oversized components are not copied.
        groups = list(components(self)) if groups is None else list(groups)
        pending = []
        for group in groups:
            parent = ancestry[group[0]]
            if any(ancestry[v] != parent for v in group):
                raise ArithmeticError('a differential joined independent parent summands')
            pending.append((self, group, parent, None, None))
        pending.reverse()
        finished = []
        splits = 0
        while pending:
            source, group, parent, endomorphisms, local_certificate = pending.pop()
            self._check()
            if local_certificate is not None:
                self.stats['fitting_local_certificates'] += 1
                self._record_local_certificate(source, group, local_certificate)
                finished.append((source, group, parent))
                continue
            size = len(group)
            if len({(source.deg[v], source.mid[v]) for v in group}) == size:
                self.stats['fitting_skipped_scalar_only'] += 1
                finished.append((source, group, parent))
                continue
            if size > self.fitting_max_objects:
                self.stats['fitting_skipped_size'] += 1
                finished.append((source, group, parent))
                continue
            if splits >= self.fitting_max_splits:
                self.stats['fitting_skipped_split_budget'] += 1
                finished.append((source, group, parent))
                continue
            self.stats['fitting_examined'] += 1
            key = _scalar_key(source, group, self.preserve_grading)
            if self.fitting_primary:
                key = 'primary', self.fitting_certify_local, key
            if key in self.scalar_cache:
                self.stats['fitting_cache_hits'] += 1
                witness, saved_metrics = self.scalar_cache[key]
                metrics = dict(saved_metrics, candidates=0, primary_candidates=0)
                if witness is None:
                    out = None
                else:
                    witness = dict(witness)
                    blocks = [[group[i] for i in block] for block in witness['blocks']]
                    if not _commutes(source, group, blocks, witness['endomorphism_columns']):
                        raise ArithmeticError('cached scalar endomorphism failed verification')
                    out, _ = _change_basis(source, group, blocks, witness['basis_columns'],
                                           witness['kernel_dimensions'])
            else:
                self.stats['fitting_cache_misses'] += 1
                if endomorphisms is None:
                    endomorphisms = scalar_endomorphism_space(
                        source, group, max_variables=self.fitting_max_variables,
                        check=self._check, preserve_grading=self.preserve_grading)
                    self.stats['fitting_endomorphism_computations'] += 1
                    if endomorphisms is not None:
                        self.stats['fitting_equations_built'] += endomorphisms[3]
                else:
                    self.stats['fitting_inherited_spaces_used'] += 1
                out, witness, metrics = find_scalar_split(
                    source, group, max_variables=self.fitting_max_variables,
                    basis_trials=self.fitting_basis_trials,
                    combination_trials=self.fitting_combination_trials, check=self._check,
                    preserve_grading=self.preserve_grading, primary=self.fitting_primary,
                    certify_local=self.fitting_certify_local, endomorphism_data=endomorphisms)
                if self.fitting_cache_entries:
                    if len(self.scalar_cache) >= self.fitting_cache_entries:
                        self.scalar_cache.clear()
                    self.scalar_cache[key] = (None if witness is None else dict(witness), dict(metrics))
            self.stats['fitting_candidates'] += metrics['candidates']
            self.stats['fitting_primary_candidates'] += metrics.get('primary_candidates', 0)
            self.stats['fitting_primary_splits'] += metrics.get('primary_splits', 0)
            self.stats['fitting_local_certificates'] += metrics.get('local_certificates', 0)
            self.stats['fitting_primary_max_minimal_degree'] = max(
                self.stats['fitting_primary_max_minimal_degree'],
                metrics.get('primary_max_minimal_degree', 0))
            self.stats['fitting_skipped_variables'] += metrics['skipped_variables']
            self.stats['fitting_max_variables'] = max(self.stats['fitting_max_variables'], metrics['variables'])
            self.stats['fitting_max_endomorphism_dimension'] = max(
                self.stats['fitting_max_endomorphism_dimension'], metrics['dimension'])
            if out is None:
                if self.record_witnesses and metrics.get('local_certificate') is not None:
                    self._record_local_certificate(source, group, metrics['local_certificate'])
                finished.append((source, group, parent))
                continue
            splits += 1
            self.stats['fitting_splits'] += 1
            if self.record_witnesses:
                local = {v: i for i, v in enumerate(group)}
                shifts = recover_shifts(source, group) if self.preserve_grading else {}
                witness.update(quantum_shifts=[shifts.get(v) for v in group],
                    preserves_quantum_grading=self.preserve_grading, stage=len(self.stage_history) + 1,
                    matchings=[source.algebra.pairs[source.mid[v]] for v in group],
                    degrees=[source.deg[v] for v in group],
                    rows=[{local[w]: value for w, value in source.out[v].items()} for v in group],
                    transformed_rows=[dict(row) for row in out])
                self.fitting_witnesses.append(witness)
            changed = _View(source, group, out=out)
            children = list(components(changed))
            inherited = {}
            local_corners = {}
            saturated = (self.fitting_monogenic_corners and 'primary' in witness
                         and witness['primary']['minimal_degree'] == metrics['dimension'])
            if ((self.fitting_reuse_endomorphisms and endomorphisms is not None) or saturated
                    ) and splits < self.fitting_max_splits:
                selected = [index for index, child in enumerate(children)
                            if len(child) <= self.fitting_max_objects
                            and len({(changed.deg[v], changed.mid[v]) for v in child})
                            < len(child)]
                if selected:
                    selected_children = [children[index] for index in selected]
                    if saturated:
                        blocks = [[group[v] for v in block] for block in witness['blocks']]
                        if not _commutes(source, group, blocks,
                                         witness['primary']['candidate_columns']):
                            raise ArithmeticError('the saturated generator does not commute with d')
                        corners = _monogenic_child_spaces(witness, selected_children, self._check)
                        for index, (space, certificate) in zip(selected, corners):
                            if space is not None:
                                inherited[index] = space
                            else:
                                local_corners[index] = certificate
                        self.stats['fitting_monogenic_corners'] += len(corners)
                        self.stats['fitting_inherited_spaces_built'] += len(inherited)
                    else:
                        spaces = _inherited_endomorphism_spaces(
                            endomorphisms, group, witness['basis_columns'], selected_children,
                            self._check)
                        inherited = dict(zip(selected, spaces))
                        self.stats['fitting_inherited_spaces_built'] += len(spaces)
                        self.stats['fitting_inheritance_maps'] += 1
                        self.stats['fitting_inheritance_variables'] += len(endomorphisms[1])
                        self.stats['fitting_inheritance_generators'] += len(endomorphisms[2])
            for index in range(len(children) - 1, -1, -1):
                pending.append((changed, children[index], parent, inherited.get(index),
                                local_corners.get(index)))
        if not splits:
            super()._compress(ancestry, groups=groups)
            return

        mid, degree, out, origin = [], [], [], []
        rebuilt_groups = []
        for source, group, parent in finished:
            offset = len(mid)
            local = {v: offset + i for i, v in enumerate(group)}
            for v in group:
                mid.append(source.mid[v])
                degree.append(source.deg[v])
                out.append({local[w]: value for w, value in source.out[v].items()})
            origin.extend([parent] * len(group))
            rebuilt_groups.append(list(range(offset, len(mid))))
        if len(mid) != self.live:
            raise ArithmeticError('Fitting splitting changed the object count')
        inc = [set() for _ in mid]
        for v, row in enumerate(out):
            for w in row:
                inc[w].add(v)
        self.mid, self.deg, self.out, self.inc = mid, degree, out, inc
        super()._compress(origin, groups=rebuilt_groups)


def _run(pd, *, order=None, max_objects=None, seconds=None, check_d_squared=False,
         shape_cache=None, rank_cap=None, length_cap=None, **fitting_options):
    validate_seconds(seconds)
    deadline = None if seconds is None else monotonic() + seconds
    def check():
        if deadline is not None and monotonic() >= deadline:
            raise ScanLimit("time budget exhausted")
    if max_objects is not None and (type(max_objects) is not int or max_objects < 0):
        raise ValueError("max_objects must be nonnegative or None")
    pd = [tuple(crossing) for crossing in pd]
    if order is not None:
        order = validate_order(len(pd), order)
    if not pd:
        scan = FittingScan(max_objects=max_objects, deadline=deadline, shape_cache=shape_cache,
                           rank_cap=rank_cap, length_cap=length_cap, **fitting_options)
        return None, []
    check()
    if order is None:
        order = best_scan_order(pd, tries=min(len(pd), 12), check=check)
    if shape_cache is None:
        shape_cache = len(order) >= 16 and 8 * repeated_stages(pd, order) >= len(order)
    scan = FittingScan(max_objects=max_objects, deadline=deadline, shape_cache=shape_cache,
                       rank_cap=rank_cap, length_cap=length_cap, **fitting_options)
    for index in order:
        scan.add_crossing(pd[index])
        if check_d_squared:
            scan.check_d_squared()
    return scan, order


def fitting_khovanov_rank(pd, **options):
    """Exact rank and raw homological grading, with optional scalar splitting."""
    if options.get('rank_cap') is not None or options.get('length_cap') is not None:
        raise ValueError('the exact-rank entry point does not accept decision caps')
    scan, order = _run(pd, **options)
    primary = options.get('fitting_primary', False)
    backend = 'scalar-primary-interval-sharing' if primary else 'scalar-fitting-interval-sharing'
    if scan is None:
        return dict(rank=2, reduced_rank=1, by_degree={0: 2}, stats={}, order=[],
                    backend=backend, stages=[], witnesses=[], primary_decomposition=primary,
                    local_certificates=[])
    rank = scan.total_rank()
    if rank % 2:
        raise ArithmeticError('odd unreduced F2 rank for a knot')
    stats = dict(scan.stats)
    stats.update(scan.algebra.stats)
    return dict(rank=rank, reduced_rank=rank // 2, by_degree=scan.ranks_by_degree(),
                stats=stats, order=order, backend=backend,
                stages=scan.stage_history, witnesses=scan.fitting_witnesses,
                local_certificates=scan.fitting_local_certificates,
                preserves_quantum_grading=scan.preserve_grading,
                primary_decomposition=scan.fitting_primary)


def fitting_khovanov_decide(pd, *, length_cap=2, **options):
    """Exact capped-rank decision for an already validated one-component knot.

    In the default decision model, whole common-nilpotent interval summands are
    shortened to length two after certified scalar splitting. Exact rank and
    homotopy type are not preserved by this optional length replacement.
    """
    scan, order = _run(pd, rank_cap=3, length_cap=length_cap, **options)
    primary = options.get('fitting_primary', False)
    backend = 'scalar-primary-interval-decision' if primary else 'scalar-fitting-interval-decision'
    if scan is None:
        return dict(status='UNKNOT', rank_capped=2, rank_cap=3, stats={}, order=[],
                    backend=backend, length_cap=length_cap,
                    stages=[], witnesses=[], primary_decomposition=primary, local_certificates=[])
    rank = scan.total_rank()
    if rank not in (2, 3):
        raise ArithmeticError('a validated knot has unreduced rank at least two')
    stats = dict(scan.stats)
    stats.update(scan.algebra.stats)
    return dict(status='UNKNOT' if rank == 2 else 'KNOTTED', rank_capped=rank, rank_cap=3,
                stats=stats, order=order, backend=backend,
                length_cap=length_cap, stages=scan.stage_history,
                witnesses=scan.fitting_witnesses, preserves_quantum_grading=scan.preserve_grading,
                local_certificates=scan.fitting_local_certificates,
                primary_decomposition=scan.fitting_primary)
