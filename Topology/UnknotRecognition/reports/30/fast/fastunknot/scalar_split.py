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


def find_scalar_split(scan, group, *, max_variables=1024, basis_trials=64,
                      combination_trials=16, check=None, preserve_grading=True):
    """Return transformed rows and a verifiable witness, or no split.

    The search is deterministic: the first basis_trials basis vectors, then a
    fixed-seed collection of binary linear combinations. Every returned split
    is exact, regardless of whether this bounded search finds all splits.
    """
    data = scalar_endomorphism_space(scan, group, max_variables=max_variables, check=check,
                                     preserve_grading=preserve_grading)
    metrics = dict(variables=0, equations=0, dimension=0, candidates=0, skipped_variables=0)
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
        if image_dimension in (0, len(group)):
            continue
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
        return out, witness, metrics
    return None, None, metrics


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
                 record_witnesses=False, preserve_grading=True, **kwargs):
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
        self.preserve_grading = preserve_grading
        self.record_witnesses = record_witnesses
        self.fitting_witnesses = []
        self.scalar_cache = {}
        self.stats.update(fitting_examined=0, fitting_splits=0, fitting_candidates=0,
                          fitting_skipped_size=0, fitting_skipped_variables=0,
                          fitting_skipped_split_budget=0, fitting_max_variables=0,
                          fitting_max_endomorphism_dimension=0, fitting_cache_hits=0,
                          fitting_cache_misses=0, fitting_skipped_scalar_only=0)

    def _compress(self, ancestry, groups=None):
        # Work with views of the current indices until an accepted split really
        # requires new arrays. Ineligible and oversized components are not copied.
        groups = list(components(self)) if groups is None else list(groups)
        pending = []
        for group in groups:
            parent = ancestry[group[0]]
            if any(ancestry[v] != parent for v in group):
                raise ArithmeticError('a differential joined independent parent summands')
            pending.append((self, group, parent))
        pending.reverse()
        finished = []
        splits = 0
        while pending:
            source, group, parent = pending.pop()
            self._check()
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
            if key in self.scalar_cache:
                self.stats['fitting_cache_hits'] += 1
                witness, saved_metrics = self.scalar_cache[key]
                metrics = dict(saved_metrics, candidates=0)
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
                out, witness, metrics = find_scalar_split(
                    source, group, max_variables=self.fitting_max_variables,
                    basis_trials=self.fitting_basis_trials,
                    combination_trials=self.fitting_combination_trials, check=self._check,
                    preserve_grading=self.preserve_grading)
                if self.fitting_cache_entries:
                    if len(self.scalar_cache) >= self.fitting_cache_entries:
                        self.scalar_cache.clear()
                    self.scalar_cache[key] = (None if witness is None else dict(witness), dict(metrics))
            self.stats['fitting_candidates'] += metrics['candidates']
            self.stats['fitting_skipped_variables'] += metrics['skipped_variables']
            self.stats['fitting_max_variables'] = max(self.stats['fitting_max_variables'], metrics['variables'])
            self.stats['fitting_max_endomorphism_dimension'] = max(
                self.stats['fitting_max_endomorphism_dimension'], metrics['dimension'])
            if out is None:
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
            for child in reversed(list(components(changed))):
                pending.append((changed, child, parent))
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
    if scan is None:
        return dict(rank=2, reduced_rank=1, by_degree={0: 2}, stats={}, order=[],
                    backend='scalar-fitting-interval-sharing', stages=[], witnesses=[])
    rank = scan.total_rank()
    if rank % 2:
        raise ArithmeticError('odd unreduced F2 rank for a knot')
    stats = dict(scan.stats)
    stats.update(scan.algebra.stats)
    return dict(rank=rank, reduced_rank=rank // 2, by_degree=scan.ranks_by_degree(),
                stats=stats, order=order, backend='scalar-fitting-interval-sharing',
                stages=scan.stage_history, witnesses=scan.fitting_witnesses,
                preserves_quantum_grading=scan.preserve_grading)


def fitting_khovanov_decide(pd, *, length_cap=2, **options):
    """Exact capped-rank decision for an already validated one-component knot.

    In the default decision model, whole common-nilpotent interval summands are
    shortened to length two after certified scalar splitting. Exact rank and
    homotopy type are not preserved by this optional length replacement.
    """
    scan, order = _run(pd, rank_cap=3, length_cap=length_cap, **options)
    if scan is None:
        return dict(status='UNKNOT', rank_capped=2, rank_cap=3, stats={}, order=[],
                    backend='scalar-fitting-interval-decision', length_cap=length_cap,
                    stages=[], witnesses=[])
    rank = scan.total_rank()
    if rank not in (2, 3):
        raise ArithmeticError('a validated knot has unreduced rank at least two')
    stats = dict(scan.stats)
    stats.update(scan.algebra.stats)
    return dict(status='UNKNOT' if rank == 2 else 'KNOTTED', rank_capped=rank, rank_cap=3,
                stats=stats, order=order, backend='scalar-fitting-interval-decision',
                length_cap=length_cap, stages=scan.stage_history,
                witnesses=scan.fitting_witnesses, preserves_quantum_grading=scan.preserve_grading)
