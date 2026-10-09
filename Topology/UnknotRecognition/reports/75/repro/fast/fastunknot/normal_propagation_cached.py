"""Exact, certificate-preserving screening for positive-Euler propagation.

This opt-in producer has the same node LPs, scan order, branch order, and
certificate schema as ``normal_propagation.search_positive_euler``.  It omits
only coordinate-deletion LPs already answered positively by an independently
checked exact witness.  No negative conclusion is obtained from the cache.

If both runs have enough resources to follow their common logical trace, their
certificates are equal, including all dual vectors and final coordinates.
With a finite pivot allowance the screened run may go farther.  Neither exact
Bland simplex nor the number of branch nodes has a polynomial bound here.

The search body is an additive fork of the pinned producer; no global default
or existing module is changed.  See lp_cache_research for paired audits.
"""

from itertools import product
from math import prod

from .exact_lp import solve_nonnegative_kernel
from .normal_propagation import build_standard_model, _digest, _limit, _SCHEMA
from .normal_surface_geometry import _coordinates


class PositiveWitnessCache:
    """Inclusion-minimal supports of checked positive integer kernel vectors.

    Equivalently, the zero sets form an inclusion-maximal antichain.  A vector
    with smaller support answers every zero-coordinate restriction answered by
    a vector with larger support.  Matrices, objectives and vectors are copied;
    callers cannot invalidate an accepted witness by mutating their inputs.

    ``capacity=0`` disables the global cache.  A finite capacity evicts the
    oldest retained support after antichain pruning.  This affects performance
    only.  The producer separately retains its current state's witness.
    """

    def __init__(self, matrix, objective, *, capacity=256, check=lambda: None):
        _limit('capacity', capacity)
        self.objective = tuple(objective)
        self.width = len(self.objective)
        self.matrix = tuple(tuple(row) for row in matrix)
        if (any(type(x) is not int for x in self.objective)
                or any(len(row) != self.width or any(type(x) is not int for x in row)
                       for row in self.matrix)):
            raise ValueError('the witness cache requires an integer matrix and objective')
        self.capacity = capacity
        self.check = check
        self._entries = []
        self._measured = dict(cache_witnesses_checked=0, cache_dominated=0,
                              cache_evictions=0, cache_max_entries=0,
                              cache_support_comparisons=0)

    @property
    def entries(self):
        """Immutable ``(support_mask, witness)`` pairs, oldest first."""
        return tuple(self._entries)

    def stats(self):
        return dict(self._measured, cache_entries=len(self._entries))

    def add(self, vector):
        """Check a positive kernel witness exactly, retain if useful, return mask."""
        self.check()
        vector = tuple(vector)
        if len(vector) != self.width or any(type(x) is not int or x < 0 for x in vector):
            raise ValueError('a witness must be a nonnegative integer vector of the model width')
        if sum(x*c for x, c in zip(vector, self.objective)) <= 0:
            raise ValueError('a cached witness must have strictly positive objective')
        for row in self.matrix:
            self.check()
            if sum(a*x for a, x in zip(row, vector)):
                raise ValueError('a cached witness must satisfy every matching equation')
        self._measured['cache_witnesses_checked'] += 1
        mask = sum(1 << j for j, x in enumerate(vector) if x)
        if self.capacity == 0:
            return mask
        retained = []
        for support, witness in self._entries:
            self.check()
            self._measured['cache_support_comparisons'] += 1
            if support & mask == support:
                self._measured['cache_dominated'] += 1
                return mask
            if support & mask != mask:
                retained.append((support, witness))
            else:
                self._measured['cache_dominated'] += 1
        retained.append((mask, vector))
        if self.capacity is not None and len(retained) > self.capacity:
            retained.pop(0)
            self._measured['cache_evictions'] += 1
        self._entries = retained
        self._measured['cache_max_entries'] = max(
            self._measured['cache_max_entries'], len(retained))
        return mask

    def covers(self, allowed_mask):
        """Whether a stored exact witness survives this complete column mask."""
        if (type(allowed_mask) is not int or allowed_mask < 0
                or allowed_mask >> self.width):
            raise ValueError('allowed_mask must be a nonnegative model-width bit mask')
        for support, _ in self._entries:
            self.check()
            self._measured['cache_support_comparisons'] += 1
            if support & allowed_mask == support:
                return True
        return False


def search_positive_euler(triangulation, *, max_branch_depth=12, max_nodes=1000,
                          max_pivots=100000, allowed_branch_tetrahedra=None,
                          max_cached_witnesses=256,
                          check=lambda: None):
    """Return POSITIVE_EULER, NO_POSITIVE_EULER, or INCONCLUSIVE.

    Coordinate-deletion queries are screened by exact positive witnesses.
    Current-node LPs are always solved afresh, preserving witness-dependent
    branching and certificate equality with the baseline when budgets suffice.
    ``max_cached_witnesses`` bounds the antichain (None means no bound); zero
    retains only the current witness for screening.

    Every LP call shares ``max_pivots``.  ``max_nodes`` counts nodes across all
    triangle-anchor assignments; ``max_branch_depth`` counts only actual
    quadrilateral branching, not deterministic propagation.  A limit prevents
    a negative conclusion and yields INCONCLUSIVE, never a knot verdict.

    ``allowed_branch_tetrahedra`` optionally restricts guesses to a supplied
    distinct list of tetrahedron indices.  Mandatory implications still apply
    everywhere.  Remaining allowed tetrahedra are branched even if the current
    relaxed witness happens to have only one quad type there; this is needed
    for complete exploration of a supplied strong backdoor.

    Positive certificates contain primitive integer standard coordinates.
    Negative certificates contain one complete dual-certified tree for every
    anchor tuple.  The independent verifier reconstructs the source model and
    checks those trees without calling this search or an LP solver.
    """
    _limit('max_cached_witnesses', max_cached_witnesses)
    for name, value in (('max_branch_depth', max_branch_depth),
                        ('max_nodes', max_nodes), ('max_pivots', max_pivots)):
        _limit(name, value)
    check()
    model = build_standard_model(triangulation, check=check)
    t, width = model['tetrahedra'], model['variables']
    cache = PositiveWitnessCache(model['matrix'], model['euler'],
                                 capacity=max_cached_witnesses, check=check)
    if allowed_branch_tetrahedra is not None and (
            type(allowed_branch_tetrahedra) is not list
            or any(type(a) is not int or not 0 <= a < t for a in allowed_branch_tetrahedra)
            or len(set(allowed_branch_tetrahedra)) != len(allowed_branch_tetrahedra)):
        raise ValueError('allowed_branch_tetrahedra must be a distinct list of tetrahedron indices or None')
    branchable = set(range(t) if allowed_branch_tetrahedra is None else allowed_branch_tetrahedra)
    source = _digest(triangulation)
    stats = dict(tetrahedra=t, vertices=model['vertices'], variables=width,
                 equations=len(model['matrix']),
                 anchor_assignments=prod(map(len, model['anchor_groups'])),
                 anchors_started=0, anchors_completed=0, nodes=0, branches=0,
                 propagations=0, lp_calls=0, lp_pivots=0, tableau_updates=0,
                 maximum_tableau_bits=0, maximum_branch_depth=0,
                 branched_tetrahedra=[], deletion_queries=0,
                 deletion_lp_calls=0, node_lp_calls=0,
                 witness_local_hits=0, witness_antichain_hits=0)
    limits = dict(max_branch_depth=max_branch_depth, max_nodes=max_nodes,
                  max_pivots=max_pivots, max_cached_witnesses=max_cached_witnesses,
                  allowed_branch_tetrahedra=None if allowed_branch_tetrahedra is None
                  else sorted(allowed_branch_tetrahedra))

    def finish(status, **fields):
        stats.update(cache.stats())
        return dict(status=status, stats=dict(stats), limits=limits, **fields)

    def relaxed(anchors, allowed, forbidden=None, current_support=None):
        check()
        if forbidden is not None:
            stats['deletion_queries'] += 1
            # This support belongs to the current LP at exactly this state.
            # Pinning it separately preserves the support bound even if the
            # global antichain is capacity-limited or disabled.
            if current_support is not None and not current_support & (1 << forbidden):
                stats['witness_local_hits'] += 1
                return dict(status='POSITIVE', screened=True)
        zeros = set(anchors)
        columns = [j for j in range(width) if j not in zeros
                   and (j % 7 < 4 or j % 7-4 in allowed[j//7])
                   and j != forbidden]
        if forbidden is not None:
            mask = sum(1 << j for j in columns)
            if cache.covers(mask):
                stats['witness_antichain_hits'] += 1
                return dict(status='POSITIVE', screened=True)
            stats['deletion_lp_calls'] += 1
        else:
            stats['node_lp_calls'] += 1
        matrix = [[row[j] for j in columns] for row in model['matrix']]
        objective = [model['euler'][j] for j in columns]
        remaining = None if max_pivots is None else max_pivots-stats['lp_pivots']
        answer = solve_nonnegative_kernel(matrix, objective,
                                         max_pivots=remaining, check=check)
        stats['lp_calls'] += 1
        measured = answer['stats']
        stats['lp_pivots'] += measured['pivots']
        stats['tableau_updates'] += measured['tableau_updates']
        stats['maximum_tableau_bits'] = max(stats['maximum_tableau_bits'],
                                            measured['maximum_tableau_bits'])
        if answer['status'] == 'POSITIVE':
            flat = [0]*width
            for j, value in zip(columns, answer['primitive_x']):
                flat[j] = value
            answer['support_mask'] = cache.add(flat)
            answer['coordinates'] = [flat[7*a:7*a+7] for a in range(t)]
        return answer

    def visit(anchors, allowed, depth):
        check()
        if max_nodes is not None and stats['nodes'] >= max_nodes:
            return dict(status='INCONCLUSIVE', reason='node allowance exhausted')
        stats['nodes'] += 1
        stats['maximum_branch_depth'] = max(stats['maximum_branch_depth'], depth)
        steps = []
        while True:
            current = relaxed(anchors, allowed)
            if current['status'] == 'INCONCLUSIVE':
                return dict(status='INCONCLUSIVE', reason=current['reason'])
            if current['status'] == 'NONPOSITIVE':
                tree = dict(propagations=steps,
                            terminal=dict(kind='NONPOSITIVE', y=current['y']))
                return dict(status='NO_POSITIVE_EULER', tree=tree)
            rows = current['coordinates']
            conflicts = [a for a, row in enumerate(rows)
                         if sum(value > 0 for value in row[4:]) > 1]
            if not conflicts:
                analysed = _coordinates(model['prepared'], rows, check)
                if analysed['euler_characteristic'] <= 0:
                    raise ArithmeticError('positive LP witness has nonpositive Euler characteristic')
                return dict(status='POSITIVE_EULER', coordinates=rows,
                            euler_characteristic=analysed['euler_characteristic'])
            forced = False
            for a in range(t):
                if len(allowed[a]) < 2:
                    continue
                for q in allowed[a]:
                    test = relaxed(anchors, allowed, forbidden=7*a+4+q,
                                   current_support=current['support_mask'])
                    if test['status'] == 'INCONCLUSIVE':
                        return dict(status='INCONCLUSIVE', reason=test['reason'])
                    if test['status'] == 'NONPOSITIVE':
                        steps.append(dict(tetrahedron=a, type=q, y=test['y']))
                        stats['propagations'] += 1
                        allowed = allowed[:a] + ((q,),) + allowed[a+1:]
                        forced = True
                        break
                if forced:
                    break
            if forced:
                continue
            candidates = [a for a in conflicts if a in branchable]
            if not candidates:
                candidates = [a for a in sorted(branchable) if len(allowed[a]) >= 2]
            if not candidates:
                return dict(status='INCONCLUSIVE', reason='allowed branch tetrahedra exhausted')
            if max_branch_depth is not None and depth >= max_branch_depth:
                return dict(status='INCONCLUSIVE', reason='branch depth allowance exhausted')
            a = candidates[0]
            stats['branches'] += 1
            stats['branched_tetrahedra'] = sorted(set(stats['branched_tetrahedra']) | {a})
            children = []
            for q in allowed[a]:
                child_allowed = allowed[:a] + ((q,),) + allowed[a+1:]
                child = visit(anchors, child_allowed, depth+1)
                if child['status'] != 'NO_POSITIVE_EULER':
                    return child
                children.append(dict(type=q, tree=child['tree']))
            return dict(status='NO_POSITIVE_EULER', tree=dict(propagations=steps,
                        terminal=dict(kind='BRANCH', tetrahedron=a, children=children)))

    trees = []
    for anchors in product(*model['anchor_groups']):
        check()
        stats['anchors_started'] += 1
        answer = visit(anchors, ((0, 1, 2),)*t, 0)
        if answer['status'] == 'INCONCLUSIVE':
            return finish('INCONCLUSIVE', reason=answer['reason'])
        if answer['status'] == 'POSITIVE_EULER':
            certificate = dict(schema=_SCHEMA, source_sha256=source,
                               status='POSITIVE_EULER', anchors=list(anchors),
                               coordinates=answer['coordinates'])
            return finish('POSITIVE_EULER', coordinates=answer['coordinates'],
                          euler_characteristic=answer['euler_characteristic'],
                          certificate=certificate)
        stats['anchors_completed'] += 1
        trees.append(dict(anchors=list(anchors), tree=answer['tree']))
    certificate = dict(schema=_SCHEMA, source_sha256=source,
                       status='NO_POSITIVE_EULER', anchor_trees=trees)
    return finish('NO_POSITIVE_EULER', certificate=certificate)
