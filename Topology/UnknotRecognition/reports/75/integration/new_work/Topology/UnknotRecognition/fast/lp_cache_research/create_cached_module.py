"""One-time construction of the reviewed additive producer, retained for audit."""

from hashlib import sha256
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
source_bytes = (ROOT / 'fastunknot/normal_propagation.py').read_bytes()
if sha256(source_bytes).hexdigest() != '147f4b504756036f0c56999f9f8e34747c20f9e36014b9361f1261428cbbc905':
    raise SystemExit('the additive fork generator requires the audited baseline source')
source = source_bytes.decode()
body = source[source.index('def search_positive_euler('):]
body = body.replace('max_pivots=100000, allowed_branch_tetrahedra=None,',
                    'max_pivots=100000, allowed_branch_tetrahedra=None,\n'
                    '                          max_cached_witnesses=256,')
body = body.replace('    for name, value in ((\'max_branch_depth\'',
                    "    _limit('max_cached_witnesses', max_cached_witnesses)\n"
                    "    for name, value in (('max_branch_depth'")
body = body.replace("    t, width = model['tetrahedra'], model['variables']",
                    "    t, width = model['tetrahedra'], model['variables']\n"
                    "    cache = PositiveWitnessCache(model['matrix'], model['euler'],\n"
                    "                                 capacity=max_cached_witnesses, check=check)")
body = body.replace('                 branched_tetrahedra=[])',
                    '                 branched_tetrahedra=[], deletion_queries=0,\n'
                    '                 deletion_lp_calls=0, node_lp_calls=0,\n'
                    '                 witness_local_hits=0, witness_antichain_hits=0)')
body = body.replace('max_pivots=max_pivots,\n',
                    'max_pivots=max_pivots, max_cached_witnesses=max_cached_witnesses,\n')
body = body.replace('        return dict(status=status, stats=dict(stats), limits=limits, **fields)',
                    '        stats.update(cache.stats())\n'
                    '        return dict(status=status, stats=dict(stats), limits=limits, **fields)')
start = body.index('    def relaxed(')
stop = body.index("        matrix = [[row[j] for j in columns]", start)
body = body[:start] + '''    def relaxed(anchors, allowed, forbidden=None, current_support=None):
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
''' + body[stop:]
body = body.replace("            answer['coordinates'] = [flat[7*a:7*a+7] for a in range(t)]",
                    "            answer['support_mask'] = cache.add(flat)\n"
                    "            answer['coordinates'] = [flat[7*a:7*a+7] for a in range(t)]")
body = body.replace('test = relaxed(anchors, allowed, forbidden=7*a+4+q)',
                    "test = relaxed(anchors, allowed, forbidden=7*a+4+q,\n"
                    "                                   current_support=current['support_mask'])")
header = '''"""Exact, certificate-preserving screening for positive-Euler propagation.

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


'''
result = header + body
needle = '    """Return POSITIVE_EULER, NO_POSITIVE_EULER, or INCONCLUSIVE.\n'
result = result.replace(needle, needle + '''
    Coordinate-deletion queries are screened by exact positive witnesses.
    Current-node LPs are always solved afresh, preserving witness-dependent
    branching and certificate equality with the baseline when budgets suffice.
    ``max_cached_witnesses`` bounds the antichain (None means no bound); zero
    retains only the current witness for screening.
''')
(ROOT / 'fastunknot/normal_propagation_cached.py').write_text(result)
