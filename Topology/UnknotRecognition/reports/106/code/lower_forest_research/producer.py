"""A bounded, baseline-first portfolio of geometric lower spanning forests.

This module is a producer adapter for the native API pinned in the accompanying
research report.  It never supplies a verifier with prepared source geometry.
Its successful packets use the ordinary native schema and independent checker.
The two alternative policies are exceptional-unit-columns first and reverse
handle order.  They do not decide all possible lower forests.
"""

from types import FunctionType

from fastunknot.core_handlebody import (
    _forest, _occurrences, column_cancellation_plan,
    core_handlebody_certificate, leaf_cancellation_plan,
)
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies as _native


def _orbit_cycles(result):
    """Count the actual discovery cycles spent by one native composed call."""
    return sum(item.get('orbit_cycles', 0)
               for phase in ('parallelity', 'boundary')
               for item in result.get('stats', {}).get(phase, {}).values())


def _alternative_core(core, state, *, check):
    baseline = core_handlebody_certificate(core, check=check)
    if baseline['status'] == 'COMPLETE' or core['handles3']:
        return baseline
    check()
    original = core['handles1']
    identifiers = list(range(len(original)))
    raw_rows = _occurrences(core, [], check)
    owners, totals = {}, {}
    for row in raw_rows.values():
        check()
        for column, value in row.items():
            owners[column] = owners.get(column, 0) + 1
            totals[column] = totals.get(column, 0) + value
    exceptional = {c for c in owners if owners[c] == totals[c] == 3}
    orders = (
        ('exceptional_first', sorted(identifiers,
                                    key=lambda i: (i not in exceptional, i))),
        ('reverse', list(reversed(identifiers))),
    )
    record = dict(core_counts=[len(core[f'handles{i}']) for i in range(4)],
                  baseline_reason=baseline.get('reason'), trials=[])
    state['core_searches'].append(record)
    for policy, order in orders:
        check()
        if state['extra_forests'] == state['max_extra_forests']:
            state['forest_limit_reached'] = True
            break
        state['extra_forests'] += 1
        # Only the traversal order changes.  Source labels, handle charts and
        # attaching cycles retain their original identities and contents.
        forest, owners = _forest(
            dict(core, handles1=[original[i] for i in order]), check)
        counts = _occurrences(core, forest, check)
        planned = leaf_cancellation_plan(counts, check=check)
        method = 'leaf'
        if planned['remaining_rows']:
            planned = column_cancellation_plan(counts, check=check)
            method = 'column_leaf'
        trial = dict(policy=policy, forest=forest,
                     remaining_rows=planned['remaining_rows'])
        record['trials'].append(trial)
        if planned['remaining_rows']:
            continue
        alive = set(identifiers) - set(forest)
        alive.difference_update(c for _, c in planned['cancellations'])
        components = []
        for owner in sorted(set(owners)):
            check()
            vertices = [v for v, root in enumerate(owners) if root == owner]
            loops = [i for i in sorted(alive)
                     if owners[original[i]['ends'][0]] == owner]
            components.append(dict(id=owner, zero_handles=vertices,
                                   remaining_one_handles=loops, genus=len(loops)))
        schema = ('normal-core-handlebody-v2' if method == 'column_leaf'
                  else 'normal-core-handlebody-v1')
        proof = dict(schema=schema, method=method, forest=forest,
                     cancellations=planned['cancellations'], components=components)
        if not verify_core_handlebody_certificate(core, proof, check=check):
            raise ArithmeticError('alternative lower-forest proof failed native replay')
        trial['independent_core_replay'] = True
        check()
        return dict(status='COMPLETE', trust=baseline['trust'],
                    stats=planned['stats'], certificate=proof, components=components)
    return baseline


def normal_cut_handlebodies_with_forests(
        triangulation, coordinates, *, max_extra_forests=4, max_cycles=None,
        record_certificate=False, precheck_core=True, check=lambda: None):
    """Try the native producer, then at most two alternative policies per core.

    Every native COMPLETE result is returned immediately and unchanged.  On a
    native refusal, retry the same whole-cut logic with a private core-planner
    binding.  The total number of alternative forests, across all core calls in
    that retry, is bounded by ``max_extra_forests``.  Its default four permits
    both policies for an initial core and for a disk-bundle-augmented core.
    Zero disables the retry.  There is no randomized search or retained state.

    ``max_cycles`` bounds the sum of orbit-discovery cycles spent by the initial
    call and retry.  The native cycle accounting is preserved within each call.
    A depleted allowance or unsuccessful policy portfolio yields INCONCLUSIVE;
    it provides no negative topological conclusion.  Callback cancellation
    propagates immediately.  No public module globals or source inputs change.

    FunctionType copies the already imported function's globals rather than
    loading a file or mutating its module.  This research adapter depends on the
    native core-planner binding; it does not promise compatibility with future
    rewrites of the composed producer.
    """
    check()
    if type(max_extra_forests) is not int or max_extra_forests < 0:
        raise ValueError('max_extra_forests must be a nonnegative integer')
    # Delegate native option and source validation to the unchanged public API.
    baseline = _native(triangulation, coordinates, max_cycles=max_cycles,
                       record_certificate=record_certificate,
                       precheck_core=precheck_core, check=check)
    if baseline['status'] == 'COMPLETE' or max_extra_forests == 0:
        return baseline
    used = _orbit_cycles(baseline)
    if max_cycles is not None and used >= max_cycles:
        return baseline
    state = dict(max_extra_forests=max_extra_forests, extra_forests=0,
                 forest_limit_reached=False, core_searches=[])

    def alternate(core, *, check=lambda: None):
        return _alternative_core(core, state, check=check)

    if 'core_handlebody_certificate' not in _native.__code__.co_names:
        raise RuntimeError('native producer no longer exposes its core planner binding')
    private_globals = dict(_native.__globals__, core_handlebody_certificate=alternate)
    retry = FunctionType(_native.__code__, private_globals, _native.__name__,
                         _native.__defaults__, _native.__closure__)
    retry.__kwdefaults__ = dict(_native.__kwdefaults__ or {})
    remaining = None if max_cycles is None else max_cycles - used
    result = retry(triangulation, coordinates, max_cycles=remaining,
                   record_certificate=record_certificate,
                   precheck_core=precheck_core, check=check)
    state.update(baseline_reason=baseline.get('reason'),
                 baseline_orbit_cycles=used,
                 retry_orbit_cycles=_orbit_cycles(result))
    state['total_orbit_cycles'] = used + state['retry_orbit_cycles']
    result['stats']['lower_forest_portfolio'] = state
    check()
    return result
