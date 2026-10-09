"""A bounded, source-bound collapse-only research policy and chain replay.

Run a complete current 3--2 census, greedy maximal disjoint packing, and
optimal peeled-Euler subbatch selection until the chosen subbatch is empty.
The source must have at most two interior vertices, so selection uses only
the standard-library small-cover backend.  This is a geometric experiment;
neither stopping status is an unknot-recognition verdict.

The independent replay path checks the original coherent source, every
simultaneous replacement and its nonnegative peeled score, and the final
endpoint.  It does not rerun the candidate census or certify policy
optimality/STALLED.  An optional final native disc certificate concerns
only the supplied coherent surface at that endpoint.
"""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys


if __package__ in (None, ''):
    # The same file works after the research package is moved to code/fast.
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from fastunknot.cocycle_peeling_verify import verify_peeled_batch_score
from fastunknot.cocycle_transport_verify import (
    _check_signed_edges, _read_heights, _shield_callback)
from fastunknot.integer_codec import certificate_equal, encoded_integer, json_safe
from fastunknot.normal_surface_geometry import _prepare, _quad, NormalOrbitError


_CHAIN_SCHEMA = 'batched-cocycle-descent-chain-v1'
_RESULT_SCHEMA = 'batched-cocycle-descent-result-v1'


def _source_digest(triangulation, gauged_heights):
    """Bind the actual triangulation and cochain, ignoring local constants."""
    value = dict(triangulation=triangulation, heights=gauged_heights)
    data = json.dumps(json_safe(value), sort_keys=True, separators=(',', ':'))
    return hashlib.sha256(data.encode()).hexdigest()


def _edge_bits(heights):
    return max((max(row)-min(row)).bit_length() for row in heights)


def _coherent_coordinates(heights, check):
    """Independent reconstruction by sorted integer-level intervals."""
    answer = []
    for row in heights:
        check()
        a, b, c, d = sorted(range(4), key=lambda v: (row[v], v))
        values = [0]*7
        values[a], values[d] = row[b]-row[a], row[d]-row[c]
        values[4+_quad(a, b)] = row[c]-row[b]
        answer.append(values)
    return answer


@_shield_callback
def verify_descent_chain(triangulation, heights, certificate, *, check=lambda: None):
    """Verify a geometry chain against an externally supplied coherent source.

    Only the chain and optional endpoint disc count are certified.  Census
    sizes, matching optimality, timings, and STALLED/ROUND_LIMIT diagnostics
    are deliberately outside this consumer's contract.  Arbitrary callback
    exceptions propagate, including ValueError and cancellation exceptions.
    """
    check()
    fields = {'schema', 'source_sha256', 'steps', 'final', 'disk_certificate'}
    if (type(certificate) is not dict or set(certificate) != fields
            or certificate['schema'] != _CHAIN_SCHEMA
            or type(certificate['steps']) is not list
            or type(certificate['final']) is not dict
            or set(certificate['final']) != {'triangulation', 'heights'}):
        return False
    try:
        prepared = _prepare(triangulation, check)
        h = _read_heights(heights, len(prepared['tetrahedra']), check)
        if h is None or not _check_signed_edges(prepared, h, check):
            return False
        h = [[value-row[0] for value in row] for row in h]
        boundary = {prepared['vertex_roots'][4*t+v]
                    for t, f in prepared['boundary_faces']
                    for v in range(4) if v != f}
        if len(set(prepared['vertex_roots'])-boundary) > 2:
            return False
        if certificate['source_sha256'] != _source_digest(triangulation, h):
            return False
        initial_count, initial_bits = len(prepared['tetrahedra']), _edge_bits(h)
        current = triangulation
        moves = 0
        for step in certificate['steps']:
            check()
            if (type(step) is not dict
                    or set(step) != {'triangulation', 'move', 'peeling'}):
                return False
            after, move, score = step['triangulation'], step['move'], step['peeling']
            if not verify_peeled_batch_score(current, h, after, move, score,
                                              check=check):
                return False
            count = len(move['regions'])
            if not count or encoded_integer(score['peeled_euler_gain']) < 0:
                return False
            moves += count
            current = after
            h = _read_heights(move['cocycle']['heights'],
                              len(current['tetrahedra']), check)
            if h is None or _edge_bits(h) > initial_bits:
                return False
        if (moves > initial_count
                or len(current['tetrahedra']) != initial_count-moves
                or not certificate_equal(certificate['final'],
                        dict(triangulation=current, heights=h))):
            return False
        disk = certificate['disk_certificate']
        if disk is not None:
            from fastunknot.normal_disk_kernel import verify_normal_disk_count_certificate
            coordinates = _coherent_coordinates(h, check)
            if not verify_normal_disk_count_certificate(current, coordinates, disk,
                                                         check=check):
                return False
    except (NormalOrbitError, ValueError, TypeError, KeyError, IndexError):
        return False
    check()
    return True


def descend(triangulation, heights, *, max_rounds=None, max_work=None,
            endpoint_disk_count=False, max_disk_cycles=None, check=lambda: None):
    """Run the specified collapse policy, retaining independently checked steps.

    ``max_rounds=None`` runs until the policy stalls; tetrahedron count makes
    a collapse-only trajectory finite.  A nonnegative cap returns ROUND_LIMIT
    after that many committed batches, without an additional terminal census.
    ``max_work`` bounds callback ticks, not bit operations or wall time.
    Its exhaustion raises CocycleLimit.  All callback exceptions propagate;
    an interrupted private state is discarded and no partial result is returned.

    The optional native count may itself be INCONCLUSIVE under max_disk_cycles.
    Such a count supplies no endpoint certificate and does not change the
    geometric trajectory status.  No knot or diagram verdict is returned.
    """
    if max_rounds is not None and (type(max_rounds) is not int or max_rounds < 0):
        raise ValueError('max_rounds must be a nonnegative integer or None')
    if type(endpoint_disk_count) is not bool:
        raise ValueError('endpoint_disk_count must be bool')
    if max_disk_cycles is not None and (
            type(max_disk_cycles) is not int or max_disk_cycles < 0):
        raise ValueError('max_disk_cycles must be a nonnegative integer or None')
    from fastunknot.cocycle_peeling import CocyclePeelingState
    from fastunknot.normal_cocycle import _Budget, local_coordinates
    from fastunknot.pachner_batch import select_disjoint_collapses
    budget = _Budget(check, max_work)
    state = CocyclePeelingState(triangulation, heights, check=budget.tick)
    interior = sum(value == 2 for value in state.index.link_euler.values())
    if interior > 2:
        raise ValueError('this stdlib research policy requires at most two interior vertices')
    source = dict(triangulation=deepcopy(state.triangulation),
                  heights=deepcopy(state.heights))
    initial_count = len(state.triangulation['tetrahedra'])
    initial_bits = _edge_bits(state.heights)
    steps, diagnostics = [], []
    status, reason = 'ROUND_LIMIT', 'committed-round cap reached'
    while max_rounds is None or len(steps) < max_rounds:
        budget.tick()
        census = state.score_candidates()['candidates']
        packing = select_disjoint_collapses(census, check=budget.tick)
        ground = [census[i] for i in packing['selected_indices']]
        optimum = state.optimal_subbatch(ground)
        diagnostics.append(dict(before_tetrahedra=len(state.triangulation['tetrahedra']),
            eligible_edges=len(census), packed_moves=len(ground),
            retained_moves=optimum['retained_moves'],
            peeled_euler_gain=optimum['optimal_peeled_euler_gain']))
        if not optimum['sites']:
            status = 'STALLED'
            reason = 'empty legal census' if not census else 'empty optimal packed subbatch'
            break
        if optimum['optimal_peeled_euler_gain'] < 0:
            raise ArithmeticError('an optimal subbatch cannot improve on the empty batch negatively')
        before, before_h = deepcopy(state.triangulation), deepcopy(state.heights)
        result = state.apply_batch(optimum['sites'])
        if (not verify_peeled_batch_score(before, before_h, result['triangulation'],
                result['certificate'], result['peeling_certificate'], check=budget.tick)
                or result['peeling_certificate']['peeled_euler_gain']
                    != optimum['optimal_peeled_euler_gain']):
            raise ArithmeticError('committed batch failed independent score/geometry replay')
        steps.append(dict(triangulation=deepcopy(result['triangulation']),
                          move=deepcopy(result['certificate']),
                          peeling=deepcopy(result['peeling_certificate'])))
    final = dict(triangulation=deepcopy(state.triangulation),
                 heights=deepcopy(state.heights))
    disk_result, disk_proof = None, None
    if endpoint_disk_count:
        from fastunknot.normal_disk_kernel import (
            normal_compressing_disk_count, verify_normal_disk_count_certificate)
        coordinates = []
        for row in state.heights:
            budget.tick()
            coordinates.append(local_coordinates(row))
        disk_result = normal_compressing_disk_count(state.triangulation, coordinates,
            max_cycles=max_disk_cycles, record_certificate=True, check=budget.tick)
        if disk_result['status'] == 'COMPLETE':
            disk_proof = disk_result['certificate']
            if not verify_normal_disk_count_certificate(state.triangulation, coordinates,
                                                          disk_proof, check=budget.tick):
                raise ArithmeticError('final native disc count failed its independent verifier')
    certificate = dict(schema=_CHAIN_SCHEMA,
        source_sha256=_source_digest(source['triangulation'], source['heights']),
        steps=steps, final=final, disk_certificate=disk_proof)
    return dict(schema=_RESULT_SCHEMA, source=source, status=status, reason=reason,
        limits=dict(max_rounds=max_rounds, max_work=max_work,
                    max_disk_cycles=max_disk_cycles),
        stats=dict(committed_rounds=len(steps), individual_collapses=state.stats['moves'],
            initial_tetrahedra=initial_count, final_tetrahedra=len(state.heights),
            interior_vertices=interior, work=budget.work,
            initial_edge_difference_bits=initial_bits,
            final_edge_difference_bits=_edge_bits(state.heights)),
        round_diagnostics=diagnostics, certificate=certificate,
        endpoint_disk_count=disk_result,
        trust='source-bound geometric descent only; status and optimality are producer '
              'diagnostics; the chain consumer verifies moves, nonnegative peeled gains, '
              'and any optional disc count for the final coherent surface')


def main(argv=None):
    import argparse
    import os
    import tempfile
    from fastunknot.normal_cocycle import _Budget, CocycleLimit
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path,
        help='JSON with triangulation/heights, or an earlier result containing source')
    parser.add_argument('--output', type=Path, help='write JSON atomically here; default stdout')
    parser.add_argument('--max-rounds', type=int, default=None)
    parser.add_argument('--max-work', type=int, default=None)
    parser.add_argument('--disk-count', action='store_true')
    parser.add_argument('--max-disk-cycles', type=int, default=None)
    parser.add_argument('--replay', type=Path,
        help='verify this saved result against input; no producers or policy are run')
    args = parser.parse_args(argv)
    value = json.loads(args.input.read_text())
    source = value.get('source', value)
    if type(source) is not dict or set(source) != {'triangulation', 'heights'}:
        parser.error('source JSON must have exactly triangulation and heights')
    try:
        if args.replay:
            recorded = json.loads(args.replay.read_text())
            proof = recorded.get('certificate', recorded)
            budget = _Budget(lambda: None, args.max_work)
            verified = verify_descent_chain(source['triangulation'], source['heights'],
                                              proof, check=budget.tick)
            result = dict(verified=verified, work=budget.work,
                scope='geometry chain and optional endpoint disc count; no knot verdict')
        else:
            result = descend(source['triangulation'], source['heights'],
                max_rounds=args.max_rounds, max_work=args.max_work,
                endpoint_disk_count=args.disk_count, max_disk_cycles=args.max_disk_cycles)
            verified = True
    except CocycleLimit as error:
        parser.exit(2, str(error)+'; no interrupted trajectory was written\n')
    data = json.dumps(json_safe(result), sort_keys=True, indent=2)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        temporary = None
        try:
            with tempfile.NamedTemporaryFile(mode='w', dir=args.output.parent,
                    prefix=args.output.name+'.', suffix='.tmp', delete=False) as handle:
                temporary = Path(handle.name)
                handle.write(data)
            os.replace(temporary, args.output)
        finally:
            if temporary is not None and temporary.exists():
                temporary.unlink()
    else:
        print(data, end='')
    return 0 if verified else 1


if __name__ == '__main__':
    raise SystemExit(main())
