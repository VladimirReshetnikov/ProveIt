"""Compare restarted and shared region searches on the same native sources.

Run from fast/: python -m shared_cover_research.benchmark --output FILE.json
Replay stored positives: python -m shared_cover_research.benchmark --replay FILE.json

All sources are chains of the six-cell first-descent gadget attached to a
layered solid torus.  They have no initial native 3--2 move.  Each requires
an upward move before a descent; the declared search allowance is U=1,r=6.
Full-exhaustion timings disable disc queries and endpoint collection in both
implementations.  First-descent timings include the same independent replay.
Endpoint equality is checked separately by exact cochain-isomorphism keys,
not floating-point features or hashes.  The small finite cohort establishes
regression and implementation evidence, not a general runtime prediction.
"""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import platform
from statistics import median
import sys
from time import perf_counter

from causal_research.fixtures import descent_gadgets
from commitment_research.fixtures import canonical_cochain_key
from fastunknot.pachner_commitments import _State, _events
from fastunknot.pachner_cover_search import search_pachner_cover, find_pachner_descent
from fastunknot.pachner_cover_verify import verify_pachner_cover, inspect_pachner_descent
from fastunknot.pachner_regions import search_pachner_regions


FAST = Path(__file__).resolve().parents[1]


def _inventory():
    names = ('fastunknot/pachner_cover_search.py', 'fastunknot/pachner_cover_verify.py',
             'fastunknot/pachner_regions.py', 'fastunknot/pachner_commitments.py',
             'fastunknot/pachner_commitments_verify.py', 'causal_research/fixtures.py',
             'commitment_research/fixtures.py', 'shared_cover_research/benchmark.py')
    return {name: sha256((FAST/name).read_bytes()).hexdigest() for name in names}


def _representatives(raw, heights, certificates, cache):
    result = {}
    for proof in certificates:
        trace = proof['moves']
        after = trace[-1]['triangulation'] if trace else raw
        transported = trace[-1]['transport']['heights'] if trace else heights
        # The restarted search repeats identical endpoints in many covers.
        # Full serialized row/cochain equality is a safe memoization key; a
        # digest collision cannot change the endpoint-set comparison.
        normalized = [[x-row[0] for x in row] for row in transported]
        serialization = json.dumps((after, normalized), sort_keys=True,
                                   separators=(',', ':'))
        if serialization not in cache:
            cache[serialization] = canonical_cochain_key(after, transported)
        key = cache[serialization]
        result.setdefault(key, proof)
    return result


def _smaller_than(n):
    return lambda proof: bool(proof['moves'] and
        len(proof['moves'][-1]['triangulation']['tetrahedra']) < n)


def run(sizes=(1, 2), repeats=3, descent_only=False):
    if repeats < 1:
        raise ValueError('repeats must be positive')
    started = perf_counter()
    inventory = _inventory()
    cases = []
    accepted = 0
    for count in sizes:
        fixture = descent_gadgets(count)
        raw, heights = fixture['triangulation'], fixture['heights']
        n = len(raw['tetrahedra'])
        events = _events(_State(raw, heights, tuple(range(n)), 0, 0, ()),
                         True, lambda: None)
        downs = sum(event.kind == 'down' for event in events)
        if downs:
            raise AssertionError('a purported upward-required fixture already descends')
        common = dict(max_region_size=6, max_upward=1, method='sleep',
                      max_nodes=None, seek_disc=False)
        old = new = None
        old_keys, new_keys = {}, {}
        if not descent_only:
            old = search_pachner_regions(raw, heights, collect_endpoints=True, **common)
            new = search_pachner_cover(raw, heights, collect_endpoints=True, **common)
            if (old['status'] != 'COMPLETE_BOUNDED_REGIONS'
                    or new['status'] != 'COMPLETE_BOUNDED_COVER_FAMILY'):
                raise AssertionError('an endpoint comparison did not exhaust')
            cache = {}
            old_keys = _representatives(raw, heights, old['endpoints'], cache)
            new_keys = _representatives(raw, heights, new['endpoints'], cache)
            if old_keys.keys() != new_keys.keys():
                raise AssertionError('exact cochain-isomorphism endpoint sets differ')
        # Retain and replay every shared marked endpoint plus one old proof for
        # each geometric endpoint.  All are complete source-bound certificates.
        kept_old = list(old_keys.values())
        kept_new = [] if descent_only else new['endpoints']
        for proof in kept_old+kept_new:
            if not verify_pachner_cover(raw, heights, proof,
                                        max_region_size=6, max_upward=1):
                raise AssertionError('a retained covered endpoint failed independent replay')
            accepted += 1
        exhausted = dict(restart=[], shared=[])
        descent = dict(restart=[], shared=[])
        selected = {}
        for repetition in range(repeats):
            # Alternate order to avoid assigning every first/cold run to one
            # implementation.  Source construction and validation audits are
            # excluded identically from these timed calls.
            methods = [('restart', search_pachner_regions), ('shared', search_pachner_cover)]
            if repetition % 2:
                methods.reverse()
            for name, function in methods:
                if not descent_only:
                    begin = perf_counter()
                    answer = function(raw, heights, **common)
                    elapsed = perf_counter()-begin
                    expected = ('COMPLETE_BOUNDED_REGIONS' if name == 'restart'
                                else 'COMPLETE_BOUNDED_COVER_FAMILY')
                    if answer['status'] != expected:
                        raise AssertionError('a timing call failed to exhaust')
                    exhausted[name].append(dict(seconds=elapsed, stats=answer['stats']))
                begin = perf_counter()
                positive = function(raw, heights, endpoint=_smaller_than(n), **common)
                if positive['status'] != 'ENDPOINT_SELECTED':
                    raise AssertionError('a first-descent call did not find its witness')
                replay = inspect_pachner_descent(raw, heights, positive['certificate'],
                                                max_upward=1, max_region_size=6)
                if replay is None:
                    raise AssertionError('timed descent replay failed')
                elapsed = perf_counter()-begin
                if (replay['upward_moves'], replay['downward_moves']) != (1, 2):
                    raise AssertionError('unexpected first-descent move counts')
                descent[name].append(dict(seconds=elapsed, stats=positive['stats']))
                selected[name] = positive['certificate']
                accepted += 1
        timed_kinds = [('first_descent', descent)]
        if not descent_only:
            timed_kinds.insert(0, ('exhaustion', exhausted))
        medians = {kind: {name: median(row['seconds'] for row in samples[name])
                         for name in ('restart', 'shared')}
                   for kind, samples in timed_kinds}
        ratios = {kind: times['restart']/times['shared'] for kind, times in medians.items()}
        wrapper = find_pachner_descent(raw, heights, max_upward=1, max_nodes=None)
        if wrapper['status'] != 'DESCENT_FOUND':
            raise AssertionError('public descent wrapper failed')
        cases.append(dict(gadget_count=count, tetrahedra=n, source=fixture,
            scope=dict(max_upward=1, max_region_size=6, max_components=1),
            initial_upward_candidates=len(events), initial_downward_candidates=downs,
            exhaustion_performed=not descent_only,
            equality=None if descent_only else 'exact signed-cochain isomorphism keys agree',
            geometric_endpoint_count=None if descent_only else len(new_keys),
            restart_endpoint_certificates=None if descent_only else len(old['endpoints']),
            shared_marked_endpoints=None if descent_only else len(new['endpoints']),
            restart_stats=descent['restart'][0]['stats'] if descent_only else old['stats'],
            shared_stats=descent['shared'][0]['stats'] if descent_only else new['stats'],
            exhaustion_samples=exhausted, first_descent_samples=descent,
            median_seconds=medians, median_speed_ratio_restart_over_shared=ratios,
            retained_restart_endpoints=kept_old, retained_shared_endpoints=kept_new,
            selected_descent_certificates=selected, public_descent_result=wrapper))
        final = cases[-1]
        print('gadgets', count, 'tetrahedra', n,
              'regions', final['shared_stats']['regions_indexed'],
              'frames', final['restart_stats']['nodes'], '->', final['shared_stats']['nodes'],
              'endpoints', final['geometric_endpoint_count'],
              'median speed ratios', ratios, flush=True)
    return dict(schema='shared-pachner-cover-benchmark-v1',
        created_utc=datetime.now(timezone.utc).isoformat(),
        command=[sys.executable, *sys.argv], python=platform.python_version(),
        platform=platform.platform(), source_sha256=inventory,
        repeats=repeats, descent_only=descent_only, elapsed_seconds=perf_counter()-started,
        timing_scope='same sources and U=1,r=6; disc queries disabled; median of paired runs',
        mathematical_scope='finite solid-torus cochain states, not arbitrary input knots',
        endpoint_equality='full exact cochain-isomorphism tuples, with no digest-only comparisons',
        accepted_independent_replays=accepted, cases=cases)


def replay(path):
    data = json.loads(Path(path).read_text())
    covered, descents = 0, 0
    for case in data['cases']:
        source = case['source']
        raw, heights = source['triangulation'], source['heights']
        for proof in case['retained_restart_endpoints']+case['retained_shared_endpoints']:
            if not verify_pachner_cover(raw, heights, proof, max_region_size=6, max_upward=1):
                raise AssertionError('stored covered endpoint failed independent replay')
            covered += 1
        for proof in list(case['selected_descent_certificates'].values())+[
                case['public_descent_result']['certificate']]:
            if inspect_pachner_descent(raw, heights, proof, max_upward=1) is None:
                raise AssertionError('stored descent failed independent replay')
            descents += 1
    return dict(input=str(path), covered_endpoint_replays=covered,
                strict_descent_replays=descents, accepted=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output')
    parser.add_argument('--replay')
    parser.add_argument('--sizes', default='1,2')
    parser.add_argument('--repeats', type=int, default=3)
    parser.add_argument('--descent-only', action='store_true')
    arguments = parser.parse_args()
    if not arguments.output and not arguments.replay:
        parser.error('supply --output or --replay')
    result = (replay(arguments.replay) if arguments.replay else
              run(tuple(int(value) for value in arguments.sizes.split(',')),
                  arguments.repeats, arguments.descent_only))
    if arguments.output:
        target = Path(arguments.output)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(result, indent=2)+'\n')
        print('saved', target, flush=True)
    else:
        print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
