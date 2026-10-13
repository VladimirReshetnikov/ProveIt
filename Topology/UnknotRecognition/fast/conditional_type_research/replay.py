"""Replay archived matching experiments, without rerunning discovery.

Run from the fast directory with python -B -S -m conditional_type_research.replay.
The historical scratch scripts remain inert archive data.
"""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from . import closure, witnesses
from .common import (GROUPS, check_archive_bytes, digest, load_archive,
                     save, source_hashes, staged_archive)


def _historical(group, staged_raw):
    probe, raw = load_archive(group, 'probe.json')
    old, _ = load_archive(group, 'replay.json')
    script, script_raw = load_archive(group, 'probe.py')
    replay_script, replay_raw = load_archive(group, 'replay.py')
    assert script and replay_script
    assert probe['passed'] is True and old['passed'] is True
    assert probe['script_sha256'] == sha256(script_raw).hexdigest()
    assert old['script_sha256'] == sha256(replay_raw).hexdigest()
    assert old['probe_sha256'] == sha256(raw).hexdigest()
    assert probe['staged_audit_sha256'] == sha256(staged_raw).hexdigest()
    assert digest(probe['source_sha256']) == digest(old['source_sha256'])
    pins = probe['source_sha256']
    assert type(pins) is dict and pins
    assert all(type(k) is str and type(v) is str and len(v) == 64
               and all(c in '0123456789abcdef' for c in v) for k, v in pins.items())
    assert old['discovery_used'] is False and old['general_quasipolynomial'] is False
    assert type(probe['max_checks_per_source']) is int and probe['max_checks_per_source'] == 1000000
    assert probe['no_timing_claim'] is True
    return probe, old, dict(group=group, probe_sha256=sha256(raw).hexdigest(),
        generation_pins_sha256=digest(pins), generation_pin_count=len(pins),
        generation_pins_are_historical=True)


def check():
    if not __debug__:
        raise RuntimeError('archival replay requires assertions enabled')
    pins = source_hashes()
    byte_summary = check_archive_bytes()
    archive, staged_raw = staged_archive()
    assert archive['passed'] is True
    assert [r['id'] for r in archive['records']] == ['T', 'F', 'TT', 'T25', 'T27', 'W34']
    cheap, old_cheap, cheap_meta = _historical(GROUPS[0], staged_raw)
    exact, old_exact, exact_meta = _historical(GROUPS[1], staged_raw)
    assert cheap['schema'] == 'scratch-conditional-type-elimination-v1'
    assert cheap['no_lp_ray_or_pachner_discovery'] is True
    assert type(cheap['maximum_total_discovery_checks']) is int
    assert cheap['maximum_total_discovery_checks'] == 6000000
    assert exact['schema'] == 'scratch-conditional-type-witnesses-v1'
    assert exact['no_lp_rowpair_ray_or_pachner_discovery'] is True
    assert exact['no_global_deletions'] is True
    assert type(exact['maximum_total_construction_checks']) is int
    assert exact['maximum_total_construction_checks'] == 6000000
    assert type(exact['expected_tests']) is int and exact['expected_tests'] == 276
    assert len(cheap['records']) == len(exact['records']) == len(archive['records']) == 6
    cheap_records, exact_records, control = [], [], None
    for earlier, later, source in zip(cheap['records'], exact['records'], archive['records']):
        # Type-sensitive canonical JSON equality binds both experiments to
        # the same labelled source and original PD, independently of pins.
        assert digest(earlier['source']) == digest(later['source'])
        assert digest(earlier['input_pd']) == digest(later['input_pd'])
        one, other_forced = closure.replay_record(earlier, source, 1000000)
        assert not other_forced and one['conditional_provenance_packets'] == 0 and one['deletions'] == 0
        two, first = witnesses.replay_record(later, source, 1000000)
        cheap_records.append(one)
        exact_records.append(two)
        if control is None:
            control = first
    assert digest(cheap_records) == digest(old_cheap['records'])
    assert old_cheap['other_forced_deletion_controls'] == []
    assert digest(exact_records) == digest(old_exact['records'])
    assert old_exact['staged_audit_sha256'] == sha256(staged_raw).hexdigest()
    controls = witnesses.corruption_controls(control)
    assert len(controls) == 12 and digest(controls) == digest(old_exact['rejected_corruption_controls'])
    assert old_exact['all_initial_conditional_types_feasible'] is True
    assert type(old_exact['verified_matching_witnesses']) is int and old_exact['verified_matching_witnesses'] == 276
    assert [r['queries'] for r in cheap_records] == [21, 30, 48, 33, 51, 33]
    assert [r['checks_used'] for r in cheap_records] == [7924, 30890, 212610, 52604, 290842, 1000000]
    assert [r['status'] for r in cheap_records] == ['SUFFICIENT_CLOSURE_FIXED_POINT']*5+['CAPPED']
    assert [r['verified_matching_witnesses'] for r in exact_records] == [21, 30, 48, 33, 51, 93]
    assert [r['checks_used'] for r in exact_records] == [3047, 6242, 16034, 7559, 18107, 60359]
    assert all(r['all_initial_conditional_types_feasible'] is True for r in exact_records)
    assert all(r['uncertified_zero_diagnostics'] == 0 for r in exact_records)
    assert source_hashes() == pins, 'replay dependencies changed during replay'
    return dict(schema='conditional-type-archival-replay-v1', passed=True,
        source_sha256=pins, archive_bytes=byte_summary,
        historical_provenance=[cheap_meta, exact_meta],
        staged_source_archive_sha256=sha256(staged_raw).hexdigest(),
        cheap_closure=dict(attempted_queries=216, returned_queries=215, capped_queries=1,
            deleted_types=0, conditional_provenance_packets=0, construction_checks=1594870,
            records=cheap_records, other_forced_deletion_controls=0),
        exact_witnesses=dict(verified_matching_witnesses=276, completed_sources=6,
            construction_checks=111348, all_initial_conditional_types_feasible=True,
            records=exact_records, rejected_corruption_controls=controls),
        source_bindings_between_experiments=6, discovery_used=False,
        timing_claim=False, native_conditional_elimination_added=False, general_quasipolynomial=False,
        historical_scope='Original source-pin maps and absolute-path generation scripts are preserved historical data; only this replay source_sha256 map describes current dependencies.',
        cheap_scope='Retained sufficient-closure outcomes, not independently recomputed kernel ranks or sufficient-rule operation traces; W34 remains capped in this experiment.',
        witness_scope='Original STANDARD nonnegative integer matching witnesses with positive tested Q coordinate and zero competitors at that tetrahedron; no Euler sign, extremality, global compatibility or knot verdict.',
        counter_scope='Recorded construction callbacks, with type/range/continuity checks; independent replay excluded and no timing or exact bit-operation claim.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = check()
    if args.output:
        save(args.output, result)
    print(json.dumps(dict(passed=True, experiment_groups=2,
        cheap_attempted_queries=216, cheap_returned_queries=215, cheap_capped_queries=1,
        global_deletions=0, exact_matching_witnesses=276, source_bindings=6,
        rejected_corruption_controls=12, source_pins=len(result['source_sha256']),
        discovery_used=False, general_quasipolynomial=False), sort_keys=True))


if __name__ == '__main__':
    main()
