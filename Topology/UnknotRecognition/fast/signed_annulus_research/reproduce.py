"""Replay embedded native annulus fixtures and optionally compare Regina cuts.

From fast/: python -m signed_annulus_research.reproduce --output PATH --regina
The JSON fixture is sufficient for replay; the source-bank hash is checked
when that historical source file is present in the checkout.
"""

import argparse
import hashlib
import json
from pathlib import Path
import platform
import time

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies


def run(output, use_regina=False):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=True)
    certificates = output / 'certificates'
    certificates.mkdir(exist_ok=True)
    fixture = Path(__file__).with_name('corpus.json')
    bank = json.loads(fixture.read_text())
    repository = Path(__file__).resolve().parents[4]
    historical = repository / bank['source_path']
    source_check = None
    if historical.exists():
        source_check = hashlib.sha256(historical.read_bytes()).hexdigest() == bank['source_sha256']
        if not source_check:
            raise AssertionError('historical discovery-bank hash changed')
    records = []
    for case in bank['cases']:
        start = time.perf_counter()
        old = normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                      boundary_method='moments', annulus_method='counts')
        old_seconds = time.perf_counter() - start
        start = time.perf_counter()
        new = normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                      boundary_method='moments', annulus_method='signed_rank_two',
                                      record_certificate=True)
        new_seconds = time.perf_counter() - start
        assert old['status'] == case['expected_old_status'], case['id']
        assert old.get('reason') == case['expected_old_reason'], case['id']
        assert new['status'] == 'COMPLETE', case['id']
        assert new['census']['histogram'] == case['expected_histogram'], case['id']
        assert new['certificate']['schema'] == case['expected_certificate_schema']
        start = time.perf_counter()
        replayed = verify_normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                                  new['certificate'])
        replay_seconds = time.perf_counter() - start
        assert replayed, case['id']
        encoded = json.dumps(json_safe(new['certificate']), sort_keys=True,
                             separators=(',', ':')).encode()
        name = case['id'].replace('/', '__') + '.json'
        (certificates / name).write_text(json.dumps(json_safe(new['certificate']), indent=2) + '\n')
        record = dict(id=case['id'], source_record=case['source_record'],
                      source_standard_vertex_index=case['source_standard_vertex_index'],
                      tetrahedra=len(case['coordinates']),
                      normal_disks=sum(map(sum, case['coordinates'])),
                      old_status=old['status'], old_reason=old.get('reason'),
                      old_seconds=old_seconds, new_status=new['status'],
                      new_seconds=new_seconds, replayed=replayed,
                      replay_seconds=replay_seconds, census=new['census'],
                      signed_stats=new['stats']['signed_annuli'],
                      certificate_bytes=len(encoded),
                      certificate_sha256=hashlib.sha256(encoded).hexdigest(),
                      certificate_path='certificates/' + name)
        if use_regina:
            import regina
            from marked_parallelity_research.audit_census import oracle
            reference = oracle(case)
            assert reference['histogram'] == new['census']['histogram'], case['id']
            record['regina'] = dict(reference, version=regina.versionString())
        records.append(record)
    refusals = []
    for case in bank.get('refusals', []):
        result = normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                         boundary_method='moments', annulus_method='signed_rank_two')
        assert result['status'] == case['expected_new_status'], case['id']
        assert result.get('reason') == case['expected_new_reason'], case['id']
        refusals.append(dict(id=case['id'], status=result['status'], reason=result.get('reason')))
    report = dict(schema='signed-annulus-native-replay-v1',
                  source_revision=bank['source_revision'],
                  source_bank_hash_checked=source_check,
                  fixture_sha256=hashlib.sha256(fixture.read_bytes()).hexdigest(),
                  python=platform.python_version(), records=records, refusals=refusals)
    (output / 'native_replay.json').write_text(json.dumps(json_safe(report), indent=2) + '\n')
    print(json.dumps(dict(cases=len(records), independently_replayed=len(records),
                         retained_refusals=len(refusals),
                         regina_agreements=len(records) if use_regina else None)))
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True)
    parser.add_argument('--regina', action='store_true')
    args = parser.parse_args()
    run(args.output, args.regina)
