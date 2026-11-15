#!/usr/bin/env python3
"""Offline late-snapshot reconciliation against the original frozen inventory."""
from pathlib import Path
import argparse
from collections import Counter
import csv
import hashlib
import json

HERE = Path(__file__).resolve().parent
COMPARISON = HERE.parent
INITIAL_PIN = '8d31445d858761a8f6150c2e5012adae8895e932'
LATEST_PIN = 'ef0839bf15d8b556bc1e1634e6ad310adbcd4fe3'
CHECKED_AT = '2026-11-15 01:05:04 UTC'


def read_json(path):
    return json.loads(path.read_text())


def tsv(path):
    with path.open(newline='') as f:
        return list(csv.DictReader(f, delimiter='\t'))


def set_digest(values):
    return hashlib.sha256(('\n'.join(sorted(values))+'\n').encode()).hexdigest()


def verify():
    identities = read_json(HERE/'source_identities.json')
    for item in identities:
        data = (HERE/item['path']).read_bytes()
        assert len(data) == item['bytes'], item['path']
        assert hashlib.sha256(data).hexdigest() == item['sha256'], item['path']
        assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest() == item['git_blob_sha'], item['path']
    initial = tsv(COMPARISON/'catalog/MACHINES.tsv')
    incoming = read_json(COMPARISON/'incoming_table_classes.json')
    latest = tsv(HERE/'MACHINES.tsv')
    frontier = read_json(COMPARISON/'frontier194_index.json')
    old_classes = {r['table_class'] for r in initial}
    incoming_classes = {r['table_class'] for r in incoming}
    original_union = old_classes | incoming_classes
    latest_classes = {r['table_class'] for r in latest}
    assert len(initial) == len(old_classes) == 705
    assert len(incoming_classes) == 389
    assert len(latest) == len(latest_classes) == len(original_union) == 747
    assert original_union == latest_classes
    original_frontier = {r['table_class'] for r in frontier if r['reachable'] == 194}
    latest_frontier = {r['table_class'] for r in latest if r['states'] == '194'}
    assert len(original_frontier) == len(latest_frontier) == 139
    assert original_frontier == latest_frontier
    assert {r['table_class'] for r in frontier} <= latest_classes
    with (COMPARISON/'late_snapshot_paths.csv').open(newline='') as f:
        placements = list(csv.DictReader(f))
    assert len(placements) == 6
    packet_names = {r['current_packet'] for r in placements}
    historical_files = tsv(COMPARISON/'catalog/MACHINE_FILES.tsv')
    latest_files = tsv(HERE/'MACHINE_FILES.tsv')
    def record(r):
        return (r['packet'],r['file'],r['sha256'])
    historical = Counter(map(record,historical_files))
    unchanged = Counter(record(r) for r in latest_files if r['packet'] not in packet_names)
    assert historical == unchanged
    occurrences = read_json(COMPARISON/'current_table_occurrences.json')
    direct = [r for r in occurrences if r['zip_depth'] == 0]
    assert len(direct) == 1439
    per_packet = []
    missing = []
    extra = []
    for p in placements:
        old = [r for r in direct if r['origin'].startswith(p['initial_archive']+'!')]
        new = [r for r in latest_files if r['packet'] == p['current_packet']]
        old_counter = Counter(r['byte_sha256'] for r in old)
        new_counter = Counter(r['sha256'] for r in new)
        for sha,count in (old_counter-new_counter).items():
            origins = [r for r in old if r['byte_sha256'] == sha]
            missing.append(dict(packet=p['current_packet'],byte_sha256=sha,count=count,original_occurrences=origins))
        for sha,count in (new_counter-old_counter).items():
            extra.append(dict(packet=p['current_packet'],byte_sha256=sha,count=count))
        per_packet.append(dict(packet=p['current_packet'],initial_direct_members=len(old),latest_catalog_members=len(new)))
    assert len(historical_files) == 13879
    assert len(latest_files) == 15317
    assert len(missing) == 1 and missing[0]['count'] == 1 and not extra
    assert missing[0]['byte_sha256'] == 'e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8'
    omitted = missing[0]['original_occurrences'][0]
    assert omitted['states'] == omitted['reachable'] == 196
    retained = next(r for r in latest if r['table_class'] == omitted['table'])
    assert retained['states'] == '196'
    return dict(
        result='PASS',initial_snapshot=INITIAL_PIN,late_snapshot=LATEST_PIN,
        checked_at_utc=CHECKED_AT,placement_commit='78080fb26db69fed2ee295332cfdc16eafae1c7d',
        source_identities='late_snapshot/source_identities.json',
        archive_path_mapping='late_snapshot_paths.csv',
        frontier_path_mapping='late_snapshot/frontier_current_paths.csv',
        all_class_comparison=dict(initial_filed=705,incoming_classes=389,incoming_new_classes=42,frozen_union=747,latest=747,exact_set_equality=True,missing=[],added=[],sorted_table_keys_sha256=set_digest(latest_classes)),
        frontier_comparison=dict(frozen_spanning_194=139,latest_spanning_194=139,exact_set_equality=True,missing=[],added=[],additional_disconnected_diagnostic=1,sorted_table_keys_sha256=set_digest(latest_frontier)),
        packet_count=93,
        member_record_comparison=dict(initial_filed_records=13879,initial_direct_incoming_records=1439,latest_records=15317,historical_records_unchanged=True,latest_six_packet_records=1438,per_packet=per_packet,missing_from_latest_member_ledger=missing,extra_in_latest_member_ledger=extra,missing_occurrence_class_retained=retained,explanation='The late member ledger omits one direct loop-packet occurrence of the already cataloged 196-state PA196 table. Its canonical table class remains present; this does not affect the 747-class union or the 139 spanning 194-state classes. The reason for omission is not inferred from this comparison.'),
        scope='Exact comparison of pinned catalog table-class keys and frozen census metadata. The original audit verifies the 140 concrete representative tables. This late check does not download and reclassify every newly filed table; it proves that the latest catalog presents exactly the same class set already covered by the original novelty audit. No original census or count is revised.'
    )


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Assertions must be enabled; do not use Python -O.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=COMPARISON/'late_snapshot_receipt.json')
    args = parser.parse_args()
    result = verify()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: 747 canonical classes, including exactly the same 139 spanning 194-state classes.')
    print('PASS: 13,879 historical member records unchanged; six filed packets contribute 1,438 records.')
    print('The one omitted incoming member occurrence is a 196-state table in a class still present.')
