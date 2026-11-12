"""Replay the pinned source census and its explicit eligibility ledger offline."""
import csv
import hashlib
import io
import json
from pathlib import Path
import sys
from measure import measure

ROOT = Path(__file__).resolve().parent


def main():
    inventory = json.loads((ROOT / 'evidence/source_inventory.json').read_text())
    rows = []
    for item in inventory['sources']:
        data = (ROOT / item['local_path']).read_bytes()
        git_hash = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if git_hash != item['git_blob_sha']:
            raise ValueError('Git blob mismatch: ' + item['local_path'])
        rows.append({'git_blob_sha': git_hash, **measure(data),
                     'origins': item['origins'], 'local_path': item['local_path']})
    ledger = json.loads((ROOT / 'evidence/eligibility.json').read_text())
    classified = {r['git_blob_sha']: r for r in ledger['entries']}
    threshold = {'tokens': 248, 'ast_nodes': 270, 'normalized_bytes': 487}
    threshold_rows = [r for r in rows if any(r[k] <= v for k, v in threshold.items())]
    missing = [r['git_blob_sha'] for r in threshold_rows if r['git_blob_sha'] not in classified]
    if missing:
        raise ValueError('Unclassified source at or below an incumbent coordinate: ' + repr(missing))
    eligible = [r for r in threshold_rows if classified[r['git_blob_sha']]['eligible']]
    envelope = {key: min(r[key] for r in eligible) for key in threshold}
    if envelope != threshold:
        raise ValueError('Changed incumbent envelope: ' + repr(envelope))
    output = {'commit': inventory['commit'], 'python': sys.version,
              'artifact_python_paths': inventory['artifact_python_paths'],
              'artifact_unique_python_blobs': inventory['artifact_unique_python_blobs'],
              'incoming_archives': inventory['incoming_archives'],
              'incoming_python_members': inventory['incoming_python_members'],
              'unique_sources': len(rows), 'classified_threshold_sources': len(threshold_rows),
              'compact_coordinate_envelope': envelope,
              'minima_are_distinct_programs': True,
              'scope': inventory['scope'],
              'limits': ['An empirical source envelope, not a mathematical lower bound.',
                         'Classification establishes program role, not soundness of every historical checker.',
                         'Packed loaders, report builders, tests and import-only drivers are excluded from the direct standalone class.']}
    (ROOT / 'evidence/census_results.json').write_text(json.dumps(output, indent=2) + '\n')
    with (ROOT / 'evidence/source_metrics.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=['git_blob_sha', 'tokens', 'ast_nodes', 'normalized_bytes', 'normalized_sha256', 'source_sha256', 'local_path'])
        writer.writeheader()
        writer.writerows({k: r[k] for k in writer.fieldnames} for r in rows)
    print(json.dumps(output, indent=2))


if __name__ == '__main__':
    main()
