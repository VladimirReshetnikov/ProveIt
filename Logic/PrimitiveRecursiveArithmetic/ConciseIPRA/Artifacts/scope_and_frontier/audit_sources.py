"""Remeasure the pinned inspected source corpus without executing its code."""
from pathlib import Path
import hashlib
import json
import platform
from measure import measure

ROOT = Path(__file__).resolve().parent
small = json.loads((ROOT / 'evidence/integrated_audit_rows.json').read_text())
large = json.loads((ROOT / 'evidence/large_exclusion_review.json').read_text())
errors = []
for row in small + large:
    sha = row['git_blob_sha']
    relative = 'reference/integrated_sources/' + sha + '.py'
    raw = (ROOT / relative).read_bytes()
    git_blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    measured = measure(relative)
    wanted_size = row['raw_bytes']
    if git_blob != sha or len(raw) != wanted_size:
        errors.append({'sha': sha, 'error': 'raw bytes or Git hash differ'})
    for field in ('significant_tokens', 'ast_nodes', 'normalized_bytes'):
        if measured[field] != row[field]:
            errors.append({'sha': sha, 'field': field,
                           'expected': row[field], 'actual': measured[field]})
    if row.get('sha256') and hashlib.sha256(raw).hexdigest() != row['sha256']:
        errors.append({'sha': sha, 'error': 'SHA-256 differs'})
summary = {
    'python': platform.python_version(),
    'small_sources_remeasured': len(small),
    'larger_sources_remeasured': len(large),
    'total': len(small) + len(large),
    'errors': errors,
    'source_programs_executed': False,
    'scope': 'Reproduces bytes and metrics; checker classifications are '
             'the explicit manual/static reviews in evidence.'
}
(ROOT / 'evidence/local_source_remeasurement.json').write_text(
    json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
if errors:
    raise SystemExit(1)
