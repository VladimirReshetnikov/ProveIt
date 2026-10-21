#!/usr/bin/env python3
"""Static, read-only-source audit. Does not load or execute any incoming code."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parent
SRC = ROOT / 'sources'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_text())

pins = read(ROOT / 'SOURCE_PINS.json')
blobs = []
for x in pins:
    remote = x['path']
    if '/proposals/' in remote:
        rel = remote.split('/proposals/', 1)[1]
    elif '/rocq-extension/coq/215/' in remote:
        rel = 'production/rocq/' + remote.rsplit('/', 1)[1]
    else:
        rel = 'production/' + remote.rsplit('/', 1)[1]
    p = SRC / rel
    b = p.read_bytes()
    got = hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
    blobs.append({'file': rel, 'bytes': len(b), 'sha256': sha(p),
                  'git_blob': got, 'matches': got == x['git_blob_sha']})

norm = SRC / 'k215-simplification/source_normalization'
nr = read(norm / 'kernel_receipt.json')
normalized = []
for x in nr['modules']:
    p = norm / ('RMNormalizedBisim.lean' if x['module'] == 'RMNormalizedBisim'
                else 'normalized_lean/' + x['module'] + '.lean')
    normalized.append({'module': x['module'], 'bytes': p.stat().st_size,
                       'source_hash_matches': sha(p) == x['source_sha256'],
                       'recorded_exit_code': x['exit_code']})

plain = SRC / 'k215-simplification-2/plain_source'
pr = read(plain / 'result.json')
selected = {x['module']: x for x in pr['selected']}
plain_checks = []
for m, x in selected.items():
    p = plain / x['source']
    imports = re.findall(r'^import\s+(\S+)', p.read_text(), re.M)
    plain_checks.append({'module': m, 'source_hash_matches': sha(p) == x['source_sha256'],
                         'offset_imports': [i for i in imports if 'Offset' in i],
                         'unlisted_project_imports': [i for i in imports
                             if i.startswith('BusyBeaver.') and i not in selected]})

production = []
for x in nr['upstream_dependencies']:
    p = SRC / 'production' / (x['module'] + '.lean')
    production.append({'module': x['module'], 'recorded_sha256': x['source_sha256'],
                       'current_sha256': sha(p), 'identical': sha(p) == x['source_sha256']})

cm = SRC / 'k215-simplification-2/formal_cm215'
cr = read(cm / 'verification/compile-summary.json')
cm_checks = [{'source': x['source'], 'source_hash_matches': sha(cm / x['source']) == x['source_sha256']}
             for x in cr['modules'] if not x['source'].startswith('vendor/')]

coq = SRC / 'k215-simplification-2/coq'
qr = read(coq / 'verification/kernel-result.json')
coq_checks = [{'source': name, 'source_hash_matches': sha(coq / name) == digest}
              for name, digest in qr['source_sha256'].items() if (coq / name).exists()]

ordinary = SRC / 'zfc215-simplification/source_proof'
orr = read(ordinary / 'verification/result.json')
ordinary_checks = []
for x in orr['bindings']:
    p = ordinary / x['file']
    if not p.exists() and x['file'] in ['deps/K215F/Prog215.v', 'deps/K215F/DagPerm.v']:
        p = SRC / 'production/rocq' / Path(x['file']).name
    if p.exists():
        ordinary_checks.append({'source': x['file'], 'source_hash_matches': sha(p) == x['source_sha256']})

def declaration(text, name):
    m = re.search(r'^def ' + re.escape(name) + r'\b.*?(?=\n(?:def |theorem |private theorem |/--|/\-!|end )|\Z)', text, re.M | re.S)
    return re.sub(r'\s+', ' ', m[0]).strip() if m else None

current = (SRC / 'production/KSource215Data.lean').read_text()
replacement = (norm / 'normalized_lean/KSource215Programs.lean').read_text()
defs = {n: declaration(current, n) is not None and declaration(current, n) == declaration(replacement, n)
        for n in ['tH', 'tB', 'tC', 'p215Nodes', 'p215', 'pathDagPerm']}
summary = {
    'audit_type': 'Static source/receipt consistency, not a proof-assistant replay',
    'incoming_code_executed': False,
    'git_blob_count': len(blobs), 'git_blobs_all_match': all(x['matches'] for x in blobs),
    'normalized_local_count': len(normalized),
    'normalized_all_receipt_sources_match': all(x['source_hash_matches'] and x['recorded_exit_code'] == 0 for x in normalized),
    'normalized_local_source_bytes': sum(x['bytes'] for x in normalized),
    'normalized_recorded_30_module_source_bytes': sum(x['bytes'] for x in normalized) + sum((plain / ('BusyBeaver/ZFC/' + x['module'] + '.lean')).stat().st_size for x in nr['upstream_dependencies']),
    'plain_module_count': len(plain_checks),
    'plain_all_receipt_sources_match': all(x['source_hash_matches'] for x in plain_checks),
    'plain_import_closure_complete_and_no_offset_module': all(not x['offset_imports'] and not x['unlisted_project_imports'] for x in plain_checks),
    'plain_recorded_70_module_source_bytes': sum(x['source_bytes'] for x in selected.values()),
    'production_source_declarations_equal_ignoring_whitespace': defs,
    'current_production_dependency_differences': [x['module'] for x in production if not x['identical']],
    'cm215_checked_source_hashes_all_match': all(x['source_hash_matches'] for x in cm_checks),
    'coq_checked_source_hashes_all_match': all(x['source_hash_matches'] for x in coq_checks),
    'ordinary_coq_checked_source_hashes_all_match': all(x['source_hash_matches'] for x in ordinary_checks),
    'kernel_replay_performed': False,
}
result = {'summary': summary, 'git_blobs': blobs, 'normalized': normalized,
          'plain': plain_checks, 'production_dependencies': production,
          'cm215': cm_checks, 'coq': coq_checks, 'ordinary_coq': ordinary_checks}
(ROOT / 'STATIC_AUDIT.json').write_text(json.dumps(result, indent=2) + '\n')
assert summary['git_blobs_all_match']
assert summary['normalized_all_receipt_sources_match']
assert summary['plain_all_receipt_sources_match']
assert summary['plain_import_closure_complete_and_no_offset_module']
assert all(defs.values())
assert summary['current_production_dependency_differences'] == ['RMBisim']
assert summary['cm215_checked_source_hashes_all_match']
assert summary['coq_checked_source_hashes_all_match']
assert summary['ordinary_coq_checked_source_hashes_all_match']
print(json.dumps(summary, indent=2))
