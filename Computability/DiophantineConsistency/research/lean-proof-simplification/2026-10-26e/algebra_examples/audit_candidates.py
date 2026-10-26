#!/usr/bin/env python3
"""Read-only source audit for the nine proof-only simplification candidates.

Usage:
  python3 audit_candidates.py --repo /path/to/ProveIt
  python3 audit_candidates.py --baseline /path/to/baseline

A baseline root contains Computability/DiophantineConsistency/Lean/...
The program reads candidate evidence, source files and patches, runs the
non-mutating `git apply --check`, and prints JSON to stdout. It never rewrites
candidate manifests, measurements, source files, or recorded audit evidence.
This is not a Lean compiler invocation.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import subprocess
import sys

PIN = '60e9c5d620c6c387d932876cfa2d9376f64ea56c'
REL = Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency')
HERE = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
group = parser.add_mutually_exclusive_group(required=True)
group.add_argument('--repo', type=Path, help='Root of an existing ProveIt checkout')
group.add_argument('--baseline', type=Path, help='Root of the bundled selected-file baseline')
parser.add_argument('--candidates', type=Path, default=HERE / 'candidates.json')
parser.add_argument('--patch-dir', type=Path, default=HERE)
args = parser.parse_args()
root = (args.repo or args.baseline).resolve()
candidates = json.loads(args.candidates.read_text())
errors = []
rows = []
by_module = {}
for candidate in candidates:
    module = candidate['module']
    before, after = candidate['before'], candidate['after']
    label = module + '.' + candidate['theorem']
    source_path = root / REL / (module + '.lean')
    try:
        source_bytes = source_path.read_bytes()
        source = source_bytes.decode()
    except OSError as ex:
        errors.append(label + ': ' + str(ex))
        continue
    unchanged_header = before.split(':= by', 1)[0] == after.split(':= by', 1)[0]
    exact_source = source.count(before) == 1
    matching_hash = hashlib.sha256(source_bytes).hexdigest() == candidate['source_sha256']
    trust_tokens_absent = not re.search(r'\b(sorry|admit|axiom|unsafe)\b', after)
    row = {'theorem': label, 'unchanged_header': unchanged_header,
           'exact_before_text_present_once': exact_source,
           'source_hash_matches_recorded_baseline': matching_hash,
           'replacement_has_no_placeholder_or_new_axiom_tokens': trust_tokens_absent}
    for mode, text in [('before', before), ('after', after)]:
        body = text.split(':= by', 1)[1]
        row[mode + '_proof_nonblank_lines'] = sum(bool(line.strip()) for line in body.splitlines())
        row[mode + '_proof_characters'] = len(body)
        for suffix in ['_proof_nonblank_lines', '_proof_characters']:
            if row[mode + suffix] != candidate[mode + suffix]:
                errors.append(label + ': metric mismatch for ' + mode + suffix)
    for key in ['unchanged_header', 'exact_before_text_present_once',
                'source_hash_matches_recorded_baseline',
                'replacement_has_no_placeholder_or_new_axiom_tokens']:
        if not row[key]:
            errors.append(label + ': ' + key + ' failed')
    rows.append(row)
    by_module.setdefault(module, []).append(candidate)

patch_checks = []
for module in sorted(by_module):
    patch = args.patch_dir.resolve() / (module + '.patch')
    try:
        source = (root / REL / (module + '.lean')).read_text()
        modified = source
        for candidate in by_module[module]:
            modified = modified.replace(candidate['before'], candidate['after'])
        relative_name = (REL / (module + '.lean')).as_posix()
        expected_patch = ''.join(difflib.unified_diff(
            source.splitlines(True), modified.splitlines(True),
            fromfile='a/' + relative_name, tofile='b/' + relative_name))
        if patch.read_text() != expected_patch:
            errors.append(patch.name + ': patch differs from the manifest proof-only replacements')
        result = subprocess.run(['git', 'apply', '--check', str(patch)], cwd=root,
                                text=True, capture_output=True, check=False)
        patch_checks.append({'patch': patch.name, 'exit_code': result.returncode,
                             'stdout': result.stdout, 'stderr': result.stderr})
        if result.returncode:
            errors.append(patch.name + ': git apply --check failed')
    except OSError as ex:
        patch_checks.append({'patch': patch.name, 'status': 'not_run', 'error': str(ex)})
        errors.append(patch.name + ': patch check could not run')

head = None
if args.repo is not None and (root / '.git').exists():
    result = subprocess.run(['git', 'rev-parse', 'HEAD'], cwd=root,
                            text=True, capture_output=True, check=False)
    if result.returncode == 0:
        head = result.stdout.strip()
        if head != PIN:
            errors.append('Checkout HEAD differs from the recorded source pin')

report = {
    'audit_kind': 'read_only_static_source_and_patch_check',
    'source_pin': PIN,
    'checkout_head': head,
    'theorems': len(candidates),
    'proof_nonblank_lines_before': sum(r['before_proof_nonblank_lines'] for r in rows),
    'proof_nonblank_lines_after': sum(r['after_proof_nonblank_lines'] for r in rows),
    'proof_characters_before': sum(r['before_proof_characters'] for r in rows),
    'proof_characters_after': sum(r['after_proof_characters'] for r in rows),
    'compiler_invoked': False,
    'caveat': 'Static source and patch-application checks do not establish Lean elaboration, kernel acceptance, unchanged axiom dependencies, or full-project integration.',
    'candidate_checks': rows,
    'patch_checks': patch_checks,
    'errors': errors,
    'passed': not errors,
}
print(json.dumps(report, ensure_ascii=False, indent=2))
sys.exit(1 if errors else 0)
