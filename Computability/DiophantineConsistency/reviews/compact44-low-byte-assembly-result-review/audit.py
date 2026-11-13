#!/usr/bin/env python3
"""Inspect checked MC assembly source, twelve boundary receipts and providers."""
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
DC = HERE.parents[1]
ROOT = DC.parents[1]
BASE = DC / 'research/ordinary12-ipra-bridge'
ASSEMBLY = BASE / 'compact44-low-byte-assembly-attempt2'
ATTEMPT = ASSEMBLY / 'observations/attempt01'
MANIFEST = BASE / 'compact44-low-byte-assembly-attempt/observations/prepare-attempt01/manifest.json'
CHUNKS = BASE / 'compact44-low-byte-boundary-chunks'
FIX = BASE / 'compact44-low-byte-boundary01-fix'
EARLIER_REVIEW = DC / 'reviews/compact44-low-byte-assembly-source-review'
SUFFIXES = ('.olean.private.hash', '.olean.server.hash', '.olean.hash', '.olean.private',
            '.olean.server', '.olean', '.ir.hash', '.ir', '.ilean.hash', '.ilean')


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def record(path):
    path = Path(path)
    if not os.path.lexists(path):
        return None
    need(path.is_file(), ('dangling or nonfile path', str(path)))
    return {'sha256': digest(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}


def family(path):
    return next((str(path)[:-len(s)] for s in SUFFIXES if str(path).endswith(s)), None)


def providers_inventory(roots):
    return {str(p): record(p) for r in roots for p in r.rglob('*') if p.is_file() and family(p.name)}


source = ASSEMBLY / 'CompactLowByteAssembly.lean'
receipt = json.loads((ATTEMPT / 'terminal.json').read_text())
manifest = json.loads(MANIFEST.read_text())
log = (ATTEMPT / 'compile.log').read_text()
need(digest(source) == digest(ATTEMPT / 'source.lean') == receipt['source_sha256'] ==
     receipt['workspace_source_sha256_after'] == '67699cc0e1f832a20f48efd13ed9f535bbddcf2c6d1817edfe74577f5a9a4d05',
     'assembly source drift')
need(digest(MANIFEST) == receipt['manifest_sha256'] and receipt['exit_code'] == 0 and
     all(receipt[k] for k in ('guards_unchanged', 'selected_unchanged', 'providers_unchanged')) and
     digest(ATTEMPT / 'compile.log') == receipt['log_sha256'] and
     not (ATTEMPT / 'deps.stderr').read_bytes() and
     not any(x in log for x in ('error:', 'warning:', 'sorryAx')), 'bad assembly receipt or log')
for name in ('point', 'decode_bytes'):
    need(f"'CompactLowByteAssembly.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log,
         ('unexpected axiom report', name))
project = Path(manifest['project']); lib = project / 'lib'
need(receipt['object_sha256'] == digest(project / 'CompactLowByteAssembly.olean') ==
     '83bf7396f168ed2a4aa49e0e13ec43a7d265f951e26d7c894b66351002e9d098', 'assembly object drift')
need(all(record(path) == old for path, old in receipt['guards_before'].items()), 'assembly guard drift')

sources = source.read_text()
need('theorem decode_bytes : Nat.ofDigits 256 bytes = CompactSymbolicPorts.lowNat := by' in sources and
     'theorem point (j : ℕ) (hj : j < 73759)' in sources and
     'apply RadixWindowReconstruction.ofDigits_eq_of_windows 256 (by decide)' in sources and
     'exact all_windows' in sources, 'unexpected endpoint statement or reconstruction')
need('set_option maxHeartbeats 3000000' in sources and
     len(re.findall(r'rw \[byteAt,[^\n]*hpow\]', sources)) == 4, 'unexpected assembly retry')
for i in range(1, 13):
    need(f'import CompactLowByteBoundary{i:02d}' in sources and
         f'exact CompactLowByteBoundary{i:02d}.windows j h.1 h.2' in sources,
         ('missing boundary use', i))

roots = [Path(p) for p in manifest['roots']]
need(len(roots) == 28 and len(manifest['files']) == 606 and not manifest['suppressed_companions'] and
     manifest['unchanged'], 'unexpected selected provider manifest')
before = providers_inventory(roots)
need(before == manifest['providers_before'], 'provider inventory drift')
overlaps = {}; seen = {}
for root in roots:
    for p in root.rglob('*'):
        if not p.is_file() or family(p.name) is None:
            continue
        rel = p.relative_to(root).as_posix(); rec = before[str(p)]
        if rel in seen:
            need(seen[rel]['sha256'] == rec['sha256'], ('conflicting provider path', rel))
            overlaps[rel] = overlaps.get(rel, 1) + 1
        else:
            seen[rel] = rec
need(set(seen) == set(manifest['files']), 'selected manifest path mismatch')
actual = {p.relative_to(lib).as_posix(): record(p) for p in lib.rglob('*') if p.is_file()}
need(set(actual) == set(manifest['files']) and
     all(actual[k]['sha256'] == manifest['files'][k]['sha256'] and
         actual[k]['resolved'] == manifest['files'][k]['resolved'] for k in actual),
     'selected overlay mismatch')

recipe_dir = BASE / 'compact44-low-byte-complete-recipe'
recipe_obs = recipe_dir / 'observations/attempt01'
recipe_receipt = json.loads((recipe_obs / 'terminal.json').read_text())
need(recipe_receipt['exit_code'] == 0 and recipe_receipt['guards_unchanged'] and
     digest(recipe_dir / 'CompactLowByteRecipeData.lean') == digest(recipe_obs / 'source.lean') ==
     recipe_receipt['source_sha256'] == recipe_receipt['workspace_source_sha256_after'] and
     digest(recipe_obs / 'compile.log') == recipe_receipt['log_sha256'] and
     digest(Path(recipe_receipt['run']) / 'CompactLowByteRecipeData.olean') ==
     recipe_receipt['object_sha256'] == manifest['files']['CompactLowByteRecipeData.olean']['sha256'] and
     all(record(path) == old for path, old in recipe_receipt['guards_before'].items()),
     'closed recipe object/source receipt mismatch')

boundary_rows = []
for i in range(1, 13):
    module = f'CompactLowByteBoundary{i:02d}'
    obs = (FIX / 'observations/attempt02' if i == 1 else
           CHUNKS / 'observations' / f'{module}-attempt01')
    src = FIX / f'{module}.lean' if i == 1 else CHUNKS / f'{module}.lean'
    r = json.loads((obs / 'terminal.json').read_text())
    need(r['exit_code'] == 0 and r['guards_unchanged'] and r['generic_unchanged'] and
         digest(src) == digest(obs / 'source.lean') == r['source_sha256'] ==
         r['workspace_source_sha256_after'] and digest(obs / 'compile.log') == r['log_sha256'] and
         not (obs / 'deps.stderr').read_bytes(), ('boundary receipt mismatch', module))
    content = (obs / 'compile.log').read_text()
    need(not any(x in content for x in ('error:', 'warning:', 'sorryAx')) and
         f"'{module}.windows' depends on axioms:" in content, ('boundary log', module))
    obj = Path(r['run']) / f'{module}.olean'
    need(digest(obj) == r['object_sha256'] == manifest['files'][f'{module}.olean']['sha256'],
         ('boundary object mismatch', module))
    need(all(record(path) == old for path, old in r['guards_before'].items()),
         ('boundary direct guard drift', module))
    boundary_rows.append({'module': module, 'source_sha256': r['source_sha256'],
                          'object_sha256': r['object_sha256'], 'receipt_sha256': digest(obs / 'terminal.json')})

prior = subprocess.run([sys.executable, '-I', '-S', '-B', str(EARLIER_REVIEW / 'audit.py')],
                       cwd=ROOT, capture_output=True, text=True, timeout=120)
need(prior.returncode == 0 and not prior.stderr, ('earlier finite review failed', prior.stderr))
finite = json.loads(prior.stdout)
need(finite['total_indices'] == 73759 and finite['uncovered'] == finite['overlap'] == 0 and
     finite['boundary_indices'] == 142 and finite['recipe_matches_payload'] and
     finite['independent_defect_matches_payload'], 'finite review outcome changed')
actual_intervals = [[int(a), int(b)] for a, b in re.findall(
    r'\((\d+) ≤ j ∧ j < (\d+)\)', sources[sources.index('have hleft'):sources.index('rcases hleft')])]
need(actual_intervals == finite['boundary_intervals'], 'retry boundary intervals changed')
need(providers_inventory(roots) == before and
     all(record(path) == old for path, old in receipt['guards_before'].items()), 'guards changed during review')
print(json.dumps({'status': 'SOURCE_AND_ARTIFACT_REVIEW_PASS_NOT_A_REPLAY',
                  'assembly_source_sha256': digest(source), 'assembly_object_sha256': receipt['object_sha256'],
                  'assembly_receipt_sha256': digest(ATTEMPT / 'terminal.json'),
                  'manifest_sha256': digest(MANIFEST), 'provider_roots': len(roots),
                  'provider_files': len(before), 'selected_files': len(actual),
                  'overlapping_relative_paths': len(overlaps), 'boundary_receipts': boundary_rows,
                  'recipe_source_sha256': recipe_receipt['source_sha256'],
                  'recipe_object_sha256': recipe_receipt['object_sha256'],
                  'finite_review_sha256': digest(EARLIER_REVIEW / 'audit.py'),
                  'scope': 'single-author source/artifact and external finite review; no new Lean replay, '
                           'transitive/package/dynamic ancestry, filesystem byte theorem or PDF/iPRA proof'},
                 indent=2, sort_keys=True))
