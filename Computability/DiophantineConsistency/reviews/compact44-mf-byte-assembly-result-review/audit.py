#!/usr/bin/env python3
"""Read-only source, object-receipt and external-data audit of MF assembly."""
import gzip
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
PACKET = BASE / 'compact44-mf-byte-assembly-prototype'
OBS = PACKET / 'observations/attempt01'
MANIFEST = PACKET / 'observations/prepare-attempt01/manifest.json'
PAYLOAD = DC / 'candidates/free-j-polarized-positive/source/positive/coefficients/payloads/MF_source.bin.gz'
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


def inventory(roots):
    return {str(p): record(p) for r in roots for p in r.rglob('*') if p.is_file() and family(p.name)}


src = PACKET / 'CompactShiftedHighByteAssembly.lean'
receipt = json.loads((OBS / 'terminal.json').read_text())
manifest = json.loads(MANIFEST.read_text()); project = Path(manifest['project']); lib = project / 'lib'
log = (OBS / 'compile.log').read_text()
need(digest(src) == digest(OBS / 'source.lean') == receipt['source_sha256'] ==
     receipt['workspace_source_sha256_after'] == '420ac9903e344d5952a22433003e7b5623514e52c042e017eb924e2f9f8390c2',
     'assembly source drift')
need(receipt['exit_code'] == 0 and all(receipt[k] for k in
     ('guards_unchanged', 'selected_unchanged', 'providers_unchanged')) and
     digest(MANIFEST) == receipt['manifest_sha256'] and digest(OBS / 'compile.log') == receipt['log_sha256'] and
     not (OBS / 'deps.stderr').read_bytes() and
     not any(x in log for x in ('error:', 'warning:', 'sorryAx')) and
     "'CompactShiftedHighByteAssembly.decode_bytes' depends on axioms: [propext, Classical.choice, Quot.sound]" in log,
     'assembly receipt/log mismatch')
need(digest(project / 'CompactShiftedHighByteAssembly.olean') == receipt['object_sha256'] ==
     '992dd20b27f39d9fda165349221ca1e93ed36789816d48d17555bea74efec77e', 'assembly object drift')
need(all(record(p) == v for p, v in receipt['guards_before'].items()), 'assembly direct guards drift')
source = src.read_text()
need(re.search(r'theorem decode_bytes\s*:\s*Nat\.ofDigits 256 bytes =\s*'
               r'CompactFixedBeta\.betaNat \+ CompactSymbolicPorts\.highNat := by', source) and
     'exact CompactShiftedHighBound.shifted_lt_byte_power' in source and 'exact bytes_windows' in source,
     'unexpected assembly statement')
need(set(p.name for p in map(Path, (OBS / 'deps').read_text().splitlines())) ==
     {'Init.olean', 'CompactShiftedHighByteWindow.olean', 'CompactShiftedHighBound.olean',
      'RadixWindowReconstruction.olean'}, 'unexpected direct assembly imports')

roots = [Path(p) for p in manifest['roots']]
need(len(roots) == 12 and len(manifest['files']) == 590 and not manifest['suppressed_companions'] and
     manifest['unchanged'], 'unexpected selected manifest')
before = inventory(roots)
need(before == manifest['providers_before'], 'provider inventory drift')
seen = {}; overlaps = set()
for root in roots:
    for p in root.rglob('*'):
        if not p.is_file() or family(p.name) is None: continue
        rel = p.relative_to(root).as_posix(); current = before[str(p)]
        if rel in seen:
            need(seen[rel]['sha256'] == current['sha256'], ('conflicting provider path', rel))
            overlaps.add(rel)
        else: seen[rel] = current
actual = {p.relative_to(lib).as_posix(): record(p) for p in lib.rglob('*') if p.is_file()}
need(set(seen) == set(actual) == set(manifest['files']) and
     all(actual[k]['sha256'] == manifest['files'][k]['sha256'] and
         actual[k]['resolved'] == manifest['files'][k]['resolved'] for k in actual), 'overlay mismatch')

inputs = [('compact44-mf-byte-window-prototype', 'attempt02', 'CompactShiftedHighByteWindow'),
          ('compact44-mf-byte-bound-prototype', 'attempt02', 'CompactShiftedHighBound'),
          ('compact44-retained-mf-digit-prototype', 'attempt03', 'CompactShiftedHighDigits'),
          ('generic-radix-shifted-digits-prototype', 'attempt02', 'RadixShiftedDigits'),
          ('generic-radix-window-reconstruction-prototype', 'attempt01', 'RadixWindowReconstruction')]
rows = []
for directory, attempt, module in inputs:
    root = BASE / directory; obs = root / 'observations' / attempt
    r = json.loads((obs / 'terminal.json').read_text()); item = root / f'{module}.lean'
    need(r['exit_code'] == 0 and r['guards_unchanged'] and r.get('generic_unchanged', True) and
         digest(item) == digest(obs / 'source.lean') == r['source_sha256'] == r['workspace_source_sha256_after'] and
         digest(obs / 'compile.log') == r['log_sha256'] and
         digest(Path(r['run']) / f'{module}.olean') == r['object_sha256'] == manifest['files'][f'{module}.olean']['sha256'] and
         all(record(p) == v for p, v in r['guards_before'].items()), ('dependency receipt', module))
    messages = (obs / 'compile.log').read_text()
    need(not any(x in messages for x in ('error:', 'warning:', 'sorryAx')), ('dependency log', module))
    rows.append({'module': module, 'source_sha256': r['source_sha256'], 'object_sha256': r['object_sha256'],
                 'receipt_sha256': digest(obs / 'terminal.json')})

digits_source = (BASE / 'compact44-retained-mf-digit-prototype/CompactShiftedHighDigits.lean').read_text()
window_source = (BASE / 'compact44-mf-byte-window-prototype/CompactShiftedHighByteWindow.lean').read_text()
bound_source = (BASE / 'compact44-mf-byte-bound-prototype/CompactShiftedHighBound.lean').read_text()
beta_path = BASE / 'compact44-fixed-beta-bounds-prototype/CompactFixedBeta.lean'
ports_path = BASE / 'compact44-symbolic-ports-prototype/CompactSymbolicPorts.lean'
generic_window_path = BASE / 'compact44-symbolic-k-byte-window-exploration/ByteWindow.lean'
extra_sources = {p: digest(p) for p in (beta_path, ports_path, generic_window_path)}
need('def betaNat : ℕ := 2^(67*8807)-1' in beta_path.read_text() and
     'def highNat : ℕ := Nat.ofDigits (2^67) CompactHighPopulation.highDigits' in ports_path.read_text(),
     'fixed symbolic port definitions mismatch')
need('def shiftedDigits : List ℕ := (3 :: highDigits.tail) ++ [1]' in digits_source and
     'CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat =' in digits_source and
     'shifted_value_generic (2^67)' in digits_source, 'once-shifted digit construction mismatch')
need('rw [← shifted_value] at h' in window_source and 'have h := ByteWindow.byte shiftedDigits shifted_digits_bounded j' in window_source and
     'def bytes : List ℕ := (List.range 73759).map byteAt' in window_source, 'window mismatch')
need('theorem byte (L : List ℕ) (hL : ∀ x ∈ L, x < 2^67) (j : ℕ)' in generic_window_path.read_text() and
     '(Nat.ofDigits (2^67) L / 2^(8*j)) % 256' in generic_window_path.read_text(),
     'generic byte window statement mismatch')
need('CompactFixedBeta.betaNat + CompactSymbolicPorts.highNat < 256^73759' in bound_source and
     '(2:ℕ)*(2^67)^8807 < 256^73759' in bound_source, 'bound mismatch')

# Independently parse the displayed high-digit Lean list (rather than running
# the author's Python recipe transcription), then evaluate a single beta shift.
high_path = BASE / 'compact44-high-population-prototype/CompactHighPopulation.lean'
high_src = high_path.read_text(); prior_high_hash = digest(high_path)
values = {'mu': 2**51-2, 'padding': 2**65-1, 'lastPadding': 2**19-1}
for name, formula in [('mu', '2^51-2'), ('padding', '2^65-1'), ('lastPadding', '2^19-1')]:
    need(f'def {name} : ℕ := {formula}' in high_src, ('high alias', name))
expression = high_src.split('def highDigits : List ℕ :=', 1)[1].split('\ntheorem digits_length', 1)[0]
digits = []
for part in expression.split('++'):
    part = part.strip()
    m = re.fullmatch(r'List\.replicate\s+(\d+)\s+(\w+)', part)
    if m:
        token = m.group(2); val = int(token) if token.isdigit() else values[token]
        digits.extend([val] * int(m.group(1))); continue
    m = re.fullmatch(r'\[([^]]*)\]', part)
    need(m is not None, ('unparsed high-digit source part', part))
    for token in m.group(1).split(','):
        token = token.strip(); digits.append(int(token) if token.isdigit() else values[token])
need(len(digits) == 8807 and digits[0] == 4 and all(0 <= d < 2**67 for d in digits), 'high digits')
high_value = sum(d << (67*i) for i, d in enumerate(digits))
beta = (1 << (67*8807)) - 1
shifted = [3] + digits[1:] + [1]
shifted_value = sum(d << (67*i) for i, d in enumerate(shifted))
need(beta + high_value == shifted_value and beta + high_value < 256**73759, 'shift/bound arithmetic')
raw = gzip.decompress(PAYLOAD.read_bytes()); payload_hash = digest(PAYLOAD)
need(len(raw) == 73759 and sha256(raw).hexdigest() ==
     '48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737' and
     shifted_value.to_bytes(73759, 'little') == raw, 'retained MF raw bytes mismatch')
checker = PACKET / 'check_recipe.py'
check = subprocess.run([sys.executable, '-I', '-B', str(checker)], cwd=ROOT,
                       capture_output=True, text=True, timeout=120)
need(check.returncode == 0 and not check.stderr and json.loads(check.stdout)['all_recipe_bytes_match'],
     'author external checker failed')
need(digest(high_path) == prior_high_hash and digest(PAYLOAD) == payload_hash and
     all(digest(p) == h for p, h in extra_sources.items()) and inventory(roots) == before and
     all(record(p) == v for p, v in receipt['guards_before'].items()), 'inputs changed during review')
print(json.dumps({'status': 'SOURCE_AND_ARTIFACT_REVIEW_PASS_NOT_A_REPLAY',
                  'assembly_source_sha256': digest(src), 'assembly_object_sha256': receipt['object_sha256'],
                  'manifest_sha256': digest(MANIFEST), 'provider_roots': len(roots),
                  'provider_files': len(before), 'selected_files': len(actual),
                  'overlapping_relative_paths': len(overlaps), 'dependency_receipts': rows,
                  'high_digits_count': len(digits), 'shifted_digits_count': len(shifted),
                  'extra_source_hashes': {str(p.relative_to(ROOT)): h for p, h in extra_sources.items()},
                  'retained_raw_sha256': sha256(raw).hexdigest(), 'independent_one_beta_shift_matches': True,
                  'scope': 'source/artifact and external finite review; no new Lean replay or proof of '
                           'filesystem/gzip/PDF bytes, external data transcription, or iPRA endpoint'},
                 indent=2, sort_keys=True))
