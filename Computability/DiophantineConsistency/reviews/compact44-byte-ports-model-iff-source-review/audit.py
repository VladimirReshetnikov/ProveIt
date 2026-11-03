#!/usr/bin/env python3
"""Inspect the byte-port/model join and its guarded selected-provider union."""
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import sys

if not __debug__ or not sys.flags.isolated or not sys.flags.no_site:
    raise RuntimeError('invoke python3 -I -S -B without optimization')
HERE = Path(__file__).resolve().parent
DC = HERE.parents[1]
ROOT = DC.parents[1]
BASE = DC / 'research/ordinary12-ipra-bridge'
JOIN = BASE / 'compact44-byte-ports-model-iff-prototype'
PREP = JOIN / 'observations/prepare-attempt01/manifest.json'
ATTEMPT = JOIN / 'observations/attempt03'
BYTE = BASE / 'compact44-four-port-byte-assembly2'
MODEL = BASE / 'free-j-retained-shift-model-prototype'
SUFFIXES = ('.olean.private.hash', '.olean.server.hash', '.olean.hash', '.olean.private',
            '.olean.server', '.olean', '.ir.hash', '.ir', '.ilean.hash', '.ilean')


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()


def record(path):
    path = Path(path)
    if not os.path.lexists(path): return None
    need(path.is_file(), ('dangling or nonfile path', str(path)))
    return {'sha256': digest(path), 'resolved': str(path.resolve(strict=True)),
            'link': os.readlink(path) if path.is_symlink() else None}


def family(path):
    return next((str(path)[:-len(s)] for s in SUFFIXES if str(path).endswith(s)), None)


def inventory(roots):
    return {str(p): record(p) for root in roots for p in root.rglob('*') if p.is_file()}


manifest = json.loads(PREP.read_text())
need(manifest['unchanged'] and not manifest['suppressed_companions'], 'join preflight incomplete')
byte_manifest_path = Path(manifest['byte_manifest_path']); byte_terminal_path = Path(manifest['byte_receipt_path'])
model_terminal_path = Path(manifest['model_receipt_path'])
need(digest(byte_manifest_path) == manifest['byte_manifest_sha256'] and
     digest(byte_terminal_path) == manifest['byte_receipt_sha256'] and
     digest(model_terminal_path) == manifest['model_receipt_sha256'], 'predecessor receipt/manifest drift')
bm = json.loads(byte_manifest_path.read_text()); bt = json.loads(byte_terminal_path.read_text())
mt = json.loads(model_terminal_path.read_text())
need(bt['exit_code'] == mt['exit_code'] == 0 and
     all(bt[k] for k in ('guards_unchanged', 'selected_unchanged', 'producers_unchanged')) and
     all(mt[k] for k in ('dependencies_unchanged', 'providers_unchanged', 'source_unchanged')),
     'predecessor build did not pass its scoped checks')
need(all(record(p) == v for p, v in manifest['byte_guards'].items()) and
     all(record(p) == v for p, v in manifest['model_guards'].items()) and
     manifest['byte_guards'] == bt['guards_before'] and
     manifest['model_guards'] == mt['dependencies_before'], 'predecessor direct guard drift')
byte_src = BYTE / 'CompactFourPortByteAssembly2.lean'
model_src = MODEL / 'FreeJRetainedShiftModel.lean'
need(digest(byte_src) == bt['source_sha256'] and digest(model_src) == mt['source_sha256'],
     'predecessor source drift')
byte_log = (BYTE / 'observations/attempt01/compile.log').read_text()
model_log = (MODEL / 'observations/attempt01/compile.log').read_text()
need(digest(BYTE / 'observations/attempt01/compile.log') == bt['log_sha256'] and
     not any(x in byte_log or x in model_log for x in ('error:', 'warning:', 'sorryAx')) and
     "'CompactFourPortByteAssembly2.decode_ports' depends on axioms:" in byte_log and
     "'FreeJRetainedShiftModel.shifted_model_iff' depends on axioms:" in model_log,
     'predecessor compiler log mismatch')
byte_project = Path(bm['project']); byte_lib = byte_project / 'lib'
byte_live = {p.relative_to(byte_lib).as_posix(): record(p) for p in byte_lib.rglob('*') if p.is_file()}
need(set(byte_live) == set(bm['files']) and
     all(byte_live[k]['sha256'] == bm['files'][k]['sha256'] and
         byte_live[k]['resolved'] == bm['files'][k]['resolved'] for k in byte_live),
     'byte predecessor selected union drift')
for name, prior in bm['prior_manifests'].items():
    need(digest(prior['path']) == prior['sha256'] and
         all(record(p) == v for p, v in prior['providers_before'].items()), ('byte prior drift', name))

roots = [Path(p) for p in manifest['model_roots']]
before = inventory(roots)
need(before == manifest['model_before'], 'model provider inventory drift')
seen = {}; owners = {}; conflicts = []; suppressed = []; overlap_count = 0


def add(relative, path, owner):
    global overlap_count
    fam = family(relative)
    if fam is None: return
    current = record(path)
    need(current is not None, ('missing selected input', relative))
    if relative in seen:
        overlap_count += 1
        if seen[relative]['sha256'] != current['sha256']:
            conflicts.append(relative)
    if fam not in owners: owners[fam] = owner
    if owners[fam] != owner and relative not in seen: suppressed.append((owner, relative))
    elif owners[fam] == owner: seen.setdefault(relative, current)


for relative in bm['files']:
    add(relative, byte_lib / relative, 'byte-union')
for root in roots:
    for path in root.rglob('*'):
        if path.is_file(): add(path.relative_to(root).as_posix(), path, str(root))
for root, module, terminal in [(byte_project, 'CompactFourPortByteAssembly2', bt),
                               (Path(mt['run']), 'FreeJRetainedShiftModel', mt)]:
    path = root / f'{module}.olean'
    need(digest(path) == terminal['object_sha256'], ('predecessor object drift', module))
    add(module + '.olean', path, str(root))
need(not conflicts and not suppressed and overlap_count == manifest['overlap_count'] and
     set(seen) == set(manifest['files']), 'join overlay conflicts, suppression or coverage changed')
project = Path(manifest['project']); lib = project / 'lib'
actual = {p.relative_to(lib).as_posix(): record(p) for p in lib.rglob('*') if p.is_file()}
need(set(actual) == set(manifest['files']) and
     all(actual[k]['sha256'] == manifest['files'][k]['sha256'] and
         actual[k]['resolved'] == manifest['files'][k]['resolved'] for k in actual),
     'join selected overlay drift')

source = (JOIN / 'CompactBytePortsModelIff.lean').read_text()
ports = byte_src.read_text()
fixed = (BASE / 'compact44-symbolic-model-iff-prototype/CompactSymbolicModelIff.lean').read_text()
shift = model_src.read_text()
syntax = (DC / 'Lean/DiophantineConsistency/AdaptiveEquationSyntax2011.lean').read_text()
expected = ('![RetainedBetaBytes.betaBytes, CompactKernelByteRecipe.bytes, '
            'CompactLowByteRecipeData.bytes, CompactShiftedHighByteWindow.bytes]')
need(expected in ' '.join(ports.split()) and
     '![CompactFixedBeta.betaNat, paramKernel rho, lowNat, CompactFixedBeta.betaNat + highNat]' in ports,
     'byte port order or one-beta shift mismatch')
need('def p : Fin 4 → ℤ := fun j => (ports CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat j:ℤ)' in fixed and
     'def byteP : Fin 4 → ℤ := fun j => ((Nat.ofDigits 256 (bytePorts j) : ℕ) : ℤ)' in source and
     'congrArg (fun n : ℕ => (n : ℤ)) (congrFun decode_ports j)' in source,
     'byte/int cast or symbolic tuple mismatch')
need('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in source and
     '(∃ x : Fin 12 → V, InternalZero (positiveShift (retainedExpression byteP)) x)' in source and
     '(∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0)' in source and
     'rw [byteP_eq]' in source and 'exact FreeJRetainedShiftModel.shifted_model_iff' in source,
     'unexpected theorem statement or use of predecessor')
need('e.subst (fun i => Expr.var i + Expr.constant 1)' in syntax and
     'InternalZero (positiveShift e) v ↔ InternalZero e (fun i => v i + 1)' in syntax and
     'retainedExpression p' in shift and 'CompactSymbolicModelUnconditionalIff.model_iff' in shift,
     'positive shift or model equivalence mismatch')

receipt = json.loads((ATTEMPT / 'terminal.json').read_text())
log = (ATTEMPT / 'compile.log').read_text()
src_path = JOIN / 'CompactBytePortsModelIff.lean'
need(receipt['exit_code'] == 0 and digest(src_path) == digest(ATTEMPT / 'source.lean') ==
     receipt['source_sha256'] and digest(ATTEMPT / 'compile.log') == receipt['log_sha256'] and
     digest(PREP) == receipt['manifest_sha256'] and
     all(receipt[k] for k in ('guards_unchanged', 'selected_unchanged', 'providers_unchanged')) and
     not any(x in log for x in ('error:', 'warning:', 'sorryAx')),
     'join build receipt/log mismatch')
need(digest(project / 'CompactBytePortsModelIff.olean') == receipt['object_sha256'] and
     all(record(p) == v for p, v in receipt['guards_before'].items()), 'join output/direct guard drift')
for name in ('byteP_eq', 'shifted_model_iff'):
    need(f"'CompactBytePortsModelIff.{name}' depends on axioms: [propext, Classical.choice, Quot.sound]" in log,
         ('join axiom report mismatch', name))
byte_after = {p.relative_to(byte_lib).as_posix(): record(p) for p in byte_lib.rglob('*') if p.is_file()}
need(inventory(roots) == before and byte_after == byte_live and
     all(record(p) == v for p, v in receipt['guards_before'].items()) and
     all(record(p) == v for p, v in manifest['byte_guards'].items()) and
     all(record(p) == v for p, v in manifest['model_guards'].items()) and
     all(digest(prior['path']) == prior['sha256'] and
         all(record(p) == v for p, v in prior['providers_before'].items())
         for prior in bm['prior_manifests'].values()), 'inputs changed during audit')
print(json.dumps({'status': 'SOURCE_AND_ARTIFACT_REVIEW_PASS_NOT_A_REPLAY',
                  'source_sha256': digest(src_path), 'object_sha256': receipt['object_sha256'],
                  'receipt_sha256': digest(ATTEMPT / 'terminal.json'), 'manifest_sha256': digest(PREP),
                  'predecessor_sources': {'byte_tuple': digest(byte_src), 'retained_model': digest(model_src)},
                  'selected_files': len(actual), 'model_provider_roots': len(roots),
                  'model_provider_files': len(before), 'overlap_count': overlap_count,
                  'suppressed_companions': len(suppressed),
                  'scope': 'source and sampled artifact review; no fresh Lean replay, file/gzip/PDF '
                           'transcription theorem, full inherited ancestry or iPRA derivability claim'},
                 indent=2, sort_keys=True))
