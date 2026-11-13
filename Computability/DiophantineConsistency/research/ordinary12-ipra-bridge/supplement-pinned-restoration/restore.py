#!/usr/bin/env python3
"""Verify and restore only missing files pinned by the 95-row supplement.

Run ``python3 -I -B restore.py verify`` before ``... restore``. Verification
constructs a disposable copy and executes the supplement checker there.
The restore mode refuses any different manifest, source, target or receipt;
it never overwrites an existing destination.
"""
from pathlib import Path
import gzip
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
SUP = REPO / 'Computability/DiophantineConsistency/con-zfc-diophantine-forms/115-synchronized-exponents/supplement'
PARENT = REPO / 'Computability/DiophantineConsistency/candidates/free-j-polarized-positive/source/positive/coefficients'
OBS = HERE / 'observations'
MANIFEST_SHA = 'b6f7ecd9dc2a6317dce88e01985a1d167e4aef77c393ff8a53c363eece72956d'
CHILD_SHA = '2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22'
PARENT_SHA = '2a8da9ac141de5078fbdca96acccab5a7c44f6b39f4bc6063261b29179cb68be'
MISSING = (
    'coefficients/BINDING.json', 'coefficients/README.md', 'coefficients/SHA256.json',
    'coefficients/payloads/K.bin.gz', 'coefficients/payloads/MC.bin.gz',
    'coefficients/payloads/MF_source.bin.gz', 'coefficients/payloads/beta.bin.gz',
    'coefficients/recipe/COEFFICIENT_BINDING.json', 'coefficients/recipe/PROOF.md',
    'coefficients/recipe/SOURCE_PINS.json', 'coefficients/recipe/build_coefficients.py',
    'coefficients/recipe/k215_transitions.json', 'inherited_proofs/eleven_adaptive.md',
    'inherited_proofs/free_J.md', 'inherited_proofs/thirteen_ordinary.md',
    'inherited_proofs/twelve_ordinary.md',
    'parents/candidates/free-j-polarized-positive/source/positive/p13_free_J.json',
    'parents/candidates/positive11-adaptive-shears/positive11.json',
)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def need(ok, msg):
    if not ok:
        raise RuntimeError(msg)

def read_safe(p):
    need(p.is_file() and not p.is_symlink(), 'missing or symlinked file: ' + str(p))
    return p.read_bytes()

def state():
    manifest_bytes = read_safe(SUP / 'MANIFEST.json')
    need(sha(manifest_bytes) == MANIFEST_SHA, 'manifest pin changed')
    manifest = json.loads(manifest_bytes)['files']
    pin_bytes = read_safe(SUP / 'SOURCE_PINS.json')
    need(sha(pin_bytes) == manifest['SOURCE_PINS.json'], 'source-pin manifest changed')
    source_pins = json.loads(pin_bytes)
    need(source_pins['commit'] == '84e16e43092614bae262ca59651cb9d77e31a255', 'source snapshot changed')
    pin_map = {r['local_path']: REPO / r['repository_path'] for r in source_pins['sources']}
    missing = {p for p in manifest if not (SUP / p).exists()}
    need(missing == set(MISSING), 'missing-file set differs from the pinned observation')
    for rel, digest in manifest.items():
        p = SUP / rel
        if rel not in missing:
            need(sha(read_safe(p)) == digest, 'existing supplement mismatch: ' + rel)
    mapping = {}
    for rel in MISSING:
        src = PARENT / rel.removeprefix('coefficients/') if rel.startswith('coefficients/') else pin_map[rel]
        data = read_safe(src)
        need(sha(data) == manifest[rel], 'source/manifest mismatch: ' + rel)
        need(not os.path.lexists(SUP / rel), 'destination exists: ' + rel)
        mapping[rel] = {'source': str(src.relative_to(REPO)), 'sha256': sha(data), 'size': len(data)}
    child_raw = read_safe(SUP / 'circuits/positive12_95_degree70.json')
    parent_raw = read_safe(SUP / 'parents/candidates/free-j-polarized-positive/equation.json')
    need(sha(child_raw) == CHILD_SHA and sha(parent_raw) == PARENT_SHA, 'circuit pin mismatch')
    child, parent = json.loads(child_raw), json.loads(parent_raw)
    need(child['parent_sha256'] == PARENT_SHA, 'child parent pin mismatch')
    need(child['coefficient_binding'] == '../coefficients/BINDING.json', 'child binding path changed')
    need(child['fixed_numerals'] == parent['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF'], 'port order')
    need(child['witnesses'] == parent['witnesses'] and child['domain'] == parent['domain'] == 'strictly positive integers', 'domain')
    need(child['operations'] == 95 and parent['operations'] == 96, 'graph counts')
    binding = json.loads(read_safe(PARENT / 'BINDING.json'))
    need(list(binding['ports']) == ['beta', 'K0', 'MC', 'MF'], 'binding order')
    need([binding['ports'][p]['upstream_port'] for p in binding['ports']] == ['beta', 'K', 'MC', 'MF_source'], 'upstream mapping')
    need('already shifted' in binding['warning'], 'MF shift warning missing')
    payloads = {}
    for name, row in binding['ports'].items():
        compressed = read_safe(PARENT / row['file'])
        raw = gzip.decompress(compressed)
        value = int.from_bytes(raw, 'little')
        need(sha(compressed) == row['sha256_gzip'] and sha(raw) == row['sha256_raw'], 'payload hash: ' + name)
        need(len(raw) == row['raw_bytes'] == (value.bit_length() + 7) // 8 and value.bit_length() == row['bits'], 'payload encoding: ' + name)
        payloads[name] = {'gzip_sha256': sha(compressed), 'raw_sha256': sha(raw), 'bytes': len(raw), 'bits': value.bit_length()}
    return manifest, mapping, payloads

def copy_missing(mapping, destination):
    for rel, row in mapping.items():
        target = destination / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        # Refuse symlink directories as well as any pre-existing file.
        for directory in (target.parent, *target.parent.parents):
            if directory == destination.parent:
                break
            need(not directory.is_symlink(), 'symlink target directory: ' + str(directory))
        data = read_safe(REPO / row['source'])
        need(sha(data) == row['sha256'], 'source changed before copy: ' + rel)
        fd = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
        with os.fdopen(fd, 'wb') as out:
            out.write(data)
        need(sha(read_safe(target)) == row['sha256'], 'copy mismatch: ' + rel)

def verify():
    need(not OBS.exists(), 'observations already exist')
    manifest, mapping, payloads = state()
    OBS.mkdir(parents=True)
    with tempfile.TemporaryDirectory(prefix='supplement-manifest-verification-') as tmp:
        target = Path(tmp) / 'supplement'
        shutil.copytree(SUP, target, symlinks=True)
        copy_missing(mapping, target)
        for rel, digest in manifest.items():
            need(sha(read_safe(target / rel)) == digest, 'isolated manifest mismatch: ' + rel)
        commands = []
        for name, opts in [('normal', []), ('optimized', ['-O'])]:
            cmd = [sys.executable, '-I', '-B', *opts, str(target / 'check.py')]
            result = subprocess.run(cmd, capture_output=True, text=True, timeout=120)
            (OBS / (name + '.stdout')).write_text(result.stdout)
            (OBS / (name + '.stderr')).write_text(result.stderr)
            commands.append({'mode': name, 'command': cmd, 'exit': result.returncode})
            need(result.returncode == 0 and not result.stderr, 'isolated checker failed: ' + name)
            output = target / ('CHECK_OPTIMIZED.json' if opts else 'CHECK.json')
            need(sha(read_safe(output)) == manifest[output.name], 'generated checker receipt drift: ' + name)
        # Corrupt the MF payload in the disposable copy: checker must reject.
        mf = target / 'coefficients/payloads/MF_source.bin.gz'
        corrupted = bytearray(read_safe(mf)); corrupted[-1] ^= 1; mf.write_bytes(corrupted)
        result = subprocess.run([sys.executable, '-I', '-B', str(target / 'check.py')], capture_output=True, text=True, timeout=120)
        (OBS / 'tampered.stdout').write_text(result.stdout)
        (OBS / 'tampered.stderr').write_text(result.stderr)
        need(result.returncode != 0, 'tampered gzip was not rejected')
        commands.append({'mode': 'tampered', 'exit': result.returncode})
    # Verify every original input again after the isolated run.
    manifest_after, mapping_after, payloads_after = state()
    need(manifest_after == manifest and mapping_after == mapping and payloads_after == payloads, 'inputs changed during isolated run')
    receipt = {'scope': 'external pinned provenance and isolated checker, not Lean file semantics',
        'manifest_sha256': MANIFEST_SHA, 'source_pins_sha256': manifest['SOURCE_PINS.json'],
        'child_sha256': CHILD_SHA, 'parent_sha256': PARENT_SHA, 'mapping': mapping,
        'file_count': len(mapping), 'total_bytes': sum(r['size'] for r in mapping.values()),
        'ports': payloads, 'commands': commands, 'inputs_unchanged': True}
    (OBS / 'verify.json').write_text(json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': 'PASS', 'file_count': len(mapping), 'total_bytes': receipt['total_bytes'], 'checker_modes': commands}, sort_keys=True))

def restore():
    receipt = json.loads(read_safe(OBS / 'verify.json'))
    manifest, mapping, payloads = state()
    need(receipt['mapping'] == mapping and receipt['ports'] == payloads and receipt['manifest_sha256'] == MANIFEST_SHA and receipt['inputs_unchanged'], 'verification receipt mismatch')
    copy_missing(mapping, SUP)
    for rel, digest in manifest.items():
        need(sha(read_safe(SUP / rel)) == digest, 'restored manifest mismatch: ' + rel)
    result = {'status': 'PASS', 'files_restored': list(mapping), 'manifest_sha256': MANIFEST_SHA,
              'restored_count': len(mapping), 'total_bytes': sum(r['size'] for r in mapping.values()),
              'all_manifest_files_match': True}
    (OBS / 'restore.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, sort_keys=True))

if __name__ == '__main__':
    need(len(sys.argv) == 2 and sys.argv[1] in ('verify', 'restore'), 'usage: restore.py verify|restore')
    (verify if sys.argv[1] == 'verify' else restore)()
