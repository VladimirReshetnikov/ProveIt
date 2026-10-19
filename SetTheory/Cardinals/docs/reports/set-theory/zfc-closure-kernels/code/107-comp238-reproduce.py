#!/usr/bin/env python3
"""Portable replay of the 238-state composition and separate E713 frontend.

Quick mode checks exact construction, source identity, local blocks, startup,
and frontend serialization/algebra. Full mode also rederives both unbounded
instruction proofs. Nothing here invokes a Lean or Rocq kernel.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parent
VENDOR_SHA = 'fbbdf0f20f91a23d83d8d7cc8f0fae00981281a50035d993c3955fa81608479d'
CANONICAL_SHA = '909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08'
OLD_LABEL_SHA = '069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c'
SITES_SHA = '7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6'

def require(c, message):
    if not c:
        raise RuntimeError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_text())

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--full', action='store_true')
    p.add_argument('--output', type=Path, default=ROOT / 'replay')
    a = p.parse_args()
    require(__debug__ and not sys.flags.optimize, 'Run without -O, -OO, or optimized Python.')
    require(sys.version_info >= (3, 10), 'Python 3.10 or later is required.')
    out = a.output.resolve()
    require(out != ROOT and (ROOT not in out.parents or out.name.startswith('replay')),
            'Use a separate output directory, or a replay-prefixed directory under the package.')
    require(not out.exists(), 'Choose a new output directory; existing replay results are preserved.')
    out.mkdir(parents=True)
    (out / 'logs').mkdir()
    started = time.monotonic()
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    checks = []

    def run(label, script, *arguments):
        print('Checking', label, flush=True)
        t = time.monotonic()
        result = subprocess.run([sys.executable, '-B', str(script), *map(str, arguments)],
                                cwd=ROOT, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (out / 'logs' / (label + '.log')).write_text(result.stdout)
        require(result.returncode == 0, f'{label} failed; see {out / "logs" / (label + ".log")}')
        checks.append({'name': label, 'status': 'PASS', 'seconds': round(time.monotonic()-t, 3)})

    manifest = ROOT / 'SHA256SUMS'
    require(manifest.is_file(), 'Missing final manifest.')
    tracked = {}
    for line in manifest.read_text().splitlines():
        expected, name = line.split('  ', 1)
        path = ROOT / name
        require(path.is_file() and sha(path) == expected, 'Manifest mismatch: ' + name)
        if path.suffix in ('.py', '.tm', '.json', '.bits', '.zip'):
            tracked[path] = expected
    checks.append({'name': 'manifest', 'status': 'PASS',
                   'files': len(manifest.read_text().splitlines())})

    archive = ROOT / 'vendor/ZFC_239_State_Construction_2026-10-19.zip'
    require(sha(archive) == VENDOR_SHA, 'Wrong parent archive.')
    vendor = out / 'vendor'
    vendor.mkdir()
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            target = (vendor / info.filename).resolve()
            require(target.is_relative_to(vendor.resolve()), 'Unsafe archive path.')
            require(not stat.S_ISLNK(info.external_attr >> 16), 'Archive symlinks are not accepted.')
        z.extractall(vendor)
    parent = vendor / 'zfc239-research-20261019'
    require((parent / 'candidate239/zfc_boundary239_old.tm').read_bytes() ==
            (ROOT / 'inputs/boundary239_old.tm').read_bytes(), 'Wrong parent table copy.')
    require((parent / 'candidate239/sites_logical.json').read_bytes() ==
            (ROOT / 'machines/sites_logical.json').read_bytes(), 'Wrong source copy.')
    run('parent_source_and_local_proofs', parent / 'reproduce.py',
        '--record', out / 'parent_replay.json', '--keep-work', out / 'parent_replay_work')
    require(load(out / 'parent_replay.json')['status'] == 'PASS', 'Parent quick replay not proved.')

    run('literal_constructor', ROOT / 'build_machine.py', '--output', out / 'rebuilt')
    for name, expected in [('zfc238.tm', CANONICAL_SHA), ('zfc238_old.tm', OLD_LABEL_SHA),
                           ('sites_logical.json', SITES_SHA)]:
        require(sha(out / 'rebuilt' / name) == expected, 'Rebuilt digest differs: ' + name)
        require((out / 'rebuilt' / name).read_bytes() == (ROOT / 'machines' / name).read_bytes(),
                'Rebuilt bytes differ: ' + name)
    require(load(out / 'rebuilt/construction238.json')['working_states'] == 238, 'Wrong rebuilt states.')
    require(load(out / 'rebuilt/bootstrap238.json')['steps'] == 409835, 'Wrong rebuilt startup.')

    run('independent_local_and_blank', ROOT / 'verification/composition_check.py',
        '--old', ROOT / 'inputs/boundary239_old.tm',
        '--new', ROOT / 'machines/zfc238_old.tm',
        '--canonical', ROOT / 'machines/zfc238.tm',
        '--output', out / 'composition_check.json')
    local = load(out / 'composition_check.json')
    require(local['status'] == 'PASS_EXACT_COMPOSITION_LOCAL_AND_BLANK', 'Local proof not accepted.')
    require(local == load(ROOT / 'evidence/composition_check.json'), 'Local finite certificate differs.')

    run('equational_packets', ROOT / 'foundations/build_packet.py', '--out', out / 'packets')
    packet_names = [f'E{n}.{suffix}' for n in (946, 917, 745, 713)
                    for suffix in ('bits', 'json', 'equations')] + ['verification.json']
    for name in packet_names:
        require((out / 'packets' / name).read_bytes() ==
                (ROOT / 'foundations/generated' / name).read_bytes(),
                'Frontend packet differs: ' + name)
    require((out / 'packets/E946.bits').read_bytes() ==
            (ROOT / 'inputs/E946_original.bits').read_bytes(),
            'Reconstructed 946-bit baseline differs from inspected original.')
    original946 = load(ROOT / 'inputs/E946_original.json')
    rebuilt946 = load(out / 'packets/E946.json')
    for key in ('signature', 'equations', 'start', 'target'):
        require(original946[key] == rebuilt946[key], '946-bit baseline differs: ' + key)
    run('independent_equational_review', ROOT / 'foundations/review713.py',
        '--input-dir', out / 'packets', '--output', out / 'review713.json')
    require(load(out / 'review713.json')['complete_bits'] == 713, 'Wrong complete packet count.')
    require(load(out / 'review713.json') == load(ROOT / 'evidence/review713.json'),
            'Independent frontend review differs.')

    if a.full:
        run('direct_unbounded_238', ROOT / 'verification/check_literal_runtime.py',
            '--table', ROOT / 'machines/zfc238_old.tm',
            '--sites', ROOT / 'machines/sites_logical.json', '--states', 238,
            '--output', out / 'universal238.json')
        direct = load(out / 'universal238.json')
        require(direct['status'] == 'UNIVERSAL_MATHEMATICAL_PASS', 'Direct runtime proof not accepted.')
        require((direct['working_states'], direct['transition_rows'], direct['cases'],
                 direct['symbolic_steps'], direct['minimum_actual_steps']) ==
                (238, 476, 8386, 2255513, 13), 'Direct proof census differs.')
        require(len(direct['directly_used_rows']) == 476, 'Direct proof omits a transition row.')
        require(load(out / 'universal238_cases.json') == load(ROOT / 'evidence/universal238_cases.json'),
                'Direct affine per-case certificate differs.')

        run('unbounded_parent_context_guard', ROOT / 'verification/guard169/certify_guard169_A.py',
            '--table', ROOT / 'inputs/boundary239_old.tm',
            '--sites', ROOT / 'machines/sites_logical.json', '--output-dir', out / 'guard169')
        guard = load(out / 'guard169/guard169_universal.json')
        require(guard['status'] == 'PASS_UNIVERSAL_RUNTIME_AND_EXACT_BOOT_GUARD', 'Parent guard not proved.')
        require((guard['cases'], guard['symbolic_rules'], guard['all_runtime_rows'],
                 guard['next_one_guard_visits'], guard['minimum_certified_one_run_length_constant']) ==
                (8386, 2247513, 478, 32, 23), 'Parent guard census differs.')
        for name in ['guard169_cases.json', 'guard169_visits.json']:
            require(load(out / 'guard169' / name) == load(ROOT / 'evidence/guard169' / name),
                    'Parent guard finite certificate differs: ' + name)

    # Read-only proof inputs must still be the bytes checked at entry.
    for path, expected in tracked.items():
        require(sha(path) == expected, 'A proof input changed during replay: ' + str(path))
    summary = {
        'status': 'FULL_238_CERTIFICATE_REPLAY_PASS' if a.full else 'QUICK_238_CERTIFICATE_REPLAY_PASS',
        'full_unbounded_proofs_replayed': a.full, 'checks': checks,
        'canonical_machine_sha256': CANONICAL_SHA, 'working_states': 238,
        'seconds': round(time.monotonic()-started, 3),
        'proof_status': 'Ordinary mathematical proof and executable certificates, with explicitly inherited source/calculus/ZFC calibration; no Lean/Rocq endpoint is built.',
        'consistency_status': 'No unconditional consistency, nonhalting, or minimality claim.'
    }
    (out / 'replay_summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2), flush=True)

if __name__ == '__main__':
    main()
