#!/usr/bin/env python3
"""Replay only the fully reviewed Round14 direct closure in private copies."""
import argparse
from hashlib import sha256
import io
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tempfile
import time
import zipfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
ARCHIVE = 'ConZFC_Powered_Saturation_Factorial_Carriers_Round14_2026-10-24.zip'
PREFIX = ARCHIVE[:-4]+'/'
ARCHIVE_SHA = 'a303369f9973ae400ba28e3b080960c8480af8359c23434473d86d4a3ef7a1d8'
COMMIT = '45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6'

def need(ok, why):
    if not ok:
        raise ValueError(why)

def digest(data):
    return sha256(data).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    archive_path = REPO/'docs/incoming'/ARCHIVE
    blob = archive_path.read_bytes() if archive_path.exists() else subprocess.check_output(
        ['git', 'show', COMMIT+':docs/incoming/'+ARCHIVE], cwd=REPO)
    need(digest(blob) == ARCHIVE_SHA, 'whole reviewed archive or historical Git blob')
    with zipfile.ZipFile(io.BytesIO(blob)) as z:
        members = {}
        for info in z.infolist():
            if info.is_dir():
                continue
            need(info.filename.startswith(PREFIX), 'single exact archive prefix')
            name = info.filename[len(PREFIX):]
            need(not PurePosixPath(name).is_absolute() and '..' not in PurePosixPath(name).parts, 'safe relative archive member')
            need(name not in members and (info.external_attr >> 16) & 0o170000 != 0o120000, 'unique regular archive member')
            members[name] = z.read(info)
    manifest = json.loads(members['MANIFEST_SHA256.json'])['files']
    need(set(manifest) == set(members)-{'MANIFEST_SHA256.json'} and len(members) == 374, 'closed374-member release')
    for name, pin in manifest.items():
        need(len(members[name]) == pin['bytes'] and digest(members[name]) == pin['sha256'], 'whole manifest member '+name)
    direct_pins = json.loads(members['direct/SOURCE_PINS.json'])
    need(len(direct_pins) == 46, 'all46 direct input pins')
    for name, pin in direct_pins.items():
        need(digest(members[name]) == pin, 'whole direct input '+name)
    binding = json.loads(members['architecture/SOURCE_BINDING.json'])
    omitted = []
    for pin in binding['runtime_files']+binding['runtime_data']:
        if pin['path'] not in members:
            omitted.append(pin['path'])
        else:
            data = members[pin['path']]
            need(len(data) == pin['bytes'] and digest(data) == pin['sha256'], 'whole actual runtime module/data '+pin['path'])
    need(len(omitted) == 3 and all(n.endswith('.zip') for n in omitted), 'exact historical-origin ZIP metadata discrepancy')
    steps, rebuilt = [], []
    started = time.monotonic()
    with tempfile.TemporaryDirectory(prefix='round14_direct_peer_') as td:
        private = Path(td)
        packet, out = private/'packet', private/'outputs'
        for name, data in members.items():
            target = packet/name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        out.mkdir()
        env = os.environ.copy()
        env.update(PYTHONDONTWRITEBYTECODE='1', PYTHONPATH='', PYTHONHASHSEED='0')
        opt = bool(sys.flags.optimize)
        def run(label, relative_script, argv, inline=None):
            entry = ['-c', inline] if inline is not None else [str(packet/relative_script)]
            command = [sys.executable, '-B']+(['-O'] if opt else [])+entry+[str(v) for v in argv]
            before = time.monotonic()
            result = subprocess.run(command, cwd=packet, env=env, capture_output=True, timeout=180)
            need(result.returncode == 0, label+' failed: '+(result.stdout+result.stderr).decode(errors='replace')[-12000:])
            steps.append(dict(label=label, reviewed_script=relative_script,
                              script_sha256=digest(members[relative_script]),
                              optimized_python=opt, exit_code=result.returncode,
                              reviewed_function='export_replay' if inline is not None else '__main__',
                              stdout_sha256=digest(result.stdout), stderr_sha256=digest(result.stderr),
                              seconds=round(time.monotonic()-before, 3)))
            print('PASS '+label+(' [-O]' if opt else ''), flush=True)
        def compare(directory, frozen):
            names = sorted(p.name for p in directory.glob('*.json'))
            need(names, 'nonempty generated stage')
            for name in names:
                data = (directory/name).read_bytes()
                need(data == members[frozen+'/'+name], 'complete byte-identical generated artifact '+frozen+'/'+name)
                rebuilt.append(dict(path=frozen+'/'+name, sha256=digest(data), bytes=len(data)))
        r519, r517 = out/'519', out/'517'
        raw519 = packet/'architecture/carrier_hybrid_shell/raw'
        raw517 = packet/'architecture/derived16_shell/raw'
        affine_call = ('import json,sys\nfrom pathlib import Path\n'
                       'sys.path.insert(0,sys.argv[1])\n'
                       'from audit_literal_independent import export_replay,read\n'
                       'raw=Path(sys.argv[2])\n'
                       'print(json.dumps(export_replay(read(raw/"raw_audit_input.json"),read(raw/"equation.json")),sort_keys=True))\n')
        for label, raw in [('519', raw519), ('517', raw517)]:
            run('independent raw'+label+' whole affine export', 'direct_audit/audit_literal_independent.py',
                [packet/'direct_audit', raw], inline=affine_call)
        run('rebuild complete519 chain', 'direct/reproduce_integer519.py', ['--raw', raw519, '--output', r519])
        run('rebuild complete519 translation', 'direct/translate_coordinates.py', [r519/'factored/equation.json', r519/'translated'])
        run('rebuild517 signed source', 'direct/build_signed.py', [raw517, r517/'signed', '--drop-u-guard'])
        run('rebuild517 factorization/projection', 'direct/factor_horn.py', [r517/'signed/guarded.json', r517/'factored'])
        run('rebuild517 translation', 'direct/translate_coordinates.py', [r517/'factored/equation.json', r517/'final'])
        for directory, frozen in [(r519/'signed', 'direct/hybrid_noguard_signed_shell'),
                                  (r519/'factored', 'direct/integer519'),
                                  (r519/'final', 'direct/integer519_centered'),
                                  (r519/'translated', 'direct/integer519_centered'),
                                  (r517/'signed', 'direct/derived16_signed_shell'),
                                  (r517/'factored', 'direct/derived16_factored_shell'),
                                  (r517/'final', 'direct/derived16_centered_shell')]:
            compare(directory, frozen)
        checks = out/'checks'
        checks.mkdir()
        for label, raw, directory, translated in [('519', raw519, r519, 'translated'), ('517', raw517, r517, 'final')]:
            run('independent rebuilt'+label+' signed/factor/projection', 'direct_audit/audit_signed_independent.py',
                [raw, directory/'signed', directory/'factored', '--output', checks/(label+'-signed.json')])
            run('independent rebuilt'+label+' translation/quartic', 'direct_audit/audit_translation_independent.py',
                [directory/'factored', directory/translated, '--output', checks/(label+'-translation.json')])
        for name, data in members.items():
            need((packet/name).read_bytes() == data, 'private source input mutation '+name)
        need({str(p.relative_to(packet)) for p in packet.rglob('*') if p.is_file()} == set(members), 'private source inventory changed')
    report = dict(status='PASS', optimized_python=bool(sys.flags.optimize),
                  archive_sha256=ARCHIVE_SHA, historical_archive_commit=COMMIT,
                  closed_archive_members=374, direct_input_pins=46,
                  actual_runtime_modules_and_data_authenticated=True,
                  omitted_zip_entries_are_historical_origins_not_runtime=omitted,
                  reviewed_child_commands=steps, regenerated_byte_equalities=rebuilt,
                  regenerated_comparisons=len(rebuilt), distinct_regenerated_members=len({r['path'] for r in rebuilt}),
                  all_private_input_bytes_unchanged=True, temporary_copy_cleanup=True,
                  root_runner_norm_radicals_sympy_lean_or_network_executed=False,
                  scope='Deterministic direct519/517 endpoint rebuilds from exact frozen raw sources, then independent signed/projection/translation/fullquartic checks of those rebuilt outputs. Raw architecture generation and norm branch excluded.',
                  elapsed_seconds=round(time.monotonic()-started, 3), audit_self_sha256=digest(Path(__file__).read_bytes()))
    encoded = (json.dumps(report, indent=2, sort_keys=True)+'\n').encode()
    need(not args.output.exists(), 'fresh reproduction receipt required')
    args.output.write_bytes(encoded)
    print(json.dumps(dict(status='PASS', optimized_python=bool(sys.flags.optimize), commands=len(steps), regenerated_comparisons=len(rebuilt), distinct_regenerated_members=report['distinct_regenerated_members']), sort_keys=True))

if __name__ == '__main__':
    main()
