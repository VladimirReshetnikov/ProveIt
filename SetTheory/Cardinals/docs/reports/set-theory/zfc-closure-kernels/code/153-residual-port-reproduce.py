#!/usr/bin/env python3
"""Offline verification of this research packet; no verified <=218 machine claimed.

Default: verify the manifest and exact tables, finite-algebra and source
checks, concrete counterexamples, clean startup witnesses, and stored
primitive-proof receipt integrity. --full-runtime freshly rederives the
three new primitive proofs. --full-baseline runs the unchanged K219 driver's
default mode, with its inherited quick calibration. --search runs the
optional bounded C++ local-merge experiments.
"""
import argparse, hashlib, json, os, shutil, stat, subprocess, sys, time, zipfile
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent
ARCHIVES = (
    ('K219_Construction_2026-10-20', '04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b'),
    ('K220_Construction_2026-10-20', '132cbb326fcbf6e54957a03095c5f790e207f4ed8ebfb6ceb6e272f329e4ee00'),
    ('K221_Construction_2026-10-20', 'a06c99b775193d9642a2734b7dd5fe7b72736fbdf9d9d8be438321d5e5d57ba4'),
)

def need(test, message):
    if not test:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def safe(name):
    need(isinstance(name, str) and name and '\\' not in name and ':' not in name and '\x00' not in name, 'Invalid member path')
    path = PurePosixPath(name)
    need(not path.is_absolute() and all(p not in ('', '.', '..') for p in name.rstrip('/').split('/')), 'Escaping member path')
    return path

def extract(archive, dest, expected_name, digest):
    need(sha(archive) == digest, 'Pinned archive mismatch: ' + str(archive))
    members = set()
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            name = safe(info.filename)
            need(name.parts[0] == expected_name and name.as_posix() not in members, 'Unexpected/duplicate archive member')
            members.add(name.as_posix())
            mode = stat.S_IFMT(info.external_attr >> 16)
            need(mode in (0, stat.S_IFREG, stat.S_IFDIR) and not info.flag_bits & 1, 'Nonregular/encrypted archive member')
            target = dest / name
            need(dest in target.resolve().parents, 'Escaping archive destination')
            if info.is_dir():
                target.mkdir(parents=True, exist_ok=True)
            else:
                target.parent.mkdir(parents=True, exist_ok=True)
                with z.open(info) as source, target.open('xb') as output:
                    shutil.copyfileobj(source, output)
                need(target.stat().st_size == info.file_size, 'Truncated extraction')
    return dest / expected_name

def verify_manifest():
    manifest = json.loads((ROOT/'manifest.json').read_text())
    need(manifest['schema_version'] == 1, 'Manifest schema')
    paths = set()
    for record in manifest['files']:
        name = record['path']
        need(name not in paths and name != 'manifest.json', 'Duplicate/self manifest entry')
        paths.add(name)
        path = ROOT / safe(name)
        need(path.is_file() and not path.is_symlink() and ROOT in path.resolve().parents, 'Missing/nonregular payload')
        need(path.stat().st_size == record['size'] and sha(path) == record['sha256'], 'Payload changed: ' + name)
    # Only these local products of Python/TeX are outside the distributed payload.
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()
              and p != ROOT/'manifest.json'
              and '__pycache__' not in p.relative_to(ROOT).parts
              and '.report-build' not in p.relative_to(ROOT).parts}
    need(actual == paths, 'Manifest does not describe the exact payload inventory')
    return len(paths)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir', required=True, type=Path)
    ap.add_argument('--full-runtime', action='store_true')
    ap.add_argument('--full-baseline', action='store_true')
    ap.add_argument('--search', action='store_true')
    a = ap.parse_args()
    need(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'), 'Assertions must remain enabled')
    out = a.output_dir.resolve()
    need(out != ROOT and ROOT not in out.parents, 'Output must be outside the packet')
    need(not out.exists() or not any(out.iterdir()), 'Output directory must initially be empty')
    out.mkdir(parents=True, exist_ok=True)
    (out/'logs').mkdir()
    start = time.monotonic()
    receipt = dict(status='RUNNING', requested_218_state_goal='UNMET',
                   full_runtime=a.full_runtime, full_baseline=a.full_baseline,
                   bounded_search=a.search, phases=[])
    def save():
        receipt['seconds'] = time.monotonic() - start
        (out/'replay.json').write_text(json.dumps(receipt, indent=2)+'\n')
    def phase(name, command):
        print(name, flush=True)
        then = time.monotonic()
        log = out/'logs'/(name+'.log')
        with log.open('w') as f:
            process = subprocess.run([sys.executable, '-B', *map(str, command)],
                                     stdout=f, stderr=subprocess.STDOUT,
                                     env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
        receipt['phases'].append(dict(name=name, seconds=time.monotonic()-then,
                                     returncode=process.returncode,
                                     log=str(log.relative_to(out))))
        save()
        need(process.returncode == 0, 'Failed ' + name + '; see ' + str(log))
    try:
        receipt['manifest_files'] = verify_manifest()
        deps = out/'dependencies'
        archive = ROOT/'vendor'/(ARCHIVES[0][0]+'.zip')
        roots = []
        for i, (name, digest) in enumerate(ARCHIVES):
            base = extract(archive, deps, name, digest)
            roots.append(base)
            if i + 1 < len(ARCHIVES):
                archive = base/'portable/vendor'/(ARCHIVES[i+1][0]+'.zip')
        b219, b220, b221 = roots
        for script in ['compound_fourth_obstruction', 'peirce_hc_countermodels', 'counter_salt_blocks']:
            phase('theory_'+script, [ROOT/'theory'/(script+'.py'), '--out', out/(script+'.json')])
        phase('encoding', [ROOT/'encoding/reproduce.py', '--output-dir', out/'encoding'])
        phase('two_adic_codec', [ROOT/'experiments/two_adic/reproduce.py', '--output-dir', out/'two_adic'])
        phase('literal_tables', [ROOT/'machine/rebuild.py', '--baseline219', b219])
        phase('stored_runtime_integrity', [ROOT/'portable/audit_receipts.py', '--baseline221', b221, '--output', out/'runtime_audit.json'])
        for name in ['weak218_rejected', 'zero_guard219']:
            phase('blank_'+name, [ROOT/'machine/check_blank_prefix.py', ROOT/'machine'/name/'machine.native.tm', out/(name+'_boot.json')])
            fresh = json.loads((out/(name+'_boot.json')).read_text())
            old = json.loads((ROOT/'machine'/name/'boot.json').read_text())
            need(fresh == old, 'Blank-prefix receipt changed for '+name)
        phase('weak_gate_counterexamples', [ROOT/'machine/replay_gate_counterexample.py', '--baseline219', b219, '--output', out/'weak_counterexamples'])
        phase('drop50_counterexample', [ROOT/'experiments/drop50/check.py', '--baseline219', b219, '--output', out/'drop50.json'])
        if a.full_runtime:
            for name in ['weak218_rejected', 'zero_guard219', 'counter_salt223_interface']:
                phase('fresh_runtime_'+name, [ROOT/'machine/check_interfaces.py', '--baseline221', b221,
                      '--table', ROOT/'machine'/name/'machine.native.tm', '--sites', ROOT/'machine'/name/'sites.json', '--output', out/'fresh_runtime'/name])
        if a.full_baseline:
            phase('baseline219_default', [b219/'portable/reproduce.py', '--output-dir', out/'baseline219_replay'])
        if a.search:
            phase('bounded_window_searches', [ROOT/'experiments/window_search/reproduce.py', '--baseline219', b219, '--output-dir', out/'window_search'])
        receipt['status'] = 'RESEARCH_PACKET_REPLAY_PASS'
        receipt['scope'] = 'The requested <=218 consistency-machine construction is not achieved. Passing verifies only the explicitly listed research artifacts and their stated boundaries.'
        save()
        print(receipt['status'], flush=True)
    except Exception as error:
        receipt.update(status='FAILED', error=repr(error))
        save()
        raise

if __name__ == '__main__':
    main()
