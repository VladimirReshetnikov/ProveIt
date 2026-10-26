#!/usr/bin/env python3
"""Recheck isolated proofs. This never applies patches or builds production modules."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, tempfile, time

PACKET = Path(__file__).resolve().parents[1]
MATHLIB = '81a5d257c8e410db227a6665ed08f64fea08e997'
FILES = ['PowerFixedPoint.lean', 'CommonModulusCertificate.lean',
         'WeightedUpdates.lean', 'OriginReuse.lean', 'GammaCommon.lean']


def capture(command, cwd=None):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument('--repo', type=Path, help='Pinned ProveIt checkout with cached mathlib')
    source.add_argument('--lean', type=Path, help='Explicit Lean 4.32.0 executable')
    parser.add_argument('--lean-path', help='Dependency search path for --lean; defaults to LEAN_PATH')
    parser.add_argument('--output-dir', type=Path, help='Build/log directory; default is a fresh temporary directory')
    parser.add_argument('--include-unchecked', action='store_true',
                        help='Also try the two concrete fixtures whose earlier runs stalled before diagnostics')
    parser.add_argument('--show-commands', action='store_true', help='Print commands without running checks')
    args = parser.parse_args()
    if args.repo:
        repo = args.repo.resolve()
        expected_toolchain = (PACKET/'sources/lean-toolchain').read_text().strip()
        assert (repo/'lean-toolchain').read_text().strip() == expected_toolchain, 'Wrong Lean pin'
        manifest = json.loads((repo/'lake-manifest.json').read_text())
        mathlib = next(x for x in manifest['packages'] if x['name'] == 'mathlib')
        assert mathlib['rev'] == MATHLIB, 'Wrong mathlib pin'
        prefix = Path(capture(['lake', 'env', 'lean', '--print-prefix'], repo))
        lean = prefix/'bin/lean'
        search = capture(['lake', 'env', 'printenv', 'LEAN_PATH'], repo)
        search = os.pathsep.join(str((repo/entry).resolve()) if not Path(entry).is_absolute() else entry
                                 for entry in search.split(os.pathsep) if entry)
    else:
        lean = args.lean.resolve()
        search = args.lean_path or os.environ.get('LEAN_PATH', '')
        if not search:
            parser.error('--lean requires --lean-path or LEAN_PATH containing the pinned mathlib and dependencies')
    version = capture([str(lean), '--version'])
    assert 'version 4.32.0,' in version, version
    build = args.output_dir.resolve() if args.output_dir else Path(tempfile.mkdtemp(prefix='proveit-proof-replay-'))
    build.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(build), search]))
    files = FILES + (['ControllerPowerComparison.lean','ControllerPowerAfter.lean'] if args.include_unchecked else [])
    receipt = {'compiler':version, 'mathlib_expected_revision':MATHLIB,
               'scope':'Isolated modules only; no production or client build', 'checks':[]}
    print('Build and log directory:', build, flush=True)
    for name in files:
        file = PACKET/'lean'/name
        command = [str(lean), '-j1', '-R', str(PACKET/'lean'), '-o', str(build/(file.stem+'.olean')), str(file)]
        if args.show_commands:
            print(json.dumps(command))
            continue
        print('Checking', name, flush=True)
        start = time.monotonic()
        log = build/(file.stem+'.log')
        with log.open('w') as output:
            process = subprocess.run(command, env=env, stdout=output, stderr=subprocess.STDOUT)
        item = {'file':name, 'sha256':hashlib.sha256(file.read_bytes()).hexdigest(),
                'command':command, 'exit_code':process.returncode,
                'elapsed_seconds':round(time.monotonic()-start,3), 'log':str(log)}
        receipt['checks'].append(item)
        (build/'replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(name, 'exit', process.returncode, 'log:', log, flush=True)
        if process.returncode:
            raise SystemExit(process.returncode)
    if not args.show_commands:
        print('All requested isolated checks passed. No production modules were rebuilt.')

if __name__ == '__main__':
    main()
