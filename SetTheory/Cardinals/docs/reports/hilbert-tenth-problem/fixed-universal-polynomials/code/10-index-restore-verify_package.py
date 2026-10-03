#!/usr/bin/env python3
"""Identity gate and offline replay for the frozen Research Report 33 packet."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

MANIFEST_SHA256 = 'e71d4fcfaceea1e9f1255c3feb69095a1ceac7b225d0d422ff03d94bb1b28648'
ROOT = Path(__file__).resolve().parent


def need(value, message):
    if value is not True:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique(pairs):
    result = {}
    for k, v in pairs:
        need(k not in result, 'duplicate JSON key')
        result[k] = v
    return result


def reject_constant(value):
    raise ValueError('nonfinite JSON constant: ' + value)


def gate():
    raw = (ROOT/'MANIFEST.json').read_bytes()
    need(sha(raw) == MANIFEST_SHA256, 'Enclosing manifest identity mismatch')
    doc = json.loads(raw.decode('utf-8'), object_pairs_hook=unique,
                     parse_constant=reject_constant)
    need(type(doc) is dict and set(doc) == {'schema','files'}, 'manifest shape')
    need(doc['schema'] == 'research-report33-release-v1' and
         type(doc['files']) is dict, 'manifest schema')
    files = doc['files']
    for name, expected in files.items():
        need(type(name) is str and type(expected) is str and len(expected) == 64,
             'manifest entry types')
        rel = Path(name)
        need(not rel.is_absolute() and '..' not in rel.parts and
             rel.as_posix() == name, 'unsafe relative path')
        path = ROOT/rel
        need(path.is_file() and not path.is_symlink() and ROOT in path.resolve().parents,
             'missing or unsafe payload file: ' + name)
        need(sha(path.read_bytes()) == expected, 'Payload identity mismatch: ' + name)
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()}
    need(actual == set(files) | {'MANIFEST.json','verify_package.py','SHA256SUMS'},
         'Unexpected or missing file in release inventory')
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--replay', action='store_true')
    args = parser.parse_args()
    files = gate()
    if args.replay:
        for folder in ('repro','supplements'):
            launcher = ROOT/folder/'verify.py'
            options = ['-O'] if sys.flags.optimize else []
            result = subprocess.run([sys.executable,'-I','-B']+options+
                                    [str(launcher),'--replay'],cwd='/',check=False)
            need(result.returncode == 0, folder + ' replay failed')
        need(gate() == files, 'Release manifest changed during replay')
    print('PASS: '+str(len(files))+' frozen payload identities'+
          ('; both isolated normal/-O suites and eight tamper tests' if args.replay else ''))
    return 0

if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, OSError) as exc:
        print(str(exc), file=sys.stderr)
        raise SystemExit(1)
