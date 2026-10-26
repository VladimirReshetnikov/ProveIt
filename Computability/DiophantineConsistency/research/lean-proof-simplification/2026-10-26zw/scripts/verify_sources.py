#!/usr/bin/env python3
"""Verify target hashes, public statement identity, and proof-only edit scope."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def declaration(text, name):
    start = text.index('theorem ' + name + ' ')
    rest = text[start:]
    match = re.search(r'\n(?:/--|theorem |end )', rest)
    return rest[:match.start() if match else len(rest)].rstrip()


def erase_proof(text, name):
    decl = declaration(text, name)
    statement, _ = decl.split(':= by', 1)
    return text.replace(decl, statement + ':= by\n  PROOF')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path)
    args = parser.parse_args()
    bundle = Path(__file__).resolve().parents[1]
    manifest = json.loads((bundle / 'evidence/source_manifest.json').read_text())
    checkout_states = []
    for item in manifest['files']:
        before = bundle / 'baseline' / item['path']
        after = bundle / 'proposed' / item['path']
        assert sha(before) == item['baseline_sha256'], before
        assert sha(after) == item['proposed_sha256'], after
        btext, atext = before.read_text(), after.read_text()
        bdecl, adecl = declaration(btext, item['theorem']), declaration(atext, item['theorem'])
        assert bdecl.split(':= by', 1)[0] == adecl.split(':= by', 1)[0]
        bnorm, anorm = erase_proof(btext, item['theorem']), erase_proof(atext, item['theorem'])
        if item['comment_changed']:
            bnorm = bnorm.replace(
                '/-- The actual B is a unit, derived from the positive order of its power. -/',
                '/-- The actual B is a power of two and the entire block modulus is odd. -/')
        assert bnorm == anorm, 'Change outside allowed proof/comment: ' + item['path']
        assert len(btext.splitlines()) - len(atext.splitlines()) == item['removed_lines']
        if args.project:
            current = sha(args.project.resolve() / item['path'])
            state = ('baseline' if current == item['baseline_sha256'] else
                     'proposed' if current == item['proposed_sha256'] else 'different')
            checkout_states.append(state)
            print(item['theorem'] + ': checkout ' + state)
        else:
            print(item['theorem'] + ': proof-only comparison PASS')
    if args.project and 'different' in checkout_states:
        raise SystemExit('Some checkout sources differ; review before applying patches.')
    if args.project and all(state == 'baseline' for state in checkout_states):
        patches = [str(p) for p in sorted((bundle / 'patches').glob('*.patch'))]
        subprocess.run(['git', 'apply', '--check', *patches],
                       cwd=args.project.resolve(), check=True)
        print('Combined git apply --check: PASS')
    print('Exact total physical-line reduction:',
          sum(item['removed_lines'] for item in manifest['files']))


if __name__ == '__main__':
    main()
