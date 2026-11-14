#!/usr/bin/env python3
"""Portable release verification; no network and no proof-assistant claim.

Default: integrity, both builders, both free-term/word checkers, the rejected
emitter invariant, exact novelty and direct-control congruence.
--literal additionally rederives the four list lemmas and all physical
source contracts for both machines. Use Python without -O.
"""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
EXPECTED = {
    'PA194GH': 'b9fadcb197c33895603c71b7119bc92b1772c01960804e8850e2a66dd39a995e',
    'PA194GHS': '68442e304616894c14f0e256624208c89fc9e84897d678b1c809f0c27a4ca471',
}

def file_hash(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--literal', action='store_true')
    ap.add_argument('--output', type=Path, help='optional receipt outside the frozen release')
    args = ap.parse_args()
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Run with assertions enabled, without -O.')
    integrity = 0
    if (ROOT / 'SHA256SUMS').exists():
        for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
            expected, relative = line.split('  ', 1)
            path = ROOT / relative
            if not path.is_file() or file_hash(path) != expected:
                raise RuntimeError('Release integrity mismatch: ' + relative)
            integrity += 1
    for name, expected in EXPECTED.items():
        if file_hash(ROOT / 'machines' / name / 'machine.tm') != expected:
            raise RuntimeError('Candidate table identity changed: ' + name)

    census = json.loads((ROOT / 'comparison/census_full/summary.json').read_text())
    assert census['missing_tracked_files'] == 0
    assert census['tracked_selected_files'] == 10090
    assert census['classes_by_state_count']['194'] == 94
    assert len(json.loads((ROOT / 'comparison/packet_ledger.json').read_text())) == 82
    checked = []
    with tempfile.TemporaryDirectory(prefix='pa194gh-verify-') as tmp:
        tmp = Path(tmp)
        def run(label, relative, *extra):
            command = [sys.executable, '-B', str(ROOT / relative), *map(str, extra)]
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            if result.returncode:
                raise RuntimeError(label + ' failed:\n' + result.stdout[-5000:] + result.stderr[-5000:])
            checked.append({'check': label, 'status': 'PASS'})
            print(label + ': PASS', flush=True)

        run('GH construction and 4,754 source outcomes', 'machines/PA194GH/build.py')
        run('GHS construction and 4,750 source outcomes', 'machines/PA194GHS/build.py')
        run('GH symbolic emitter and command words', 'machines/PA194GH/check_commands.py')
        run('GHS symbolic emitter and command words', 'machines/PA194GHS/check_commands.py')
        run('Rejected 189-token emitter residue certificate',
            'machines/PA194GH/search/top_generalizer/check_invariant.py')
        run('Exact two-candidate novelty and ordinary congruence', 'comparison/verify_novelty.py',
            '--references', ROOT / 'comparison/census_full/tables',
            '--output', tmp / 'novelty.json',
            ROOT / 'machines/PA194GH/machine.tm', ROOT / 'machines/PA194GHS/machine.tm')
        novelty = json.loads((tmp / 'novelty.json').read_text())
        assert novelty['reference_count'] == 94 and novelty['candidate_count'] == 2
        assert all(x['direct_congruence_states'] == 194 for x in novelty['candidates'])
        if args.literal:
            run('Independent literal physical contracts for both machines',
                'machines/PA194GH/independent/check.py', ROOT / 'machines/PA194GH',
                ROOT / 'machines/PA194GHS', '--output', tmp / 'literal')

    receipt = {
        'status': 'PASS', 'integrity_files': integrity,
        'literal_replayed_in_this_invocation': args.literal,
        'checks': checked, 'machine_sha256': EXPECTED,
        'scope': 'Executable certificates and exact reconstruction. No completed machine-specific iPRA or Lean consistency endpoint is claimed.'
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
