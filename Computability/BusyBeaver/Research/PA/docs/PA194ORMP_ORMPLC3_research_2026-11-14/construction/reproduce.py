#!/usr/bin/env python3
"""Reconstruct both tables and rerun the complete literal and relative checks.

Requires Python 3.10+ and its standard library. All input paths are resolved
relative to this file, so the package works after extraction anywhere.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, help='Fresh evidence directory.')
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('Assertions must remain enabled; do not use Python -O.')
    output = (args.output or Path(tempfile.mkdtemp(prefix='pa194-ormp-'))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    jobs = [
        ('build_ORMP', ['build.py', '--output', output/'PA194ORMP']),
        ('build_ORMPLC3', ['build_accelerated.py', '--source', output/'PA194ORMP',
                           '--output', output/'PA194ORMPLC3']),
        ('replay_parent', ['check.py', HERE/'parent', '--output', output/'parent_replay']),
        ('replay_ORMP', ['check.py', output/'PA194ORMP']),
        ('replay_ORMPLC3', ['check.py', output/'PA194ORMPLC3']),
        ('relative_ORMP', ['verify_relative.py', '--candidate', output/'PA194ORMP',
                          '--parent-replay', output/'parent_replay',
                          '--output', output/'relative_ORMP.json']),
        ('relative_ORMPLC3', ['verify_relative.py', '--candidate', output/'PA194ORMPLC3',
                             '--parent-replay', output/'parent_replay',
                             '--output', output/'relative_ORMPLC3.json']),
    ]
    for name, arguments in jobs:
        command = [sys.executable, '-B', str(HERE/arguments[0])]
        command += [str(x) for x in arguments[1:]]
        print('Running', name, flush=True)
        result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        (output/(name+'.log')).write_text(result.stdout)
        if result.returncode:
            print(result.stdout)
            raise SystemExit(name+' failed')
    for generated, frozen in [('PA194ORMP', 'machine'), ('PA194ORMPLC3', 'accelerated')]:
        for name in ['machine.tm', 'machine.native.tm', 'nodes.json', 'sites.json',
                     'instructions.json', 'labels.json', 'grammar.json']:
            if (output/generated/name).read_bytes() != (HERE/frozen/name).read_bytes():
                raise AssertionError('Frozen artifact differs: '+generated+'/'+name)
    result = {'status': 'PASS', 'machines': ['PA194ORMP', 'PA194ORMPLC3'],
              'complete_literal_outcomes_per_machine': 4778,
              'revised_parent_replayed': True,
              'exact_source_arrays_and_closed_frame_endpoints': True,
              'kernel_checked': False,
              'scope': 'Finite and symbolic certificates for the accompanying written iPRA proof.'}
    (output/'reproduction.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
    print('Evidence:', output)


if __name__ == '__main__':
    main()
