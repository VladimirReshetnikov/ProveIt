"""Reproduce the 40 expected-verdict comparisons for scalar-neutral truth."""
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def main():
    receipts = []
    profiles = [('control_source_dispatch_bytes.py', 'checker_compact.py'),
                ('control_source_dispatch_ast.py', 'checker_compact_ast.py')]
    for path in sorted((ROOT / 'tests/neutral_baseline').glob('*.json')):
        source = path.read_text()
        transformed = json.loads(source)
        changed = 0
        for packet in transformed[:-1]:
            if packet[0] == []:
                packet[0] = 0
                changed += 1
        transformed = json.dumps(transformed, separators=(',', ':'))
        expected = not path.name.endswith('original_local.json')
        for old, new in profiles:
            for optimized in (False, True):
                for program, certificate in ((old, source), (new, transformed)):
                    command = [sys.executable] + (['-O'] if optimized else [])
                    result = subprocess.run(command + [str(ROOT / ('controls' if program.startswith('control_') else 'code') / program)],
                                            input=certificate, text=True,
                                            capture_output=True, timeout=30)
                    accepted = result.returncode == 0 and result.stdout == 'ACCEPT\n'
                    item = {'certificate': path.name, 'program': program,
                            'optimized': optimized, 'expected': expected,
                            'accepted': accepted, 'matches': accepted == expected,
                            'neutral_packets_changed': changed}
                    receipts.append(item)
                    if not item['matches']:
                        raise AssertionError(item)
    result = {'checks': len(receipts), 'mismatches': 0, 'receipts': receipts}
    (ROOT / 'evidence/zero_neutral_audit.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'checks': len(receipts), 'mismatches': 0}))


if __name__ == '__main__':
    main()
