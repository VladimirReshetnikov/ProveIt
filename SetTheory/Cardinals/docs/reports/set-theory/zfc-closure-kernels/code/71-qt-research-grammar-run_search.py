#!/usr/bin/env python3
"""Optional bounded C++ search followed by independent Python verification."""
from pathlib import Path
import argparse
import json
import subprocess
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/'fine/runtime/code'))
from audit_fine_grammar import audit


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('directory', type=Path, help='A retained or regenerated seed directory.')
    parser.add_argument('output', type=Path, help='Output grammar JSON.')
    parser.add_argument('--engine', choices=['cluster', 'embed'], default='cluster')
    parser.add_argument('--seconds', type=float, default=10)
    parser.add_argument('--seed', type=int, default=42)
    parser.add_argument('--target', type=int, default=127)
    args = parser.parse_args()
    assert args.seconds > 0
    seed = json.loads((args.directory/'seed.json').read_text())
    binary = HERE/('anneal_'+args.engine)
    if not binary.is_file():
        parser.error('Compile first: c++ -O2 -std=c++17 anneal_'+args.engine+'.cpp -o anneal_'+args.engine)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    command = [str(binary), str(args.directory/'grammar.txt'), str(args.directory/'constraints.txt'),
               str(args.output), str(args.seconds), str(args.seed), str(args.target),
               str(HERE/'fine/fine-lock54.txt'), str(args.directory/'resume.txt')]
    subprocess.run(command, check=True)
    candidate = json.loads(args.output.read_text())
    if 'source_override' in seed:
        candidate['source_override'] = seed['source_override']
    args.output.write_text(json.dumps(candidate, indent=2)+'\n')
    report = audit(args.output, short_scan=True)
    args.output.with_suffix('.audit.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': report['status'], 'grammar_roles': report['grammar_states'],
                      'charged_framework_roles': report['framework_states'],
                      'nominal_total': report['working_states']}, indent=2))


if __name__ == '__main__':
    assert __debug__, 'Assertions must remain enabled.'
    main()
