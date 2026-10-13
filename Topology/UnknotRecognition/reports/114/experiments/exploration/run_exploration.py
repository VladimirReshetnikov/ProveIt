#!/usr/bin/env python3
"""Rerun a frozen exploration using a full pinned ProveIt checkout.

Only the historical absolute path string constants are relocated. The four
original scripts remain byte-for-byte unchanged in original/; their hashes
are recorded in results/exploration_summary.json. This is a convenience
runner for the exploratory literal search, not the compressed production
algorithm or a complexity benchmark.
"""
import argparse
import ast
import json
from pathlib import Path
import subprocess
import sys

OLD_FAST = '/workspace/scratch/9f3a01c0ff48/ProveIt/Topology/UnknotRecognition/fast'
OLD_EXPERIMENTS = '/workspace/scratch/9f3a01c0ff48/experiments_native'
ENTRY = {'discovery': 'search_discovery.py', 'fibonacci': 'search_surfaces.py',
         'relabel': 'search_relabellings.py', 'inspect': 'inspect_annuli.py'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('experiment', choices=ENTRY)
    parser.add_argument('--fast-root', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepare-only', action='store_true')
    args = parser.parse_args()
    fast, output = args.fast_root.resolve(), args.output.resolve()
    if not (fast/'fastunknot/normal_cut_handlebodies.py').is_file():
        parser.error('--fast-root must be the full checkout fast/ directory')
    output.mkdir(parents=True, exist_ok=True)

    class Relocate(ast.NodeTransformer):
        def visit_Constant(self, node):
            if isinstance(node.value, str):
                for old, new in [(OLD_FAST, str(fast)), (OLD_EXPERIMENTS, str(output))]:
                    if node.value == old or node.value.startswith(old + '/'):
                        node.value = new + node.value[len(old):]
                        break
            return node

    original = Path(__file__).resolve().with_name('original')
    for source in sorted(original.glob('*.py')):
        tree = Relocate().visit(ast.parse(source.read_text(), filename=str(source)))
        ast.fix_missing_locations(tree)
        transformed = ast.unparse(tree) + '\n'
        compile(transformed, str(output/source.name), 'exec')
        (output/source.name).write_text(transformed)
    metadata = dict(experiment=args.experiment, fast_root=str(fast),
                    relocated_strings_only=True, prepared_only=args.prepare_only)
    (output/'runner_request.json').write_text(json.dumps(metadata, indent=2) + '\n')
    if args.prepare_only:
        print(json.dumps(metadata))
        return
    command = [sys.executable, str(output/ENTRY[args.experiment])]
    with (output/'run.log').open('w') as log:
        process = subprocess.Popen(command, cwd=fast, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        for line in process.stdout:
            log.write(line)
            log.flush()
            print(line, end='', flush=True)
        raise SystemExit(process.wait())

if __name__ == '__main__':
    main()
