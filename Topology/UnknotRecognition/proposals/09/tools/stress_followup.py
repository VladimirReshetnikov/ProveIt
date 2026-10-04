"""Run one baseline raw-homology sample with a longer, still bounded budget."""
import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=float, default=60)
    parser.add_argument('--output', default=str(ROOT/'results'/'stress_60.json'))
    args = parser.parse_args()
    if args.seconds <= 0:
        parser.error('--seconds must be positive')
    data = json.loads((ROOT/'examples/stress/original_random_5_braid_36.json').read_text())
    request = {'input': data, 'implementation': 'baseline', 'task': 'rank',
               'seconds': args.seconds, 'repetitions': 1, 'max_objects': 200000}
    try:
        run = subprocess.run([sys.executable, str(ROOT/'tools/benchmark_worker.py')],
                             input=json.dumps(request), text=True, capture_output=True,
                             timeout=args.seconds+10, cwd=ROOT,
                             env=dict(os.environ, PYTHONHASHSEED='0'))
        if run.returncode:
            raise RuntimeError(run.stderr)
        result = json.loads(run.stdout)
    except subprocess.TimeoutExpired:
        result = {'result': {'status': 'UNKNOWN', 'reason': 'external worker timeout'},
                  'external_limit_seconds': args.seconds+10}
    Path(args.output).write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
