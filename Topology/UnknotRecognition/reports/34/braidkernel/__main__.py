from __future__ import annotations
import argparse, json, sys
from pathlib import Path
from . import Braid, kernelize, recognize

parser = argparse.ArgumentParser(description='Certified Artin braid minority-sign kernels')
parser.add_argument('input', type=Path, help='JSON with strands and word')
parser.add_argument('--kernel-only', action='store_true')
parser.add_argument('--max-crossings', type=int, default=12)
parser.add_argument('--seconds', type=float, default=None)
args = parser.parse_args()
try:
    data = json.loads(args.input.read_text())
    braid = Braid.checked(data['strands'], data['word'])
    result = kernelize(braid) if args.kernel_only else recognize(
        braid, max_crossings=args.max_crossings, seconds=args.seconds)
    print(json.dumps(result, indent=2))
except (ValueError, KeyError, TypeError, OSError) as error:
    print(f'input error: {error}', file=sys.stderr)
    sys.exit(2)
