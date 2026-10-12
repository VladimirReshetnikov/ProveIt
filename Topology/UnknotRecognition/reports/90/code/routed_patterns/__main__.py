"""Read a closed tile chain and emit/replay a routed graph certificate."""
import argparse
import json
from pathlib import Path
from .core import parse_chain, solve
from .verify import verify_result

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('source', type=Path)
parser.add_argument('--output', type=Path)
parser.add_argument('--verify', type=Path)
parser.add_argument('--through', action='store_true',
                    help='reblock arbitrary through-component tiles before routing')
args = parser.parse_args()
chain = parse_chain(json.loads(args.source.read_text()))
if args.verify:
    proof = json.loads(args.verify.read_text())
    if proof.get('schema') == 'stable-routed-cubic-cut-v1':
        from .stable_verify import verify_result
    accepted = verify_result(chain, proof)
    print(json.dumps({'accepted': accepted}))
    raise SystemExit(0 if accepted else 1)
if args.through:
    from .stable import solve
    from .stable_verify import verify_result
result = solve(chain)
if not verify_result(chain, result):
    raise RuntimeError('independent replay rejected the produced certificate')
encoded = json.dumps(result, indent=2) + '\n'
if args.output:
    args.output.write_text(encoded)
else:
    print(encoded, end='')
