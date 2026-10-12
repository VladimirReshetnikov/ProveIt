"""Usage: PYTHONPATH=code python -m pattern_kernel input.json --output proof.json"""
import argparse
import json
from pathlib import Path
from .core import Tile, Block, natural, solve
from .verify import verify_result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = json.loads(args.input.read_text())
    if data.get('schema') != 'closed-tile-chain-v1':
        raise ValueError('unsupported input schema')
    blocks = []
    for record in data['blocks']:
        t = record['tile']
        tile = Tile(t['n'], tuple(tuple(e) for e in t['edges']),
                    tuple(t['left']), tuple(t['right']))
        blocks.append(Block(tile, natural(record['copies'])))
    chain = tuple(blocks)
    result = solve(chain)
    if not verify_result(chain, result):
        raise RuntimeError('internal proof replay failed')
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'graph_verdict': result['graph_proof']['verdict'],
                      'kernel_vertices': result['kernel']['n'],
                      'proof_replayed': True,
                      'knot_recognition_performed': False}))

if __name__ == '__main__':
    main()
