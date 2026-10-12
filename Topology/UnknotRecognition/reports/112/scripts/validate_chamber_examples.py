"""Replay stored source-bound chamber-graph packets without Regina.

Requires Python 3.10+ and the complete native ``fastunknot`` package with the
chamber-graph verifier overlay applied.  No corpus, fixtures, test helpers,
external Python packages, orbit search, or surface producer is needed.

Example, from the extracted archive root using its bundled native snapshot::

    python scripts/validate_chamber_examples.py \
      --fast-root integration/native_snapshot \
      examples/three_parallel_meridians.json \
      examples/exponential_meridian_128.json

Each input contains the exact source triangulation, coordinates and certificate.
The command emits one small JSON result per packet and exits nonzero if any
packet is malformed, exceeds an optional trace-event cap, or fails replay.
"""

import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fast-root', type=Path, required=True,
                        help='directory containing the native fastunknot package')
    parser.add_argument('--max-operations', type=int,
                        help='combined recorded orbit-event cap per packet')
    parser.add_argument('packets', type=Path, nargs='+')
    args = parser.parse_args()
    root = args.fast_root.resolve()
    if not (root / 'fastunknot/normal_chamber_graph_verify.py').is_file():
        parser.error('--fast-root must contain fastunknot/normal_chamber_graph_verify.py')
    if args.max_operations is not None and args.max_operations < 0:
        parser.error('--max-operations must be nonnegative')
    sys.path.insert(0, str(root))
    from fastunknot.integer_codec import encoded_integer
    from fastunknot.normal_chamber_graph_verify import verify_normal_chamber_graph

    failed = False
    expected_fields = {'source', 'triangulation', 'coordinates', 'certificate'}
    for path in args.packets:
        result = dict(file=str(path), verified=False)
        try:
            data = path.read_bytes()
            result['packet_sha256'] = sha256(data).hexdigest()
            packet = json.loads(data)
            if type(packet) is not dict or set(packet) != expected_fields:
                raise ValueError('expected source, triangulation, coordinates and certificate')
            if type(packet['source']) is not str:
                raise ValueError('packet source label must be a string')
            proof = packet['certificate']
            result['verified'] = verify_normal_chamber_graph(
                packet['triangulation'], packet['coordinates'], proof,
                max_operations=args.max_operations)
            if result['verified']:
                graph = proof['graph']
                result.update(source=packet['source'],
                              input_sha256=proof['input_sha256'],
                              vertices=encoded_integer(graph['vertices']),
                              edges=len(graph['edges']),
                              cycle_rank=encoded_integer(graph['cycle_rank']))
            else:
                result['error'] = 'certificate rejected or recorded orbit-event cap exceeded'
        except (OSError, UnicodeError, ValueError, TypeError, KeyError) as exc:
            result['error'] = str(exc)
        failed |= not result['verified']
        print(json.dumps(result, sort_keys=True))
    return int(failed)


if __name__ == '__main__':
    raise SystemExit(main())
