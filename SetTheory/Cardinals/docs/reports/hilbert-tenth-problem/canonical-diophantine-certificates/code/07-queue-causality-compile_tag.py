#!/usr/bin/env python3
"""Compile a deletion-tag specification supplied as a JSON object."""
from pathlib import Path
import argparse
import json
from queue_certificates import compile_tag


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--spec', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--no-witness', action='store_true')
    args = parser.parse_args()
    data = json.loads(args.spec.read_text(encoding='utf8'))
    cert = compile_tag(data['appendants'], data['deletion'], data['initial'],
                       data['horizon'], data.get('terminal', []),
                       attach_witness=not args.no_witness)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(cert, indent=2)+'\n', encoding='utf8')
    print(json.dumps({'output':str(args.output),'variables':len(cert['variables']),
                      'degree_upper_bound':cert['degree_upper_bound'],
                      'witness_found':'witness' in cert}, indent=2))


if __name__ == '__main__':
    main()
