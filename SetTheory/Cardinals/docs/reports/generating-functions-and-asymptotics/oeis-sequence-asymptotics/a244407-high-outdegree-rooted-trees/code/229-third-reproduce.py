#!/usr/bin/env python3
"""Run the standard-library finite checks; write only when --output is supplied."""
import argparse
from pathlib import Path
from output_json import emit_json, prepare_output
from third_sector import check_exact, check_literal_trees, check_root_tails


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n', type=int, default=192, help='exact coefficient cutoff, 1..256 (default 192)')
    parser.add_argument('--k', type=int, default=64, help='largest outdegree, 1..80 (default 64)')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    prepare_output(parser, args.output)
    try:
        result = {'status': 'pass', 'exact': check_exact(args.n, args.k),
                  'root_tail': check_root_tails(), 'literal': check_literal_trees()}
    except (ValueError, ArithmeticError) as error:
        parser.exit(2, f'verification error: {error}\n')
    emit_json(parser, result, args.output)


if __name__ == '__main__':
    main()
