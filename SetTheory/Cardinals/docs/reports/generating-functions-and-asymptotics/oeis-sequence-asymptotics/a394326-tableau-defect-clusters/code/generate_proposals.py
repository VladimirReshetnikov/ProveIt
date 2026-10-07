#!/usr/bin/env python3
"""Optional regeneration of dyadic inverse candidates; needs mpmath >= 1.3.

The output is not a certificate until replayed by certify_local.py. All three
candidates are checked by exact interval residuals before this script saves them.
"""
import argparse
import json
from pathlib import Path
from rigorous import IV, matrix, propose_inverse


def run():
    low, high = IV('0.78615504'), IV('0.78615506')
    interval = IV(low.lo, high.hi, True)
    return {'format': 'Report183 exact dyadic inverse proposals v1',
            'proposals': {label: propose_inverse(matrix(20, z, kind)[1])
                          for label, kind, z in [('L_low', 'L', low),
                                                 ('L_high', 'L', high),
                                                 ('K_interval', 'K', interval)]}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(json.dumps(run(), indent=2, sort_keys=True) + '\n')
    print('Saved three exactly residual-checked inverse proposals to ' + str(args.output))


if __name__ == '__main__':
    main()
