"""Untrusted adapter: wrap an old certificate's goal in a scope header."""
import argparse
import json
import sys


def shift(value, amount):
    if type(value) is int and value < 0:
        return value + amount
    if type(value) is list:
        return [shift(child, amount) for child in value]
    return value


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--offset', type=int, default=0,
                    help='Nonpositive fresh-name offset; zero preserves all original operations.')
args = parser.parse_args()
if args.offset > 0:
    parser.error('--offset must be nonpositive')
data = shift(json.load(sys.stdin), args.offset)
data[-1] = [data[-1], args.offset]
json.dump(data, sys.stdout)
print()
