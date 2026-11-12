"""Untrusted record conversion to compact477.py.

Default input is the old whole-array four-field certificate whose last item
is its goal. With --wrapped-goal, input already ends in [goal,0] as required
by compact478.py. Only administrative major fields change from integer 0 to
[]. The numerical zeros in terms and formulas are preserved.
"""
import argparse
import copy
import json
from pathlib import Path


def convert(certificate, wrapped_goal=False):
    result = copy.deepcopy(certificate)
    if type(result) is not list or not result:
        raise ValueError('expected a nonempty certificate array')
    for record in result[:-1]:
        if (type(record) is list and len(record) == 4
                and type(record[0]) is int and record[0] == 0):
            record[0] = []
    if not wrapped_goal:
        result[-1] = [result[-1], 0]
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--wrapped-goal', action='store_true')
    args = parser.parse_args()
    result = convert(json.loads(args.input.read_text()), args.wrapped_goal)
    args.output.write_text(json.dumps(result, separators=(',', ':')) + '\n')
