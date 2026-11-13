"""Reframe exact JSONL integer/list records as one reversed JSON array.

The first JSONL record is the goal, followed by the three-field proof
packets in consumption order. The entire list is reversed, so pop retrieves
exactly those same records. Neither proof checker imports this utility.
"""
import json
import sys


def to_whole(text):
    return list(reversed([json.loads(line) for line in text.splitlines()]))


def to_lines(certificate):
    return ''.join(json.dumps(record, separators=(',', ':')) + '\n'
                   for record in reversed(certificate))


if __name__ == '__main__':
    if '--to-lines' in sys.argv:
        sys.stdout.write(to_lines(json.load(sys.stdin)))
    else:
        json.dump(to_whole(sys.stdin.read()), sys.stdout, separators=(',', ':'))
        print()
