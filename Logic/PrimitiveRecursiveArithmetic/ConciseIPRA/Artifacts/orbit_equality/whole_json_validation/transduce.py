"""Convert the outer input framing; do not reverse any inner syntax tree."""
import argparse
import json
from pathlib import Path


def stream_to_array(text):
    rows = [json.loads(line) for line in text.splitlines()]
    if not rows:
        raise ValueError('A certificate must contain a goal record')
    return list(reversed(rows))


def array_to_stream(value):
    if not isinstance(value, list) or not value:
        raise ValueError('Expected a nonempty outer array')
    return ''.join(json.dumps(row, separators=(',', ':')) + '\n'
                   for row in reversed(value))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('direction', choices=('to-array', 'to-stream'))
    parser.add_argument('source', type=Path)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    text = args.source.read_text()
    if args.direction == 'to-array':
        result = json.dumps(stream_to_array(text), indent=2) + '\n'
    else:
        result = array_to_stream(json.loads(text))
    args.destination.write_text(result)


if __name__ == '__main__':
    main()
