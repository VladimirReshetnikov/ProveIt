"""Reversible presentation changes; this program is not a trusted checker."""

import argparse
import json
import sys


def rotate_packets(document, inverse=False):
    """Rotate four-field instruction rows, retaining the final goal header.

    Old instruction: [major, source, target, template].
    New instruction: [source, target, template, major].
    The stack header is the final element and is never rotated. Nested
    terms and formulas are never traversed or changed. Unused malformed
    prefix rows are retained exactly unless they are four-element arrays;
    rotating an unused array cannot affect either checking execution.
    """
    if not isinstance(document, list):
        raise ValueError("Expected one JSON array used as a certificate stack")
    result = []
    for row in document[:-1]:
        if isinstance(row, list) and len(row) == 4:
            result.append(row[-1:] + row[:-1] if inverse else row[1:] + row[:1])
        else:
            result.append(row)
    return result + document[-1:]


def stream_to_whole(text):
    """First line is the goal; remaining lines are records in use order."""
    return [json.loads(line) for line in text.splitlines()][::-1]


def whole_to_stream(document):
    return "".join(json.dumps(row, separators=(",", ":")) + "\n"
                   for row in reversed(document))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("rotate", "unrotate", "stream-to-whole",
                                        "whole-to-stream"))
    args = parser.parse_args()
    source = sys.stdin.read()
    if args.mode == "whole-to-stream":
        sys.stdout.write(whole_to_stream(json.loads(source)))
        return
    if args.mode == "stream-to-whole":
        result = stream_to_whole(source)
    else:
        result = rotate_packets(json.loads(source), args.mode == "unrotate")
    json.dump(result, sys.stdout, separators=(",", ":"))
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
