"""Regroup each proof packet, leaving the last element (the goal) unchanged."""

import argparse
import json
import sys


def group(certificate):
    if not isinstance(certificate, list) or not certificate:
        return certificate
    packets = [
        [packet[0], packet[1:]]
        if isinstance(packet, list) and packet else packet
        for packet in certificate[:-1]
    ]
    return packets + [certificate[-1]]


def flatten(certificate):
    if not isinstance(certificate, list) or not certificate:
        return certificate
    packets = [
        [packet[0], *packet[1]]
        if isinstance(packet, list) and len(packet) == 2
        and isinstance(packet[1], list) else 0
        for packet in certificate[:-1]
    ]
    return packets + [certificate[-1]]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reverse", action="store_true")
    args = parser.parse_args()
    value = json.load(sys.stdin)
    json.dump(flatten(value) if args.reverse else group(value), sys.stdout)
    print()


if __name__ == "__main__":
    main()
