#!/usr/bin/env python3
"""Query A396807 modulo 100, using the exact period proved in the article."""
from __future__ import annotations
import argparse
from series_tools import last_two_digits_at


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("index", type=int, help="positive coefficient index n")
    args = parser.parse_args()
    if args.index < 1:
        parser.error("index must be positive")
    print(f"a({args.index}) mod 100 = {last_two_digits_at(args.index):02d}")


if __name__ == "__main__":
    main()
