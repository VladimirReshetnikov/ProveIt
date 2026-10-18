#!/usr/bin/env python3
"""Generate or compare the report's complete canonical transition table."""
from pathlib import Path
import argparse
import hashlib
from audit247 import parse

ROOT = Path(__file__).resolve().parents[1]


def render():
    raw = (ROOT / "machine/zfc_prefix247.tm").read_bytes()
    assert hashlib.sha256(raw).hexdigest() == "58bbbda620daf6d4d62f486db05f54d0dccb8373c080c1b5a0b26533e7a3a669"
    table, start = parse(raw)
    assert start == 0 and len(table) == 494
    out = [r"% Generated from machine/zfc_prefix247.tm by code/build_table.py.",
           r"\begingroup\small\ttfamily",
           r"\begin{longtable}{rll@{\hspace{0.45in}}rll}",
           r"\toprule",
           r"$q$ & read 0 & read 1 & $q$ & read 0 & read 1\\\midrule",
           r"\endfirsthead",
           r"\toprule",
           r"$q$ & read 0 & read 1 & $q$ & read 0 & read 1\\\midrule",
           r"\endhead",
           r"\midrule\multicolumn{6}{r}{\normalfont Continued on next page}\\",
           r"\endfoot",
           r"\bottomrule\endlastfoot"]
    def cells(q):
        if q >= 247:
            return ["", "", ""]
        def action(bit):
            w, d, target = table[q, bit]
            return f"{w} {d} {target}"
        return [str(q), action(0), action(1)]
    for q in range(124):
        out.append(" & ".join(cells(q) + cells(q+124)) + r"\\")
    out += [r"\end{longtable}", r"\endgroup", ""]
    return "\n".join(out)


def main():
    if not __debug__:
        raise SystemExit("Assertions are required; do not use -O.")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    path = ROOT / "machine/table247.tex"
    expected = render()
    if args.check:
        assert path.read_text() == expected, "Report transition table differs from frozen machine."
        print("PASS all 247 states and 494 rows in the report table")
    else:
        path.write_text(expected)
        print("Generated machine/table247.tex")


if __name__ == "__main__":
    main()
