# -*- coding: utf-8 -*-
"""Report overfull boxes in a LaTeX log, above a dimension threshold.

This exists because the shell idiom it replaces is silently wrong.

    grep -o "Overfull \\\\hbox ([0-9.]*pt" LOG | sed 's/[^0-9.]//g' \\
      | awk '$1>20' | wc -l

reports 0 on a log with four such boxes; the same pipeline with '.' in place
of the escaped backslash reports 4.  Every "no overfull box above 20pt" line
in the 2026-08-29 commits came from the first form and was therefore
unverified -- true for one volume by luck, wrong for another, which has four
pre-existing ones.

Usage:  python audit_overfull.py <file.log> [threshold_pt]

Exits 1 if any box exceeds the threshold, so it can gate a build; the caller
decides whether pre-existing boxes in verbatim, tabular, or quoted material
are acceptable.
"""
import io
import re
import sys

# The log writes a literal backslash before hbox or vbox; matching it with a
# character class sidesteps every layer of shell and regex escaping.  An
# output-routine vbox normally has no source-line range, so that suffix stays
# optional for both kinds.
ENTRY = re.compile(
    r'Overfull [\\]?([hv])box \(([0-9.]+)pt too (wide|high)\)'
    r'(?:(?: in paragraph at lines ([0-9]+)--([0-9]+))|'
    r'(?: detected at line ([0-9]+)))?')


def main(argv):
    if len(argv) < 2:
        print(__doc__)
        return 2
    path = argv[1]
    threshold = float(argv[2]) if len(argv) > 2 else 20.0
    text = io.open(path, encoding='utf-8', errors='replace').read()
    entries = ENTRY.findall(text)
    big = [entry for entry in entries if float(entry[1]) > threshold]

    print('== overfull boxes ==')
    print('log:            %s' % path)
    print('entries total:  %d' % len(entries))
    print('over %-6.1fpt:  %d' % (threshold, len(big)))
    for kind, amount, direction, lo, hi, line in big:
        if lo:
            where = 'lines %s--%s' % (lo, hi)
        elif line:
            where = 'line %s' % line
        else:
            where = '(no line range)'
        print('   %9.2fpt  %sbox too %s  %s' %
              (float(amount), kind, direction, where))

    # Self-check: the matcher must find something in a log that has the phrase
    # at all.  A silent zero is the failure mode this replaces.
    if not entries and 'Overfull' in text:
        print()
        print('CHECKER FAILURE: the log contains "Overfull" but the')
        print('pattern matched nothing.  Fix the pattern, not the log.')
        return 2
    return 1 if big else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
