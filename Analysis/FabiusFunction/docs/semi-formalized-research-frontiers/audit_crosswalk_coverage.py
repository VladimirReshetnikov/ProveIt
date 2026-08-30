# -*- coding: utf-8 -*-
"""Which volume results carry no Lean crosswalk at all?

`audit_stale_claims.py` finds results whose prose says "not formalized"
while a citation sits nearby -- a contradiction.  This finds the
opposite and larger gap: results with **no citation and no disclaimer**,
which a reader cannot tell apart from formalized ones.

A result is a `theorem`/`proposition`/`lemma`/`corollary` environment.
It counts as *covered* if a Lean citation (`\\lean`, `\\leanPart`,
`\\leanPartx`) appears inside it or in the prose immediately following
it, before the next such environment -- which is where these volumes
put their crosswalk postscripts.  It counts as *disclaimed* if that
same span says something is not formalized.  Anything else is a gap.

This is advisory: a short corollary of a covered theorem may need no
citation of its own.  The point is a worklist, not a gate.

Usage:  python audit_crosswalk_coverage.py [volume.tex ...]
        with no arguments, every .tex under drafts/.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DRAFTS = os.path.join(HERE, 'drafts')

ENV = re.compile(
    r'\\begin\{(theorem|proposition|lemma|corollary)\}'
    r'(?:\[[^\]]*\])?'
    r'\s*(?:\\label(?:\[[^\]]*\])?\{([^}]*)\})?',
    re.S)
LEAN = re.compile(r'\\lean(?:Part|Partx)?\{')
OPEN = re.compile(
    r'not formalized|unformalized|no Lean counterpart|not yet formalized'
    r'|remains open|is not proved|not proved (?:here|anywhere)',
    re.I)


def spans(text):
    """Each result, paired with the text from it to the next result."""
    marks = [(m.start(), m.group(1), m.group(2)) for m in ENV.finditer(text)]
    for k, (start, kind, label) in enumerate(marks):
        stop = marks[k + 1][0] if k + 1 < len(marks) else len(text)
        yield kind, label, text[start:stop]


def survey(path):
    text = io.open(path, encoding='utf-8', errors='replace').read()
    covered = disclaimed = gap = 0
    gaps = []
    for kind, label, span in spans(text):
        if LEAN.search(span):
            covered += 1
        elif OPEN.search(span):
            disclaimed += 1
        else:
            gap += 1
            gaps.append((kind, label or '(no label)'))
    # Total citations in the file, to separate two very different cases:
    # a volume with an INLINE crosswalk convention and gaps in it, versus
    # one that crosswalks in a dedicated section, where "0 cited" inside
    # result spans says nothing about coverage.
    total_cites = len(LEAN.findall(text))
    return covered, disclaimed, gap, gaps, total_cites


def main(argv):
    if len(argv) > 1:
        paths = argv[1:]
    else:
        paths = []
        for root, _dirs, files in os.walk(DRAFTS):
            for f in files:
                if f.endswith('.tex'):
                    paths.append(os.path.join(root, f))
        paths.sort()

    total = [0, 0, 0]
    print('== crosswalk coverage of volume results ==')
    for path in paths:
        covered, disclaimed, gap, gaps, cites = survey(path)
        if covered + disclaimed + gap == 0:
            continue
        total[0] += covered
        total[1] += disclaimed
        total[2] += gap
        rel = os.path.relpath(path, HERE)
        print()
        print('%s' % rel)
        note = ''
        if covered == 0 and cites > 0:
            note = ('   [%d citations in the file but none inside a result '
                    'span: this volume crosswalks elsewhere, so the gap '
                    'count below is not meaningful]' % cites)
        print('   cited %d   disclaimed %d   NO POINTER %d   (file cites %d)'
              % (covered, disclaimed, gap, cites))
        if note:
            print(note)
            continue
        for kind, label in gaps[:12]:
            print('      %-12s %s' % (kind, label))
        if len(gaps) > 12:
            print('      ... and %d more' % (len(gaps) - 12))

    print()
    print('TOTAL  cited %d   disclaimed %d   NO POINTER %d'
          % (total[0], total[1], total[2]))
    print()
    print('ADVISORY.  A short corollary of a covered theorem may')
    print('legitimately carry no citation of its own.  Read before acting.')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
