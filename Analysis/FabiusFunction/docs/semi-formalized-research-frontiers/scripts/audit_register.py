#!/usr/bin/env python3
"""Audit the Combinatorial Coefficient Calculus register and its crosswalk queue.

Two defects motivated this script, and both had already happened.

The first is a row whose status contradicts its own prose: marked `Lean` while a
sentence beside it says some formula displayed in the theorem is not formalized.
Every Lean name in such a row can be correct and every formula right, so nothing
else catches it; the register simply overstates what has been checked.  Two rows
were in that state when this check was first run.

The second is an anchor in the pending-crosswalk queue that no longer matches the
manuscript, or matches it twice.  The crosswalk script asserts on that, which
means it fails in the middle of a PDF build after the register has already been
rewritten.  Running the check first turns a wedged build into a message.

Neither check needs Lean or LaTeX, so both are cheap enough to run before every
commit that touches the register.

Usage:  python audit_register.py
Exit status is 1 if anything is wrong.
"""
import io
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REG = os.path.join(HERE, 'combinatorial_lean_register.py')
PEN = os.path.join(HERE, 'combinatorial_crosswalk_pending.py')
TEX = os.path.join(HERE, os.pardir, 'drafts', 'combinatorial-coefficient-calculus',
                   'Combinatorial_Coefficient_Calculus',
                   'Combinatorial_Coefficient_Calculus.tex')

ROW = re.compile(r"^ '([^']+)': \('([^']+)',", re.M)
NEGATIVE = ('not formalized', 'not stated', 'not carried', 'is open', 'unformalized')

# A row may legitimately carry a negative sentence while being complete, when the
# sentence is about something the source states outside the theorem.  Each entry
# names the row and the phrase that makes the exception explicit in the prose, so
# that the exception cannot be inherited silently by a later rewrite of the row.
EXCEPTIONS = {'thm:bell-transform-inverse': 'rather than inside it'}


def rows(src):
    starts = [(m.start(), m.group(1), m.group(2)) for m in ROW.finditer(src)]
    starts.append((len(src), None, None))
    for i in range(len(starts) - 1):
        beg, lab, status = starts[i]
        body = src[beg:starts[i + 1][0]]
        text = re.sub(r'\s+', ' ', ' '.join(re.findall(r'r"([^"]*)"', body)))
        yield lab, status, text


def main():
    src = io.open(REG, encoding='utf-8').read()
    bad = 0
    counts = {}
    labels = []
    row_texts = []
    for lab, status, text in rows(src):
        counts[status] = counts.get(status, 0) + 1
        labels.append(lab)
        row_texts.append(text)
        hits = [p for p in NEGATIVE if p in text]
        if lab in EXCEPTIONS and EXCEPTIONS[lab] in text:
            hits = []
        if status == 'Lean' and hits:
            bad += 1
            print('CONTRADICTION       %-40s marked Lean but says %s' % (lab, hits))
        if status == 'partial' and not hits:
            bad += 1
            print('UNNAMED GAP         %-40s marked partial with no gap named' % lab)
        if status == 'none' and 'lean{' in text:
            bad += 1
            print('NONE CITES LEAN     %-40s marked none but cites Lean names' % lab)

    dups = sorted({l for l in labels if labels.count(l) > 1})
    if dups:
        bad += len(dups)
        print('DUPLICATE LABELS    %s (a dict literal keeps only the last)' % dups)

    tex = io.open(TEX, encoding='utf-8').read()
    pen = io.open(PEN, encoding='utf-8').read()
    anchors = re.findall(r'\n \(r"""(.*?)""",\n', pen, re.S)
    for a in anchors:
        c = tex.count(a)
        if c != 1:
            bad += 1
            print('ANCHOR OCCURS %d     %r' % (c, a[:60]))

    # Every cross-reference written into a crosswalk remark, or into a register
    # row, must have a label in the manuscript.  pdflatex only warns about a
    # dangling reference and still produces a PDF, so without this the mistake
    # surfaces at the very end, in the canonical validator, after a full build.
    labels_in_tex = set(re.findall(r'\\label\{([^}]*)\}', tex))
    refs = set()
    chunks = re.findall(r'\n  remark\(r"""(.*?)"""\)\),\n', pen, re.S) + row_texts
    for chunk in chunks:
        for group in re.findall(r'\\(?:cref|Cref|eqref|ref)\{([^}]*)\}', chunk):
            refs.update(part.strip() for part in group.split(','))
    for r in sorted(refs - labels_in_tex):
        bad += 1
        print('DANGLING REFERENCE  %s' % r)

    print()
    print('%d register rows: %s' % (len(labels),
                                    ', '.join('%d %s' % (v, k) for k, v in sorted(counts.items()))))
    print('%d queued crosswalk anchors' % len(anchors))
    print('PASS' if bad == 0 else '%d problem(s)' % bad)
    return 0 if bad == 0 else 1


if __name__ == '__main__':
    raise SystemExit(main())
