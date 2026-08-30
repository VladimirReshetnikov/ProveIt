# -*- coding: utf-8 -*-
"""Advisory audit: numbered displays that are called unformalized in one
place and cited as formalized in another.

The volumes carry two kinds of status prose about a numbered display:
a claim that it is *not* formalized, and a crosswalk naming the Lean
declarations that *do* formalize it.  Both are written by hand, in
different sections, sometimes years apart in editing time, and they
drift.  One such drift was found by reading: the weighted product
identity was crosswalked in the lobe-sign theorem and, three pages
later, declared unformalized in the generalized-Prouhet theorem, the
two being the same identity read in opposite directions.

This script finds candidates mechanically.  For each `.tex` file it
collects the `\\eqref` labels appearing near an unformalized-claim
phrase and the labels appearing near a `\\lean`-style citation, and
reports the labels in both sets.

It is ADVISORY, not a gate: a display can legitimately be half
formalized -- one direction, one special case, the combinatorial core
but not the analytic conclusion -- and then both kinds of prose are
correct.  Every hit needs reading.  Exit status is always 0.
"""
import io, os, re
from pathlib import Path

FRONTIER_ROOT = Path(__file__).resolve().parent
FABIUS_ROOT = FRONTIER_ROOT.parent.parent
DOCS = FRONTIER_ROOT
LEAN = FABIUS_ROOT / 'Lean' / 'FabiusFunction'

# Phrases in a Lean docstring that go stale silently.  "not proved
# here" stays literally true forever -- "here" means this module -- so
# it never trips a check, while a reader scanning the corpus concludes
# the result is unformalized.  Four such claims were found stale by
# hand in one sweep; this lists them all so the sweep is repeatable.
LEAN_CLAIM = re.compile(
    r'not formalized|is not formal|unformalized|not proved here|'
    r'remains open|is still open|left open|not available here|'
    r'no declaration of this file|not established here|is deferred',
    re.IGNORECASE)

# How far from the phrase a label still counts as "in the same claim".
WINDOW = 320


def ascii_only(s):
    """The Windows console is cp1252; Lean docstrings are not."""
    return s.encode('ascii', 'replace').decode('ascii')

CLAIM = re.compile(
    r'not\s+formalized|is\s+not\s+formal\b|unformalized|'
    r'no\s+Lean\s+counterpart|not\s+yet\s+formal|'
    r'has\s+no\s+Lean\b|lacks?\s+a\s+Lean\b',
    re.IGNORECASE)
LEANCITE = re.compile(r'\\lean(?:Partx|Part)?\{')
EQREF = re.compile(r'\\(?:eq)?ref\{([^}]+)\}')


def labels_near(text, matcher):
    """Labels cited within WINDOW characters of a match of `matcher`."""
    out = {}
    for m in matcher.finditer(text):
        lo = max(0, m.start() - WINDOW)
        hi = min(len(text), m.end() + WINDOW)
        line = text.count('\n', 0, m.start()) + 1
        for e in EQREF.finditer(text[lo:hi]):
            out.setdefault(e.group(1), set()).add(line)
    return out


total_hits = 0
files = 0
for root, _dirs, names in os.walk(DOCS):
    for fn in sorted(names):
        if not fn.endswith('.tex'):
            continue
        path = os.path.join(root, fn)
        text = io.open(path, encoding='utf-8', errors='replace').read()
        claimed = labels_near(text, CLAIM)
        cited = labels_near(text, LEANCITE)
        both = sorted(set(claimed) & set(cited))
        if not both:
            continue
        files += 1
        rel = os.path.relpath(path, DOCS)
        print('== %s' % rel)
        for lab in both:
            cl = sorted(claimed[lab])[:4]
            ci = sorted(cited[lab])[:4]
            print('   %-42s unformalized near lines %s ; '
                  'crosswalked near lines %s'
                  % (lab, cl, ci))
            total_hits += 1
        print()

print('files with candidates: %d' % files)
print('label candidates:      %d' % total_hits)
print()

# ---- Lean side: every open-claim sentence in a module docstring ----
print('=' * 62)
print('LEAN DOCSTRING OPEN CLAIMS')
print()
print('Each of these says something is not proved.  Check that it is')
print('still true, and that it carries a POINTER to whatever module')
print('does prove it -- "not proved here" is true of its own module')
print('forever, and misleads a reader scanning the corpus.')
print()

lean_hits = 0
for fn in sorted(os.listdir(LEAN)):
    if not fn.endswith('.lean'):
        continue
    text = io.open(os.path.join(LEAN, fn), encoding='utf-8',
                   errors='replace').read()
    lines = text.split('\n')
    for i, line in enumerate(lines, 1):
        if not LEAN_CLAIM.search(line):
            continue
        # A pointer names another module or declaration near the claim.
        lo = max(0, i - 4)
        window = '\n'.join(lines[lo:i + 4])
        pointed = ('FabiusFunction.' in window or '.lean' in window or
                   re.search(r'`Fabius\.\w', window) is not None)
        lean_hits += 1
        print('  %-38s :%-5d %s' % (fn, i, 'points elsewhere' if pointed
                                    else 'open, no pointer'))
        print('      %s' % ascii_only(line.strip()[:96]))

print()
print('lean open claims: %d' % lean_hits)
print()
print('ADVISORY ONLY.  A display may be half formalized, in which case')
print('both kinds of prose are correct.  Read each hit before acting.')
