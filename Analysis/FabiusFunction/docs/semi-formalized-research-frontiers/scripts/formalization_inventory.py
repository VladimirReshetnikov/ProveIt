#!/usr/bin/env python3
"""Inventory every labelled result in the frontier corpus, and how much is formalized.

The goal for this corpus is that every theorem stated in a `.tex` document under
`docs/semi-formalized-research-frontiers/` has a Lean proof.  Some packages now
carry per-result `Formal crosswalk` remarks, while others use tables, CSV
registers, or package-specific prose.  This script supplies a uniform
denominator without mistaking one documentation style for proof status.

For each package it reports:

  results   labelled theorem-like environments (theorem, lemma, corollary,
            proposition, definition is excluded as it states nothing to prove)
  cited     distinct `\\lean{...}` names cited anywhere in the package, a proxy
            for how much of it has been connected to the Lean corpus
  remarks   `Formal crosswalk` remark blocks, the per-result unit of evidence

`results` counts statements, `remarks` counts results that carry an explicit
crosswalk, and `names` counts distinct Lean declarations cited.

The `names` column is the guard against the obvious misreading.  A package with
no crosswalk remarks is not thereby unformalized: the Thue-Morse atlas cites 520
distinct Lean names with no remarks at all, and the q-Pochhammer monograph 150.
Those volumes are connected to the Lean corpus, just not through this apparatus.
The remark count measures per-result traceability, not proof status.

Usage:  python formalization_inventory.py [--csv]
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
DRAFTS = os.path.join(HERE, os.pardir, 'drafts')

THEOREM_ENVS = ('theorem', 'lemma', 'corollary', 'proposition', 'conjecture')
BEGIN = re.compile(r'\\begin\{(' + '|'.join(THEOREM_ENVS) + r')\}')
LABEL = re.compile(r'\\label\{([^}]*)\}')
LEAN = re.compile(r'\\lean\{([^}]*)\}')
CROSSWALK = re.compile(r'\\begin\{remark\}\[Formal crosswalk\]')


def package_of(path, root):
    rel = os.path.relpath(path, root)
    parts = rel.split(os.sep)
    return os.sep.join(parts[:2]) if len(parts) >= 2 else parts[0]


def main(argv):
    root = os.path.abspath(DRAFTS)
    if not os.path.isdir(root):
        sys.stderr.write('no drafts directory at %s\n' % root)
        return 2
    packages = {}
    for dirpath, dirnames, files in os.walk(root):
        if 'incoming' in dirpath.split(os.sep):
            continue
        for f in files:
            if not f.endswith('.tex'):
                continue
            path = os.path.join(dirpath, f)
            try:
                text = open(path, encoding='utf-8', errors='replace').read()
            except Exception:
                continue
            pkg = package_of(path, root)
            rec = packages.setdefault(pkg, {'results': 0, 'lean': set(), 'remarks': 0, 'files': 0})
            rec['files'] += 1
            # a labelled result: a theorem-like \begin followed shortly by a \label
            for m in BEGIN.finditer(text):
                window = text[m.end():m.end() + 240]
                if LABEL.search(window):
                    rec['results'] += 1
            rec['lean'].update(LEAN.findall(text))
            rec['remarks'] += len(CROSSWALK.findall(text))

    rows = sorted(packages.items(), key=lambda kv: -kv[1]['results'])
    tot_r = sum(v['results'] for _, v in rows)
    tot_x = sum(v['remarks'] for _, v in rows)

    if '--csv' in argv:
        print('package,files,results,crosswalk_remarks,distinct_lean_names')
        for pkg, v in rows:
            print('%s,%d,%d,%d,%d' % (pkg.replace(os.sep, '/'), v['files'], v['results'],
                                      v['remarks'], len(v['lean'])))
        return 0

    print('%-58s %6s %6s %7s %7s' % ('package', 'files', 'results', 'remarks', 'names'))
    print('-' * 88)
    for pkg, v in rows:
        if v['results'] == 0 and v['remarks'] == 0:
            continue
        print('%-58s %6d %6d %7d %7d' % (pkg.replace(os.sep, '/')[:58], v['files'],
                                         v['results'], v['remarks'], len(v['lean'])))
    print('-' * 88)
    print('%-58s %6s %6d %7d' % ('TOTAL', '', tot_r, tot_x))
    pct = (100.0 * tot_x / tot_r) if tot_r else 0.0
    linked = sum(1 for _, v in rows if v['lean'])
    remarked = sum(1 for _, v in rows if v['remarks'])
    allnames = set()
    for _, v in rows:
        allnames |= v['lean']
    print()
    print('%d labelled results in %d packages.' % (tot_r, len(rows)))
    print('%d of them (%.1f%%) carry a per-result formal-crosswalk remark across %d packages.'
          % (tot_x, pct, remarked))
    print('%d packages cite Lean names at all, %d distinct names in total.'
          % (linked, len(allnames)))
    print()
    print('Read those two lines together and do not collapse them.  A package with no')
    print('crosswalk remarks is NOT thereby unformalized: several cite hundreds of Lean')
    print('names and track their status by other means.  The remark count measures')
    print('per-result traceability, which is what makes a gap plannable.  It does not')
    print('measure proof status, and this script makes no claim about that.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main(sys.argv[1:]))
