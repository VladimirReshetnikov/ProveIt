"""Dry-run fold scripts: Fold.commit prints per-module line counts instead of writing.

usage: python -X utf8 dryrun.py gen_a.py [gen_b.py ...]
Each script runs on the current working tree independently. With --show MODULE, prints that
module's unified diff.
"""
import difflib
import re
import sys
import traceback

import foldlib

SHOW = sys.argv[sys.argv.index('--show') + 1] if '--show' in sys.argv else None


def dry_commit(self):
    tot = 0
    for m, s in self.text.items():
        p = foldlib.GS / f'{m}.lean'
        old = p.read_text(encoding='utf8') if p.exists() else ''
        new = re.sub(r'\n{3,}', '\n\n', s)
        d = list(difflib.unified_diff(old.split('\n'), new.split('\n'), lineterm='', n=1))
        add = sum(1 for l in d if l.startswith('+') and not l.startswith('+++'))
        rem = sum(1 for l in d if l.startswith('-') and not l.startswith('---'))
        tot += add - rem
        print(f'   {m}: +{add} -{rem}{" (new)" if not old else ""}')
        if m == SHOW:
            print('\n'.join(d))
    for w in self.deleted:
        print(f'   delete module {w}')
    print(f'   net {tot:+d} lines')


foldlib.Fold.commit = dry_commit
for script in [a for a in sys.argv[1:] if a.endswith('.py')]:
    print(f'== {script}')
    try:
        exec(compile(open(script, encoding='utf8').read(), script, 'exec'), {'__name__': '__main__'})
    except Exception:
        traceback.print_exc(limit=2)
