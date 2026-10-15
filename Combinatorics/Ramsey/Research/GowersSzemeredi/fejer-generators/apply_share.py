"""Apply share_groups.json: one public host copy per group, other copies removed (or aliased if public).

usage: python -X utf8 apply_share.py share_groups.json
Prints the list of touched modules (for a forced rebuild).
"""
import json
import re
import sys
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
groups = json.load(open(sys.argv[1], encoding='utf8'))
cache = {}


def text(m):
    if m not in cache:
        cache[m] = (GS / f'{m}.lean').read_text(encoding='utf8')
    return cache[m]


def block(t, head_re):
    mm = re.search(head_re, t, re.M)
    a = mm.start()
    doc = t.rfind('/--', 0, a)
    if doc != -1 and t[t.index('-/', doc) + 2:a].strip() == '':
        a = doc
    m = re.compile(r'\n\n(?=\S)').search(t, mm.end())
    return a, (m.start() + 2) if m else len(t)


touched = set()
for g in groups:
    host, hname = g['host'], g['name']
    t = text(host)
    if g['host_private']:
        t2 = re.sub(r'^private ((?:theorem|lemma) ' + re.escape(hname) + r"(?![\w']))", r'\1', t, count=1, flags=re.M)
        assert t2 != t, (host, hname)
        cache[host] = t2
        touched.add(host)
    for o in g['others']:
        m, n = o['mod'], o['name']
        t = text(m)
        a, b = block(t, r'^(?:private )?(?:theorem|lemma) ' + re.escape(n) + r"(?![\w'])")
        if o['private'] or n == hname:
            t = t[:a] + t[b:]
            if n != hname:
                t = re.sub(r'(?<![\w.\'])' + re.escape(n) + r'(?![\w\'])', hname, t)
        else:
            t = t[:a] + f'alias {n} := {hname}\n\n' + t[b:]
        cache[m] = re.sub(r'\n{3,}', '\n\n', t)
        touched.add(m)
for m in touched:
    (GS / f'{m}.lean').write_text(cache[m], encoding='utf8', newline='\n')
print(' '.join(sorted(touched)))
