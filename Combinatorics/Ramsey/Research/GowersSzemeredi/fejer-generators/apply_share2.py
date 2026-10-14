"""Apply share_groups2.json for hosts that are proof modules (Proofs*): add one public copy at the end of
the host, delete every member copy, rename member uses. Prints the touched modules."""
import json
import re
import sys
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
groups = [g for g in json.load(open(sys.argv[1], encoding='utf8')) if g['host'].startswith('Proofs')]
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
    host, name = g['host'], g['name']
    first = g['members'][0]
    t = text(first['mod'])
    a, b = block(t, r'^(?:private )?(?:theorem|lemma) ' + re.escape(first['name']) + r'\b')
    copy = t[a:b]
    copy = re.sub(r'^private (theorem|lemma) ', r'\1 ', copy, flags=re.M)
    copy = re.sub(r'^((?:theorem|lemma) )' + re.escape(first['name']) + r'\b', r'\1' + name, copy, count=1, flags=re.M)
    for o in g['members']:
        t = text(o['mod'])
        a, b = block(t, r'^(?:private )?(?:theorem|lemma) ' + re.escape(o['name']) + r'\b')
        t = t[:a] + t[b:]
        if o['name'] != name:
            t = re.sub(r'(?<![\w.\'])' + re.escape(o['name']) + r'(?![\w\'])', name, t)
        cache[o['mod']] = re.sub(r'\n{3,}', '\n\n', t)
        touched.add(o['mod'])
    h = text(host)
    i = h.rindex('end LeanProofs.GowersSzemeredi')
    cache[host] = h[:i] + copy.rstrip() + '\n\n' + h[i:]
    touched.add(host)
for m in touched:
    (GS / f'{m}.lean').write_text(cache[m], encoding='utf8', newline='\n')
print(' '.join(sorted(touched)))
