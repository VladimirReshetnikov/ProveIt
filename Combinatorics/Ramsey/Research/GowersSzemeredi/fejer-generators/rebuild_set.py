"""Modules to force-rebuild after applying a share json: touched modules plus every module naming a
host or member.  usage: rebuild_set.py share.json "touched modules" out.txt
Prints heavy (no-olean) users with the lines that name the affected lemmas, for a manual check."""
import json
import os
import re
import sys

GS = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi'
OUT = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\.lake\build\lib\lean\GowersSzemeredi'
g = json.load(open(sys.argv[1], encoding='utf8'))
names = {r['name'] for r in g} | {o['name'] for r in g for o in r['others']}
pat = re.compile(r"(?<![\w.'])(?:" + '|'.join(map(re.escape, sorted(names, key=len, reverse=True))) + r")(?![\w'])")
users = set(sys.argv[2].split())
heavy = {}
for f in os.listdir(GS):
    if not f.endswith('.lean') or 'Audit' in f:
        continue
    s = open(os.path.join(GS, f), encoding='utf8').read()
    hits = [s[s.rfind('\n', 0, m.start()) + 1:s.find('\n', m.end())].strip() for m in pat.finditer(s)]
    if hits:
        m = f[:-5]
        if os.path.exists(os.path.join(OUT, m + '.olean')):
            users.add(m)
        else:
            heavy[m] = hits
open(sys.argv[3], 'w').write(' '.join(sorted(users)))
print(len(users), 'modules to rebuild')
for m, hs in heavy.items():
    for h in hs:
        print('HEAVY', m, '|', h[:130])
