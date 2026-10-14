"""Groups of used lemmas with identical statements (up to their own name) that can share one public copy.

usage: python -X utf8 share_groups.py USED_RANGES out.json
A group qualifies when some member module (the host) is an ancestor of every other member module, every
member module has a local olean, and making the host copy public under its own name collides with no
other declaration of that name in any module downstream of the host.
"""
import collections
import json
import os
import re
import sys

GS = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi'
OUT = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\.lake\build\lib\lean\GowersSzemeredi'
mods = [f[:-5] for f in os.listdir(GS) if f.endswith('.lean')]
src = {m: open(os.path.join(GS, m + '.lean'), encoding='utf8').read() for m in mods}
imp = {m: re.findall(r'^import GowersSzemeredi\.(\S+)', src[m], re.M) for m in mods}
rev = collections.defaultdict(set)
for m, ds in imp.items():
    for d in ds:
        rev[d].add(m)
memo = {}


def anc(m):
    if m not in memo:
        s = set()
        memo[m] = s
        for d in imp.get(m, []):
            s |= {d} | anc(d)
    return memo[m]


def desc(m):
    s, st = set(), [m]
    while st:
        x = st.pop()
        for y in rev[x]:
            if y not in s:
                s.add(y)
                st.append(y)
    return s


used = collections.defaultdict(set)
for l in open(sys.argv[1], encoding='utf8'):
    m, n, a, b = l.split()
    used[m.split('.', 1)[1]].add(n.split('.')[-1])

decls = []
HEAD = re.compile(r'^((?:@\[[^\]]*\]\s*)?)(private )?(theorem|lemma) (\S+)', re.M)
for m in mods:
    if 'Audit' in m:
        continue
    s = src[m]
    for mm in HEAD.finditer(s):
        name = mm.group(4)
        if '.' in name or name not in used.get(m, ()):
            continue
        j = s.find(':=', mm.end())
        if j < 0:
            continue
        stmt = ' '.join(s[mm.end():j].split())
        end = re.compile(r'\n\n(?=\S)').search(s, j)
        body_lines = s[mm.start():end.start() if end else len(s)].count('\n') + 1
        if body_lines < 5 or mm.group(1).strip():
            continue
        decls.append((stmt, m, name, bool(mm.group(2)), body_lines))

groups = collections.defaultdict(list)
for stmt, m, name, priv, n in decls:
    groups[stmt].append((m, name, priv, n))
res = []
for stmt, members in groups.items():
    ms = {m for m, *_ in members}
    if len(ms) < 2:
        continue
    for host, hname, hpriv, hn in members:
        others = [x for x in members if x[0] != host]
        if not all(host in anc(x[0]) for x in others):
            continue
        if not all(os.path.exists(os.path.join(OUT, x[0] + '.olean')) for x in members):
            continue
        # collisions: any module downstream of the host (or the host itself) declaring `hname`
        # other than the member copies that will be removed
        member_mods = {x[0] for x in others}
        bad = [d for d in mods
               if d not in member_mods and d != host and 'Audit' not in d
               and re.search(r'^(?:private )?(?:theorem|lemma|def|abbrev) ' + re.escape(hname) + r'\b', src[d], re.M)]
        if bad:
            continue
        res.append({'host': host, 'name': hname, 'host_private': hpriv,
                    'others': [{'mod': m, 'name': n, 'private': p, 'lines': k} for m, n, p, k in others],
                    'saved': sum(k for *_, k in others)})
        break
res.sort(key=lambda r: -r['saved'])
json.dump(res, open(sys.argv[2], 'w', encoding='utf8'), indent=1)
for r in res:
    print(f"{r['saved']:4} {r['host']}.{r['name']} <- " + ', '.join(f"{o['mod']}.{o['name']}" for o in r['others']))
print(len(res), 'groups,', sum(r['saved'] for r in res), 'lines')
