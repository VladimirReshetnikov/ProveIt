"""Groups of identical-statement used lemmas with no member upstream of the others: host a public copy in
the nearest common ancestor module (most ancestors of its own), plain LeanProofs.GowersSzemeredi namespace.

usage: python -X utf8 share_groups2.py USED_RANGES out.json
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
memo = {}


def anc(m):
    if m not in memo:
        s = set()
        memo[m] = s
        for d in imp.get(m, []):
            s |= {d} | anc(d)
    return memo[m]


def ns_at(m, pos):
    stack = []
    for line in src[m][:pos].split('\n'):
        a = re.match(r'namespace (\S+)', line)
        b = re.match(r'end (\S+)', line)
        if a:
            stack.append(a.group(1))
        elif b and stack and stack[-1] == b.group(1):
            stack.pop()
    return '.'.join(stack)


used = collections.defaultdict(set)
for l in open(sys.argv[1], encoding='utf8'):
    m, n, a, b = l.split()
    used[m.split('.', 1)[1]].add(n.split('.')[-1])
HEAD = re.compile(r'^((?:@\[[^\]]*\]\s*)?)(private )?(theorem|lemma) (\S+)', re.M)
decls = []
for m in mods:
    if 'Audit' in m:
        continue
    s = src[m]
    for mm in HEAD.finditer(s):
        name = mm.group(4)
        if '.' in name or name not in used.get(m, ()) or mm.group(1).strip():
            continue
        if ns_at(m, mm.start()) != 'LeanProofs.GowersSzemeredi':
            continue
        j = s.find(':=', mm.end())
        stmt = ' '.join(s[mm.end():j].split())
        end = re.compile(r'\n\n(?=\S)').search(s, j)
        lines = s[mm.start():end.start() if end else len(s)].count('\n') + 1
        if lines >= 5:
            decls.append((stmt, m, name, bool(mm.group(2)), lines))
groups = collections.defaultdict(list)
for stmt, m, name, priv, n in decls:
    groups[stmt].append((m, name, priv, n))
res = []
for stmt, members in groups.items():
    ms = sorted({m for m, *_ in members})
    if len(ms) < 2 or len(ms) != len(members):
        continue
    if any(a in anc(b) for a in ms for b in ms if a != b):
        continue  # handled by share_groups.py
    common = set.intersection(*(anc(m) for m in ms))
    common = [c for c in common if 'Audit' not in c and os.path.exists(os.path.join(OUT, c + '.olean'))]
    if not common or not all(os.path.exists(os.path.join(OUT, m + '.olean')) for m in ms):
        continue
    host = max(common, key=lambda c: len(anc(c)))
    if not re.search(r'^end LeanProofs\.GowersSzemeredi\s*$', src[host], re.M):
        continue
    name = min((n for _, n, _, _ in members), key=len)
    if any(re.search(r'^(?:private )?(?:theorem|lemma|def|abbrev) ' + re.escape(name) + r'\b', src[d], re.M)
           for d in mods if d not in ms and 'Audit' not in d):
        continue
    res.append({'host': host, 'name': name, 'members': [{'mod': m, 'name': n, 'private': p, 'lines': k}
                                                       for m, n, p, k in members],
                'saved': sum(k for *_, k in members) - max(k for *_, k in members)})
res.sort(key=lambda r: -r['saved'])
json.dump(res, open(sys.argv[2], 'w', encoding='utf8'), indent=1)
for r in res:
    print(f"{r['saved']:4} -> {r['host']}.{r['name']} <- " + ', '.join(f"{o['mod']}" for o in r['members']))
print(len(res), 'groups,', sum(r['saved'] for r in res), 'lines')
